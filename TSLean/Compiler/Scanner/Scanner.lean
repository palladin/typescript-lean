/-
  TSLean.Compiler.Scanner.Scanner — Main scanner implementation.

  Based on Go: internal/scanner/scanner.go
  Translates Go's mutable Scanner struct to Lean 4's functional style.
  All methods take and return Scanner (FBIP optimizes in-place when refcount = 1).
-/
import TSLean.Compiler.Core
import TSLean.Compiler.Ast
import TSLean.Compiler.Scanner.Unicode
import TSLean.Compiler.Scanner.Keywords

namespace TSLean.Compiler

/-- Scanner diagnostic (error message with position).
    Replaces Go's ErrorCallback (scanner.go:33). -/
structure ScannerDiagnostic where
  message : String
  start : Nat
  length : Nat
  deriving Repr

/-- Based on Go: internal/scanner/scanner.go:200-209 (ScannerState) -/
structure ScannerState where
  pos : Nat := 0               -- Go: scanner.go:201
  fullStartPos : Nat := 0      -- Go: scanner.go:202
  tokenStart : Nat := 0        -- Go: scanner.go:203
  token : Kind := Kind.unknown  -- Go: scanner.go:204
  tokenValue : String := ""    -- Go: scanner.go:205
  tokenFlags : TokenFlags := TokenFlags.none  -- Go: scanner.go:206
  commentDirectives : Array CommentDirective := #[]  -- Go: scanner.go:207
  deriving Repr

/-- Based on Go: internal/scanner/scanner.go:211-223 (Scanner) -/
structure Scanner where
  text : String := ""                                    -- Go: scanner.go:212
  bytes : ByteArray := ByteArray.empty                   -- UTF-8 bytes of text (for fast byte access)
  languageVariant : LanguageVariant := LanguageVariant.standard  -- Go: scanner.go:213
  skipTrivia : Bool := true                              -- Go: scanner.go:215
  jsDocParsingMode : JSDocParsingMode := JSDocParsingMode.parseAll  -- Go: scanner.go:216
  scriptKind : ScriptKind := ScriptKind.unknown          -- Go: scanner.go:217
  state : ScannerState := {}                             -- Go: scanner.go:218
  diagnostics : Array ScannerDiagnostic := #[]

namespace Scanner

-- ============================================================
-- Internal helpers
-- ============================================================

/-- Get byte at position, or sentinel for EOF.
    Based on Go: scanner.go:382-387 (char) -/
@[inline] private def ch (s : Scanner) : UInt32 :=
  if s.state.pos < s.bytes.size then s.bytes[s.state.pos]!.toUInt32
  else 0xFFFFFFFF

/-- Get byte at pos + offset.
    Based on Go: scanner.go:390-395 (charAt) -/
@[inline] private def chAt (s : Scanner) (offset : Nat) : UInt32 :=
  let p := s.state.pos + offset
  if p < s.bytes.size then s.bytes[p]!.toUInt32
  else 0xFFFFFFFF

/-- Decode a full UTF-8 rune at position, returning (codepoint, byteSize).
    Returns (0xFFFFFFFF, 0) for EOF.
    Based on Go: scanner.go:397-399 (charAndSize) -/
private def runeAt (s : Scanner) : UInt32 × Nat :=
  let pos := s.state.pos
  if pos >= s.bytes.size then (0xFFFFFFFF, 0)
  else
    let b0 := s.bytes[pos]!.toUInt32
    if b0 < 0x80 then (b0, 1)  -- ASCII
    else if b0 < 0xC0 then (0xFFFD, 1)  -- invalid continuation byte
    else if b0 < 0xE0 then
      if pos + 1 < s.bytes.size then
        let b1 := s.bytes[pos + 1]!.toUInt32
        ((b0 &&& 0x1F) <<< 6 ||| (b1 &&& 0x3F), 2)
      else (0xFFFD, 1)
    else if b0 < 0xF0 then
      if pos + 2 < s.bytes.size then
        let b1 := s.bytes[pos + 1]!.toUInt32
        let b2 := s.bytes[pos + 2]!.toUInt32
        ((b0 &&& 0x0F) <<< 12 ||| (b1 &&& 0x3F) <<< 6 ||| (b2 &&& 0x3F), 3)
      else (0xFFFD, 1)
    else
      if pos + 3 < s.bytes.size then
        let b1 := s.bytes[pos + 1]!.toUInt32
        let b2 := s.bytes[pos + 2]!.toUInt32
        let b3 := s.bytes[pos + 3]!.toUInt32
        ((b0 &&& 0x07) <<< 18 ||| (b1 &&& 0x3F) <<< 12 ||| (b2 &&& 0x3F) <<< 6 ||| (b3 &&& 0x3F), 4)
      else (0xFFFD, 1)

@[inline] private def isWsSingle (c : UInt32) : Bool :=
  c == 0x09 || c == 0x0B || c == 0x0C || c == 0x20 || c == 0xA0 || c == 0xFEFF

@[inline] private def isLB (c : UInt32) : Bool :=
  c == 0x0A || c == 0x0D || c == 0x2028 || c == 0x2029

@[inline] private def isDig (c : UInt32) : Bool := c >= 0x30 && c <= 0x39
@[inline] private def isAsciiLet (c : UInt32) : Bool := (c >= 0x41 && c <= 0x5A) || (c >= 0x61 && c <= 0x7A)
@[inline] private def isWord (c : UInt32) : Bool := isAsciiLet c || isDig c || c == 0x5F

@[inline] private def adv (s : Scanner) (n : Nat) : Scanner :=
  { s with state := { s.state with pos := s.state.pos + n } }

@[inline] private def setTok (s : Scanner) (k : Kind) : Scanner :=
  { s with state := { s.state with token := k } }

@[inline] private def setVal (s : Scanner) (v : String) : Scanner :=
  { s with state := { s.state with tokenValue := v } }

@[inline] private def addFlg (s : Scanner) (f : TokenFlags) : Scanner :=
  { s with state := { s.state with tokenFlags := s.state.tokenFlags ||| f } }

private def err (s : Scanner) (msg : String) : Scanner :=
  { s with diagnostics := s.diagnostics.push { message := msg, start := s.state.pos, length := 0 } }

private def extract (s : Scanner) (startByte endByte : Nat) : String :=
  String.fromUTF8! (s.bytes.extract startByte endByte)

/-- Skip contiguous single-line whitespace. -/
private partial def skipWs (s : Scanner) : Scanner :=
  if isWsSingle (ch s) then skipWs (adv s 1) else s

/-- Scan hex digits [0-9A-Fa-f_]. -/
private partial def scanHexDigits (s : Scanner) : Scanner :=
  let c := ch s
  if isDig c || (c >= 0x41 && c <= 0x46) || (c >= 0x61 && c <= 0x66) || c == 0x5F
  then scanHexDigits (adv s 1) else s

/-- Scan binary digits [01_]. -/
private partial def scanBinDigits (s : Scanner) : Scanner :=
  let c := ch s
  if c == 0x30 || c == 0x31 || c == 0x5F then scanBinDigits (adv s 1) else s

/-- Scan octal digits [0-7_]. -/
private partial def scanOctDigits (s : Scanner) : Scanner :=
  let c := ch s
  if (c >= 0x30 && c <= 0x37) || c == 0x5F then scanOctDigits (adv s 1) else s

-- ============================================================
-- Character classification helpers for escape sequences
-- ============================================================

@[inline] private def isHexDigit (c : UInt32) : Bool :=
  isDig c || (c >= 0x41 && c <= 0x46) || (c >= 0x61 && c <= 0x66)

@[inline] private def isOctalDigit (c : UInt32) : Bool :=
  c >= 0x30 && c <= 0x37

/-- Convert a hex digit character to its numeric value. -/
@[inline] private def hexVal (c : UInt32) : UInt32 :=
  if c >= 0x30 && c <= 0x39 then c - 0x30
  else if c >= 0x41 && c <= 0x46 then c - 0x41 + 10
  else if c >= 0x61 && c <= 0x66 then c - 0x61 + 10
  else 0

/-- Scan a unicode escape sequence. Assumes position is at `\u`.
    Returns (scanner, codePoint) where codePoint = 0xFFFFFFFF on failure.
    Based on Go: scanner.go:1676-1715 (scanUnicodeEscape) -/
private partial def scanUnicodeEscape (s : Scanner) (reportErrors : Bool) : Scanner × UInt32 :=
  let s := adv s 2  -- skip \u
  if ch s == 0x7B then  -- extended: \u{HHHHH}
    let s := adv s 1
    let s := addFlg s TokenFlags.extendedUnicodeEscape
    let rec scanExtHex (s : Scanner) (value : UInt32) (count : Nat) : Scanner × UInt32 :=
      let c := ch s
      if isHexDigit c then scanExtHex (adv s 1) (value * 16 + hexVal c) (count + 1)
      else (s, if count == 0 then 0xFFFFFFFF else value)
    let (s, value) := scanExtHex s 0 0
    if value == 0xFFFFFFFF then
      let s := addFlg s TokenFlags.containsInvalidEscape
      let s := if reportErrors then err s "Hexadecimal digit expected" else s
      (s, 0xFFFFFFFF)
    else if value > 0x10FFFF then
      let s := addFlg s TokenFlags.containsInvalidEscape
      let s := if reportErrors then err s "An extended Unicode escape value must be between 0x0 and 0x10FFFF inclusive" else s
      (s, 0xFFFFFFFF)
    else if ch s != 0x7D then  -- missing closing }
      let s := addFlg s TokenFlags.containsInvalidEscape
      let s := if reportErrors then err s "Unterminated Unicode escape sequence" else s
      (s, 0xFFFFFFFF)
    else
      (adv s 1, value)  -- skip }
  else  -- fixed: \uHHHH
    let s := addFlg s TokenFlags.unicodeEscape
    let rec scan4Hex (s : Scanner) (value : UInt32) (remaining : Nat) : Scanner × UInt32 :=
      match remaining with
      | 0 => (s, value)
      | n + 1 =>
        let c := ch s
        if isHexDigit c then scan4Hex (adv s 1) (value * 16 + hexVal c) n
        else
          let s := addFlg s TokenFlags.containsInvalidEscape
          let s := if reportErrors then err s "Hexadecimal digit expected" else s
          (s, 0xFFFFFFFF)
    scan4Hex s 0 4

/-- Peek at a unicode escape without consuming it.
    Based on Go: scanner.go:1719-1729 (peekUnicodeEscape) -/
private def peekUnicodeEscape (s : Scanner) : Scanner × UInt32 :=
  if chAt s 1 == 0x75 then  -- 'u'
    let savedPos := s.state.pos
    let savedFlags := s.state.tokenFlags
    let (s, cp) := scanUnicodeEscape s false
    let s := { s with state := { s.state with pos := savedPos, tokenFlags := savedFlags } }
    (s, cp)
  else
    (s, 0xFFFFFFFF)

/-- Scan an escape sequence after the backslash. Returns (scanner, escapedString).
    Based on Go: scanner.go:1557-1673 (scanEscapeSequence) -/
private partial def scanEscapeSequence (s : Scanner) : Scanner × String :=
  let start := s.state.pos
  let s := adv s 1  -- skip backslash
  let c := ch s
  if c == 0xFFFFFFFF then (err s "Unexpected end of text", "")
  else
    let s := adv s 1  -- skip the escape character
    match c with
    | 0x30 =>  -- '0'
      if !isDig (ch s) then (s, "\x00")
      else  -- legacy octal \0N, \0NN
        let s := if isOctalDigit (ch s) then adv s 1 else s
        let s := if isOctalDigit (ch s) then adv s 1 else s
        let s := addFlg s TokenFlags.containsInvalidEscape
        (s, extract s (start + 1) s.state.pos)
    | 0x31 | 0x32 | 0x33 =>  -- '1'-'3': octal with up to 2 more digits
      let s := if isOctalDigit (ch s) then adv s 1 else s
      let s := if isOctalDigit (ch s) then adv s 1 else s
      let s := addFlg s TokenFlags.containsInvalidEscape
      (s, extract s (start + 1) s.state.pos)
    | 0x34 | 0x35 | 0x36 | 0x37 =>  -- '4'-'7': octal with up to 1 more digit
      let s := if isOctalDigit (ch s) then adv s 1 else s
      let s := addFlg s TokenFlags.containsInvalidEscape
      (s, extract s (start + 1) s.state.pos)
    | 0x38 | 0x39 =>  -- '8', '9': invalid escape
      let s := addFlg s TokenFlags.containsInvalidEscape
      (s, String.singleton (Char.ofNat c.toNat))
    | 0x62 => (s, "\x08")  -- \b backspace
    | 0x74 => (s, "\t")    -- \t tab
    | 0x6E => (s, "\n")    -- \n newline
    | 0x76 => (s, "\x0B")  -- \v vertical tab
    | 0x66 => (s, "\x0C")  -- \f form feed
    | 0x72 => (s, "\r")    -- \r carriage return
    | 0x27 => (s, "'")     -- \'
    | 0x22 => (s, "\"")    -- \"
    | 0x75 =>  -- \u: unicode escape
      let s := { s with state := { s.state with pos := start } }  -- back to backslash
      let (s, cp) := scanUnicodeEscape s true
      if cp == 0xFFFFFFFF then (s, extract s start s.state.pos)
      else (s, String.singleton (Char.ofNat cp.toNat))
    | 0x78 =>  -- \x: hex escape
      let c1 := ch s
      let c2 := chAt s 1
      if isHexDigit c1 && isHexDigit c2 then
        let s := adv s 2
        let s := addFlg s TokenFlags.hexEscape
        let value := hexVal c1 * 16 + hexVal c2
        (s, String.singleton (Char.ofNat value.toNat))
      else
        let s := addFlg s TokenFlags.containsInvalidEscape
        (err s "Hexadecimal digit expected", extract s start s.state.pos)
    | 0x0D =>  -- \r: line continuation
      let s := if ch s == 0x0A then adv s 1 else s  -- skip \n after \r
      (s, "")
    | 0x0A => (s, "")  -- \n: line continuation
    | _ => (s, String.singleton (Char.ofNat c.toNat))  -- default: literal char

-- ============================================================
-- Construction and Setup
-- ============================================================

/-- Based on Go: scanner.go:232-235 (NewScanner) -/
def new : Scanner := { skipTrivia := true }

/-- Based on Go: scanner.go:348-351 (SetText) -/
def setText (s : Scanner) (text : String) : Scanner :=
  { s with text := text, bytes := text.toUTF8, state := {} }

def setLanguageVariant (s : Scanner) (lv : LanguageVariant) : Scanner :=
  { s with languageVariant := lv }

def setScriptKind (s : Scanner) (sk : ScriptKind) : Scanner :=
  { s with scriptKind := sk }

-- ============================================================
-- Accessors (Go: scanner.go:256-290)
-- ============================================================

def token (s : Scanner) : Kind := s.state.token
def tokenFlags' (s : Scanner) : TokenFlags := s.state.tokenFlags
def tokenFullStart (s : Scanner) : Nat := s.state.fullStartPos
def tokenStart (s : Scanner) : Nat := s.state.tokenStart
def tokenEnd (s : Scanner) : Nat := s.state.pos
def tokenValue (s : Scanner) : String := s.state.tokenValue

/-- Based on Go: scanner.go:292-298 (Mark/Rewind) -/
def mark (s : Scanner) : ScannerState := s.state
def rewind (s : Scanner) (st : ScannerState) : Scanner := { s with state := st }

def hasPrecedingLineBreak (s : Scanner) : Bool :=
  TokenFlags.has s.state.tokenFlags TokenFlags.precedingLineBreak

-- ============================================================
-- String scanning (Go: scanner.go:1457)
-- ============================================================

private partial def scanStr (s : Scanner) (jsxAttributeString : Bool := false) : Scanner × String :=
  let quote := ch s
  let s := if quote == 0x27 then addFlg s TokenFlags.singleQuote else s
  let s := adv s 1
  let rec go (s : Scanner) (acc : String) : Scanner × String :=
    let c := ch s
    if c == 0xFFFFFFFF then (addFlg (err s "Unterminated string literal") TokenFlags.unterminated, acc)
    else
      if c == quote then (adv s 1, acc)
      else
        if c == 0x5C && !jsxAttributeString then
          let (s, escaped) := scanEscapeSequence s
          go s (acc ++ escaped)
        else
          if (c == 0x0A || c == 0x0D) && !jsxAttributeString then
            (addFlg (err s "Unterminated string literal") TokenFlags.unterminated, acc)
          else go (adv s 1) (acc.push (Char.ofNat c.toNat))
  go s ""

-- ============================================================
-- Number scanning (Go: scanner.go:1731)
-- ============================================================

private partial def scanNum (s : Scanner) : Scanner × Kind :=
  let start := s.state.pos
  let rec digits (s : Scanner) : Scanner :=
    let c := ch s; if isDig c || c == 0x5F then digits (adv s 1) else s
  let s := digits s
  let s := if ch s == 0x2E then digits (adv s 1) else s  -- '.'
  let c := ch s
  let s := if c == 0x65 || c == 0x45 then  -- 'e'/'E'
    let s := addFlg (adv s 1) TokenFlags.scientific
    let s := let c2 := ch s; if c2 == 0x2B || c2 == 0x2D then adv s 1 else s
    digits s
  else s
  let c := ch s
  let (s, k) := if c == 0x6E then (adv s 1, Kind.bigIntLiteral) else (s, Kind.numericLiteral)
  (setVal s (extract s start s.state.pos), k)

-- ============================================================
-- Identifier scanning (Go: scanner.go:1396)
-- ============================================================

private partial def scanIdentParts (s : Scanner) : Scanner :=
  let c := ch s
  if isWord c || c == 0x24 then scanIdentParts (adv s 1)
  else
    let (cp, size) := runeAt s
    if size > 1 && isIdentifierPart (Char.ofNat cp.toNat) then scanIdentParts (adv s size)
    else s

private partial def scanIdent (s : Scanner) (prefixLen : Nat) : Scanner × Bool :=
  let start := s.state.pos
  let s := adv s prefixLen
  let c := ch s
  -- Fast ASCII path
  if isAsciiLet c || c == 0x5F || c == 0x24 then
    let s := scanIdentParts (adv s 1)
    (setVal s (extract s start s.state.pos), true)
  else
    -- Slow path: check for Unicode identifier start
    let (cp, size) := runeAt s
    if size > 1 && isIdentifierStart (Char.ofNat cp.toNat) then
      let s := scanIdentParts (adv s size)
      (setVal s (extract s start s.state.pos), true)
    else
      ({ s with state := { s.state with pos := start + prefixLen } }, false)

-- ============================================================
-- Template scanning (Go: scanner.go:1508)
-- ============================================================

private partial def scanTmpl (s : Scanner) (startedWithBacktick : Bool) : Scanner :=
  let s := adv s 1
  let rec go (s : Scanner) (acc : String) : Scanner × String × Kind :=
    let c := ch s
    if c == 0xFFFFFFFF then
      let endKind := if startedWithBacktick then Kind.noSubstitutionTemplateLiteral else Kind.templateTail
      (addFlg (err s "Unterminated template") TokenFlags.unterminated, acc, endKind)
    else
      if c == 0x60 then
        let endKind := if startedWithBacktick then Kind.noSubstitutionTemplateLiteral else Kind.templateTail
        (adv s 1, acc, endKind)
      else
        if c == 0x24 && chAt s 1 == 0x7B then
          let midKind := if startedWithBacktick then Kind.templateHead else Kind.templateMiddle
          (adv s 2, acc, midKind)
        else
          if c == 0x5C then
            let (s, escaped) := scanEscapeSequence s
            go s (acc ++ escaped)
          else
            -- CR/CRLF normalization per ECMAScript spec 11.8.6.1
            if c == 0x0D then
              let s := adv s 1
              let s := if ch s == 0x0A then adv s 1 else s
              go s (acc.push '\n')
            else go (adv s 1) (acc.push (Char.ofNat c.toNat))
  let (s, v, k) := go s ""
  setTok (setVal s v) k

-- ============================================================
-- Comment scanning
-- ============================================================

private partial def scanSLComment (s : Scanner) : Scanner :=
  let s := adv s 2
  let rec go (s : Scanner) : Scanner :=
    let c := ch s; if c == 0xFFFFFFFF || isLB c then s else go (adv s 1)
  go s

private partial def scanMLComment (s : Scanner) : Scanner × Bool :=
  let s := adv s 2
  let isJSDoc := ch s == 0x2A && chAt s 1 != 0x2F
  let rec go (s : Scanner) : Scanner × Bool :=
    let c := ch s
    if c == 0xFFFFFFFF then (s, false)
    else
      if c == 0x2A && chAt s 1 == 0x2F then (adv s 2, true)
      else go (if isLB c then addFlg (adv s 1) TokenFlags.precedingLineBreak else adv s 1)
  let (s, closed) := go s
  let s := if isJSDoc then addFlg s TokenFlags.precedingJSDocComment else s
  let s := if !closed then addFlg (err s "Expected '*/'") TokenFlags.unterminated else s
  (s, closed)

-- ============================================================
-- Non-ASCII whitespace detection (Go: stringutil.IsWhiteSpaceSingleLine)
-- ============================================================

/-- Check if a rune is a non-ASCII whitespace character.
    Matches Go's stringutil.IsWhiteSpaceSingleLine for codepoints > 0x7F.
    ASCII whitespace (0x09, 0x0B, 0x0C, 0x20) is handled by explicit match arms. -/
@[inline] def isNonAsciiWhiteSpace (c : UInt32) : Bool :=
  c == 0x00A0 ||  -- nonBreakingSpace
  c == 0x0085 ||  -- nextLine
  c == 0x1680 ||  -- ogham
  (c >= 0x2000 && c <= 0x200B) ||  -- enQuad..zeroWidthSpace
  c == 0x202F ||  -- narrowNoBreakSpace
  c == 0x205F ||  -- mathematicalSpace
  c == 0x3000 ||  -- ideographicSpace
  c == 0xFEFF     -- byteOrderMark

-- ============================================================
-- Main scan (Go: scanner.go:431-917)
-- ============================================================

partial def scan (s : Scanner) : Scanner :=
  let s := { s with state := { s.state with fullStartPos := s.state.pos, tokenFlags := TokenFlags.none } }
  let rec go (s : Scanner) : Scanner :=
    let s := { s with state := { s.state with tokenStart := s.state.pos } }
    let c := ch s
    match c with
    -- Whitespace (Go: 439)
    | 0x09 | 0x0B | 0x0C | 0x20 =>
      let s := adv s 1
      if s.skipTrivia then go s
      else setTok (skipWs s) Kind.whitespaceTrivia
    -- Newline (Go: 452)
    | 0x0A | 0x0D =>
      let s := addFlg s TokenFlags.precedingLineBreak
      let s := if c == 0x0D && chAt s 1 == 0x0A then adv s 2 else adv s 1
      if s.skipTrivia then go s else setTok s Kind.newLineTrivia
      -- '!' (Go: 464)
      | 0x21 =>
        match chAt s 1 with
        | 0x3D =>
          match chAt s 2 with
          | 0x3D => setTok (adv s 3) Kind.exclamationEqualsEqualsToken   -- !==
          | _    => setTok (adv s 2) Kind.exclamationEqualsToken          -- !=
        | _ => setTok (adv s 1) Kind.exclamationToken                     -- !
      -- '"' '\'' (Go: 477)
      | 0x22 | 0x27 =>
        let (s, v) := scanStr s; setTok (setVal s v) Kind.stringLiteral
      -- '%' (Go: 482)
      | 0x25 =>
        match chAt s 1 with
        | 0x3D => setTok (adv s 2) Kind.percentEqualsToken               -- %=
        | _    => setTok (adv s 1) Kind.percentToken                      -- %
      -- '&' (Go: 490)
      | 0x26 =>
        match chAt s 1 with
        | 0x26 =>
          match chAt s 2 with
          | 0x3D => setTok (adv s 3) Kind.ampersandAmpersandEqualsToken  -- &&=
          | _    => setTok (adv s 2) Kind.ampersandAmpersandToken         -- &&
        | 0x3D => setTok (adv s 2) Kind.ampersandEqualsToken             -- &=
        | _    => setTok (adv s 1) Kind.ampersandToken                    -- &
      -- '(' (Go: 506)
      | 0x28 => setTok (adv s 1) Kind.openParenToken
      -- ')' (Go: 509)
      | 0x29 => setTok (adv s 1) Kind.closeParenToken
      -- '*' (Go: 512)
      | 0x2A =>
        match chAt s 1 with
        | 0x3D => setTok (adv s 2) Kind.asteriskEqualsToken              -- *=
        | 0x2A =>
          match chAt s 2 with
          | 0x3D => setTok (adv s 3) Kind.asteriskAsteriskEqualsToken    -- **=
          | _    => setTok (adv s 2) Kind.asteriskAsteriskToken           -- **
        | _ => setTok (adv s 1) Kind.asteriskToken                        -- *
      -- '+' (Go: 534)
      | 0x2B =>
        match chAt s 1 with
        | 0x3D => setTok (adv s 2) Kind.plusEqualsToken                   -- +=
        | 0x2B => setTok (adv s 2) Kind.plusPlusToken                     -- ++
        | _    => setTok (adv s 1) Kind.plusToken                          -- +
      -- ',' (Go: 545)
      | 0x2C => setTok (adv s 1) Kind.commaToken
      -- '-' (Go: 548)
      | 0x2D =>
        match chAt s 1 with
        | 0x3D => setTok (adv s 2) Kind.minusEqualsToken                 -- -=
        | 0x2D => setTok (adv s 2) Kind.minusMinusToken                  -- --
        | _    => setTok (adv s 1) Kind.minusToken                        -- -
      -- '.' (Go: 559)
      | 0x2E =>
        if isDig (chAt s 1) then let (s, k) := scanNum s; setTok s k
        else
          if chAt s 1 == 0x2E && chAt s 2 == 0x2E then setTok (adv s 3) Kind.dotDotDotToken
          else setTok (adv s 1) Kind.dotToken
      -- '/' (Go: 569)
      | 0x2F =>
        match chAt s 1 with
        | 0x2F =>  -- //
          let s := scanSLComment s
          if s.skipTrivia then go s else setTok s Kind.singleLineCommentTrivia
        | 0x2A =>  -- /*
          let (s, _) := scanMLComment s
          if s.skipTrivia then go s else setTok s Kind.multiLineCommentTrivia
        | 0x3D => setTok (adv s 2) Kind.slashEqualsToken                 -- /=
        | _    => setTok (adv s 1) Kind.slashToken                        -- /
      -- '0' prefix (Go: 644)
      | 0x30 =>
        let nx := chAt s 1
        match nx with
        | 0x58 | 0x78 =>  -- 'X' 'x' hex
          let s := addFlg (adv s 2) TokenFlags.hexSpecifier
          let start := s.state.pos - 2
          let s := scanHexDigits s
          let s := setVal s (extract s start s.state.pos)
          if ch s == 0x6E then setTok (adv s 1) Kind.bigIntLiteral else setTok s Kind.numericLiteral
        | 0x42 | 0x62 =>  -- 'B' 'b' binary
          let s := addFlg (adv s 2) TokenFlags.binarySpecifier
          let start := s.state.pos - 2
          let s := scanBinDigits s
          let s := setVal s (extract s start s.state.pos)
          if ch s == 0x6E then setTok (adv s 1) Kind.bigIntLiteral else setTok s Kind.numericLiteral
        | 0x4F | 0x6F =>  -- 'O' 'o' octal
          let s := addFlg (adv s 2) TokenFlags.octalSpecifier
          let start := s.state.pos - 2
          let s := scanOctDigits s
          let s := setVal s (extract s start s.state.pos)
          if ch s == 0x6E then setTok (adv s 1) Kind.bigIntLiteral else setTok s Kind.numericLiteral
        | _ =>
          -- Check for legacy octal (0 followed by digits) or leading-zero decimal
          let nx2 := chAt s 1
          if isDig nx2 then
            -- 0 followed by digits — scan all digits, detect octal vs decimal
            let start := s.state.pos
            let s := adv s 1  -- skip the '0'
            let rec scanDigitsOctal (s : Scanner) (allOctal : Bool) : Scanner × Bool :=
              let c := ch s
              if isDig c then scanDigitsOctal (adv s 1) (allOctal && c <= 0x37)
              else (s, allOctal)
            let (s, allOctal) := scanDigitsOctal s true
            if allOctal then
              -- Legacy octal: emit error
              let s := addFlg s TokenFlags.octal
              let s := err s "Octal literals are not allowed. Use the syntax '0o...'"
              setTok (setVal s (extract s start s.state.pos)) Kind.numericLiteral
            else
              -- Decimal with leading zero: emit error then continue with decimals/exponent
              let s := addFlg s TokenFlags.containsLeadingZero
              let s := if ch s == 0x2E then
                let rec scanFrac (s : Scanner) : Scanner :=
                  let c := ch s; if isDig c then scanFrac (adv s 1) else s
                scanFrac (adv s 1)
              else s
              let c := ch s
              let s := if c == 0x65 || c == 0x45 then
                let s := addFlg (adv s 1) TokenFlags.scientific
                let s := let c2 := ch s; if c2 == 0x2B || c2 == 0x2D then adv s 1 else s
                let rec scanExp (s : Scanner) : Scanner :=
                  let c := ch s; if isDig c then scanExp (adv s 1) else s
                scanExp s
              else s
              let s := err s "Decimals with leading zeros are not allowed"
              let c := ch s
              let (s, k) := if c == 0x6E then (adv s 1, Kind.bigIntLiteral) else (s, Kind.numericLiteral)
              setTok (setVal s (extract s start s.state.pos)) k
          else let (s, k) := scanNum s; setTok s k
      -- '1'-'9' (Go: 696)
      | 0x31 | 0x32 | 0x33 | 0x34 | 0x35 | 0x36 | 0x37 | 0x38 | 0x39 =>
        let (s, k) := scanNum s; setTok s k
      -- ':' (Go: 698)
      | 0x3A => setTok (adv s 1) Kind.colonToken
      -- ';' (Go: 701)
      | 0x3B => setTok (adv s 1) Kind.semicolonToken
      -- '<' (Go: 704)
      | 0x3C =>
        match chAt s 1 with
        | 0x3C =>
          match chAt s 2 with
          | 0x3D => setTok (adv s 3) Kind.lessThanLessThanEqualsToken    -- <<=
          | _    => setTok (adv s 2) Kind.lessThanLessThanToken           -- <<
        | 0x3D => setTok (adv s 2) Kind.lessThanEqualsToken              -- <=
        | 0x2F =>  -- </
          if s.languageVariant == LanguageVariant.jsx && chAt s 2 != 0x2A
          then setTok (adv s 2) Kind.lessThanSlashToken
          else setTok (adv s 1) Kind.lessThanToken
        | _ => setTok (adv s 1) Kind.lessThanToken                        -- <
      -- '=' (Go: 732)
      | 0x3D =>
        match chAt s 1 with
        | 0x3D =>
          match chAt s 2 with
          | 0x3D => setTok (adv s 3) Kind.equalsEqualsEqualsToken        -- ===
          | _    => setTok (adv s 2) Kind.equalsEqualsToken               -- ==
        | 0x3E => setTok (adv s 2) Kind.equalsGreaterThanToken           -- =>
        | _    => setTok (adv s 1) Kind.equalsToken                       -- =
      -- '>' (Go: 757)
      | 0x3E => setTok (adv s 1) Kind.greaterThanToken
      -- '?' (Go: 769)
      | 0x3F =>
        match chAt s 1 with
        | 0x2E =>  -- ?.
          if !(isDig (chAt s 2)) then setTok (adv s 2) Kind.questionDotToken
          else setTok (adv s 1) Kind.questionToken
        | 0x3F =>
          match chAt s 2 with
          | 0x3D => setTok (adv s 3) Kind.questionQuestionEqualsToken    -- ??=
          | _    => setTok (adv s 2) Kind.questionQuestionToken           -- ??
        | _ => setTok (adv s 1) Kind.questionToken                        -- ?
      -- '@' (Go: 833)
      | 0x40 => setTok (adv s 1) Kind.atToken
      -- '[' (Go: 785)
      | 0x5B => setTok (adv s 1) Kind.openBracketToken
      -- ']' (Go: 788)
      | 0x5D => setTok (adv s 1) Kind.closeBracketToken
      -- '\' (Go: 836) — unicode escape identifier start
      | 0x5C =>
        let (_, cp) := peekUnicodeEscape s
        if cp != 0xFFFFFFFF && isIdentifierStart (Char.ofNat cp.toNat) then
          let (s, cp) := scanUnicodeEscape s true
          let startChar := String.singleton (Char.ofNat cp.toNat)
          -- Scan rest of identifier (may contain more escapes or normal chars)
          let rec scanParts (s : Scanner) (acc : String) : Scanner × String :=
            let c := ch s
            if isWord c || c == 0x24 then scanParts (adv s 1) (acc.push (Char.ofNat c.toNat))
            else if c == 0x5C then  -- another unicode escape
              let (_, cp) := peekUnicodeEscape s
              if cp != 0xFFFFFFFF && isIdentifierPart (Char.ofNat cp.toNat) then
                let (s, cp) := scanUnicodeEscape s true
                scanParts s (acc ++ String.singleton (Char.ofNat cp.toNat))
              else (s, acc)
            else
              let (cp, size) := runeAt s
              if size > 1 && isIdentifierPart (Char.ofNat cp.toNat) then scanParts (adv s size) (acc ++ String.singleton (Char.ofNat cp.toNat))
              else (s, acc)
          let (s, rest) := scanParts s ""
          let value := startChar ++ rest
          setTok (setVal s value) (getIdentifierToken value)
        else
          setTok (err (adv s 1) "Invalid character") Kind.unknown
      -- '^' (Go: 791)
      | 0x5E =>
        match chAt s 1 with
        | 0x3D => setTok (adv s 2) Kind.caretEqualsToken                 -- ^=
        | _    => setTok (adv s 1) Kind.caretToken                        -- ^
      -- '`' (Go: 480)
      | 0x60 => scanTmpl s true
      -- '{' (Go: 799)
      | 0x7B => setTok (adv s 1) Kind.openBraceToken
      -- '|' (Go: 802)
      | 0x7C =>
        match chAt s 1 with
        | 0x7C =>
          match chAt s 2 with
          | 0x3D => setTok (adv s 3) Kind.barBarEqualsToken              -- ||=
          | _    => setTok (adv s 2) Kind.barBarToken                     -- ||
        | 0x3D => setTok (adv s 2) Kind.barEqualsToken                   -- |=
        | _    => setTok (adv s 1) Kind.barToken                          -- |
      -- '}' (Go: 827)
      | 0x7D => setTok (adv s 1) Kind.closeBraceToken
      -- '~' (Go: 830)
      | 0x7E => setTok (adv s 1) Kind.tildeToken
      -- '#' (Go: 844)
      | 0x23 =>
        if chAt s 1 == 0x21 then  -- #! shebang
          if s.state.pos == 0 then
            -- Skip shebang line at start of file
            let rec skipLine (s : Scanner) : Scanner :=
              let c := ch s; if c == 0xFFFFFFFF || isLB c then s else skipLine (adv s 1)
            let s := skipLine (adv s 2)
            go s
          else
            setTok (err (adv s 1) "'#!' can only be used at the start of a file") Kind.unknown
        else
          let (s, ok) := scanIdent s 1
          if ok then setTok s Kind.privateIdentifier
          else setTok (setVal (err s "Invalid character") "#") Kind.privateIdentifier
      -- EOF (Go: 874)
      | 0xFFFFFFFF => setTok s Kind.endOfFile
      -- Default: identifier, non-ASCII whitespace, or unknown (Go: 878)
      | _ =>
        -- Check for non-ASCII whitespace first (Go: scanner.go:889)
        let (rune, runeSize) := runeAt s
        if isNonAsciiWhiteSpace rune then
          let s := if rune == 0x0085 then addFlg s TokenFlags.precedingLineBreak else s
          let s := adv s (if runeSize == 0 then 1 else runeSize)
          if s.skipTrivia then go s
          else
            -- Collect remaining non-ASCII whitespace (rare path)
            let rec skipNonAsciiWs (s : Scanner) : Scanner :=
              let (r2, sz2) := runeAt s
              if isNonAsciiWhiteSpace r2 then skipNonAsciiWs (adv s (if sz2 == 0 then 1 else sz2))
              else s
            setTok (skipNonAsciiWs s) Kind.whitespaceTrivia
        else
          let (s, ok) := scanIdent s 0
          if ok then setTok s (getIdentifierToken s.state.tokenValue)
          else
            -- Advance by full rune size to avoid corrupting multi-byte UTF-8
            let advSize := if runeSize == 0 then 1 else runeSize
            setTok (err (adv s advSize) "Invalid character") Kind.unknown
  go s

-- ============================================================
-- ReScan methods
-- ============================================================

/-- Based on Go: scanner.go:960 (ReScanLessThanToken) -/
def reScanLessThanToken (s : Scanner) : Scanner :=
  if s.state.token == Kind.lessThanLessThanToken then
    { s with state := { s.state with pos := s.state.tokenStart + 1, token := Kind.lessThanToken } }
  else s

/-- Based on Go: scanner.go:968 (ReScanGreaterThanToken) -/
def reScanGreaterThanToken (s : Scanner) : Scanner :=
  if s.state.token == Kind.greaterThanToken then
    let c := ch s
    if c == 0x3E then
      if chAt s 1 == 0x3E then
        if chAt s 2 == 0x3D then setTok (adv s 3) Kind.greaterThanGreaterThanGreaterThanEqualsToken
        else setTok (adv s 2) Kind.greaterThanGreaterThanGreaterThanToken
      else
        if chAt s 1 == 0x3D then setTok (adv s 2) Kind.greaterThanGreaterThanEqualsToken
        else setTok (adv s 1) Kind.greaterThanGreaterThanToken
    else
      if c == 0x3D then setTok (adv s 1) Kind.greaterThanEqualsToken
      else s
  else s

/-- Based on Go: scanner.go:995 (ReScanTemplateToken) -/
def reScanTemplateToken (s : Scanner) (_isTaggedTemplate : Bool) : Scanner :=
  let start := s.state.tokenStart
  let s := { s with state := { s.state with pos := start, tokenStart := start, tokenFlags := TokenFlags.none } }
  scanTmpl s false

/-- Based on Go: scanner.go:1001 (ReScanAsteriskEqualsToken) -/
def reScanAsteriskEqualsToken (s : Scanner) : Scanner :=
  if s.state.token == Kind.asteriskEqualsToken then
    { s with state := { s.state with pos := s.state.tokenStart + 1, token := Kind.equalsToken } }
  else s

/-- Based on Go: scanner.go:1011 (ReScanSlashToken) -/
partial def reScanSlashToken (s : Scanner) : Scanner :=
  if s.state.token == Kind.slashToken || s.state.token == Kind.slashEqualsToken then
    let start := s.state.tokenStart
    let s := { s with state := { s.state with pos := start + 1 } }
    let rec body (s : Scanner) (inCC : Bool) : Scanner :=
      let c := ch s
      if c == 0xFFFFFFFF || isLB c then addFlg (err s "Unterminated regex") TokenFlags.unterminated
      else
        if c == 0x5C then body (adv s 2) inCC
        else
          if c == 0x5B then body (adv s 1) true
          else
            if c == 0x5D && inCC then body (adv s 1) false
            else
              if c == 0x2F && !inCC then adv s 1
              else body (adv s 1) inCC
    let s := body s false
    let rec flg (s : Scanner) : Scanner :=
      if isAsciiLet (ch s) then flg (adv s 1) else s
    let s := flg s
    setTok (setVal s (extract s start s.state.pos)) Kind.regularExpressionLiteral
  else s

/-- Based on Go: scanner.go:1114 (ReScanHashToken) -/
def reScanHashToken (s : Scanner) : Scanner :=
  if s.state.token == Kind.privateIdentifier then
    setTok (setVal { s with state := { s.state with pos := s.state.tokenStart + 1 } } "#") Kind.hashToken
  else s

/-- Based on Go: scanner.go:1122 (ReScanQuestionToken) -/
def reScanQuestionToken (s : Scanner) : Scanner :=
  if s.state.token == Kind.questionQuestionToken then
    { s with state := { s.state with pos := s.state.tokenStart + 1, token := Kind.questionToken } }
  else s

/-- Based on Go: scanner.go:1135 (ScanJsxTokenEx) -/
partial def scanJsxTokenEx (s : Scanner) (allowMultilineJsxText : Bool) : Scanner :=
  let s := { s with state := { s.state with fullStartPos := s.state.pos, tokenStart := s.state.pos, tokenFlags := TokenFlags.none } }
  let c := ch s
  if c == 0xFFFFFFFF then
    setTok s Kind.endOfFile
  else
    if c == 0x3C then
      if chAt s 1 == 0x2F then setTok (adv s 2) Kind.lessThanSlashToken
      else setTok (adv s 1) Kind.lessThanToken
    else
      if c == 0x7B then
        setTok (adv s 1) Kind.openBraceToken
      else
        let rec go (s : Scanner) (allWs : Bool) : Scanner × Bool :=
          let c := ch s
          if c == 0xFFFFFFFF || c == 0x7B || c == 0x3C then (s, allWs)
          else
            if !allowMultilineJsxText && isLB c then (s, allWs)
            else
              let allWs := allWs && (isWsSingle c || isLB c)
              go (adv s 1) allWs
        let (s, allWs) := go s true
        let v := extract s s.state.fullStartPos s.state.pos
        let s := setVal s v
        if allWs then setTok s Kind.jsxTextAllWhiteSpaces else setTok s Kind.jsxText

/-- Based on Go: scanner.go:1131 (ScanJsxToken) -/
def scanJsxToken (s : Scanner) : Scanner :=
  scanJsxTokenEx s true

/-- Based on Go: scanner.go:1107 (ReScanJsxToken) -/
def reScanJsxToken (s : Scanner) (allowMultilineJsxText : Bool := true) : Scanner :=
  let s := { s with state := { s.state with pos := s.state.fullStartPos, tokenStart := s.state.fullStartPos } }
  scanJsxTokenEx s allowMultilineJsxText

/-- Based on Go: scanner.go:1203 (ScanJsxIdentifier) -/
partial def scanJsxIdentifier (s : Scanner) : Scanner :=
  if s.state.token == Kind.identifier || Kind.isKeywordKind s.state.token then
    let rec go (s : Scanner) : Scanner :=
      let c := ch s
      if c == 0x2D then
        go (adv s 1)
      else
        let (s', ok) := scanIdent s 0
        if ok then go s' else s
    let s := go s
    let v := extract s s.state.tokenStart s.state.pos
    setTok (setVal s v) (getIdentifierToken v)
  else s

/-- Based on Go: scanner.go:1230 (ScanJsxAttributeValue) -/
def scanJsxAttributeValue (s : Scanner) : Scanner :=
  let s := { s with state := { s.state with fullStartPos := s.state.pos, tokenStart := s.state.pos, tokenFlags := TokenFlags.none } }
  let c := ch s
  if c == 0x22 || c == 0x27 then
    let (s, v) := scanStr s (jsxAttributeString := true)
    setTok (setVal s v) Kind.stringLiteral
  else
    scan s

/-- Based on Go: scanner.go:1243 (ReScanJsxAttributeValue) -/
def reScanJsxAttributeValue (s : Scanner) : Scanner :=
  let s := { s with state := { s.state with pos := s.state.fullStartPos, tokenStart := s.state.fullStartPos } }
  scanJsxAttributeValue s

-- ============================================================
-- Convenience
-- ============================================================

/-- Scan all tokens, useful for testing. -/
partial def scanAll (text : String) : Array (Kind × String) :=
  let s := Scanner.new |>.setText text
  let rec go (s : Scanner) (acc : Array (Kind × String)) : Array (Kind × String) :=
    let s := s.scan
    if s.token == Kind.endOfFile then acc
    else go s (acc.push (s.token, s.state.tokenValue))
  go s #[]

end Scanner

end TSLean.Compiler
