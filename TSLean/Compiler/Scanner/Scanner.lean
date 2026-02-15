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
private def skipWs (s : Scanner) (fuel : Nat) : Scanner :=
  match fuel with
  | 0 => s
  | fuel + 1 => if isWsSingle (ch s) then skipWs (adv s 1) fuel else s

/-- Scan hex digits [0-9A-Fa-f_]. -/
private def scanHexDigits (s : Scanner) (fuel : Nat) : Scanner :=
  match fuel with
  | 0 => s
  | fuel + 1 =>
    let c := ch s
    if isDig c || (c >= 0x41 && c <= 0x46) || (c >= 0x61 && c <= 0x66) || c == 0x5F
    then scanHexDigits (adv s 1) fuel else s

/-- Scan binary digits [01_]. -/
private def scanBinDigits (s : Scanner) (fuel : Nat) : Scanner :=
  match fuel with
  | 0 => s
  | fuel + 1 =>
    let c := ch s
    if c == 0x30 || c == 0x31 || c == 0x5F then scanBinDigits (adv s 1) fuel else s

/-- Scan octal digits [0-7_]. -/
private def scanOctDigits (s : Scanner) (fuel : Nat) : Scanner :=
  match fuel with
  | 0 => s
  | fuel + 1 =>
    let c := ch s
    if (c >= 0x30 && c <= 0x37) || c == 0x5F then scanOctDigits (adv s 1) fuel else s

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

private def scanStr (s : Scanner) : Scanner × String :=
  let quote := ch s
  let s := if quote == 0x27 then addFlg s TokenFlags.singleQuote else s
  let s := adv s 1
  let rec go (s : Scanner) (acc : String) (fuel : Nat) : Scanner × String :=
    match fuel with
    | 0 => (s, acc)
    | fuel + 1 =>
      let c := ch s
      if c == 0xFFFFFFFF then (addFlg (err s "Unterminated string literal") TokenFlags.unterminated, acc)
      else if c == quote then (adv s 1, acc)
      else if c == 0x5C then -- '\\'
        let s := adv s 1; let nc := ch s
        if nc == 0xFFFFFFFF then (addFlg s TokenFlags.unterminated, acc ++ "\\")
        else go (adv s 1) (acc.push '\\' |>.push (Char.ofNat nc.toNat)) fuel
      else if c == 0x0A || c == 0x0D then (addFlg (err s "Unterminated string literal") TokenFlags.unterminated, acc)
      else go (adv s 1) (acc.push (Char.ofNat c.toNat)) fuel
  go s "" (s.bytes.size + 1)

-- ============================================================
-- Number scanning (Go: scanner.go:1731)
-- ============================================================

private def scanNum (s : Scanner) : Scanner × Kind :=
  let start := s.state.pos
  let rec digits (s : Scanner) (fuel : Nat) : Scanner :=
    match fuel with
    | 0 => s
    | fuel + 1 => let c := ch s; if isDig c || c == 0x5F then digits (adv s 1) fuel else s
  let s := digits s (s.bytes.size + 1)
  let s := if ch s == 0x2E then digits (adv s 1) (s.bytes.size + 1) else s  -- '.'
  let c := ch s
  let s := if c == 0x65 || c == 0x45 then  -- 'e'/'E'
    let s := addFlg (adv s 1) TokenFlags.scientific
    let s := let c2 := ch s; if c2 == 0x2B || c2 == 0x2D then adv s 1 else s
    digits s (s.bytes.size + 1)
  else s
  let c := ch s
  let (s, k) := if c == 0x6E then (adv s 1, Kind.bigIntLiteral) else (s, Kind.numericLiteral)
  (setVal s (extract s start s.state.pos), k)

-- ============================================================
-- Identifier scanning (Go: scanner.go:1396)
-- ============================================================

private def scanIdent (s : Scanner) (prefixLen : Nat) : Scanner × Bool :=
  let start := s.state.pos
  let s := adv s prefixLen
  let c := ch s
  if isAsciiLet c || c == 0x5F || c == 0x24 then
    let rec go (s : Scanner) (fuel : Nat) : Scanner :=
      match fuel with
      | 0 => s
      | fuel + 1 => let s := adv s 1; let c := ch s; if isWord c || c == 0x24 then go s fuel else s
    let s := go s (s.bytes.size + 1)
    (setVal s (extract s start s.state.pos), true)
  else
    ({ s with state := { s.state with pos := start + prefixLen } }, false)

-- ============================================================
-- Template scanning (Go: scanner.go:1508)
-- ============================================================

private def scanTmpl (s : Scanner) : Scanner :=
  let s := adv s 1
  let rec go (s : Scanner) (acc : String) (fuel : Nat) : Scanner × String × Kind :=
    match fuel with
    | 0 => (s, acc, Kind.noSubstitutionTemplateLiteral)
    | fuel + 1 =>
      let c := ch s
      if c == 0xFFFFFFFF then (addFlg (err s "Unterminated template") TokenFlags.unterminated, acc, Kind.noSubstitutionTemplateLiteral)
      else if c == 0x60 then (adv s 1, acc, Kind.noSubstitutionTemplateLiteral)
      else if c == 0x24 && chAt s 1 == 0x7B then (adv s 2, acc, Kind.templateHead)
      else if c == 0x5C then let s := adv s 1; let nc := ch s;
        if nc == 0xFFFFFFFF then (s, acc ++ "\\", Kind.noSubstitutionTemplateLiteral)
        else go (adv s 1) (acc.push '\\' |>.push (Char.ofNat nc.toNat)) fuel
      else go (adv s 1) (acc.push (Char.ofNat c.toNat)) fuel
  let (s, v, k) := go s "" (s.bytes.size + 1)
  setTok (setVal s v) k

-- ============================================================
-- Comment scanning
-- ============================================================

private def scanSLComment (s : Scanner) : Scanner :=
  let s := adv s 2
  let rec go (s : Scanner) (fuel : Nat) : Scanner :=
    match fuel with | 0 => s | fuel + 1 => let c := ch s; if c == 0xFFFFFFFF || isLB c then s else go (adv s 1) fuel
  go s (s.bytes.size + 1)

private def scanMLComment (s : Scanner) : Scanner × Bool :=
  let s := adv s 2
  let isJSDoc := ch s == 0x2A && chAt s 1 != 0x2F
  let rec go (s : Scanner) (fuel : Nat) : Scanner × Bool :=
    match fuel with
    | 0 => (s, false)
    | fuel + 1 =>
      let c := ch s
      if c == 0xFFFFFFFF then (s, false)
      else if c == 0x2A && chAt s 1 == 0x2F then (adv s 2, true)
      else go (if isLB c then addFlg (adv s 1) TokenFlags.precedingLineBreak else adv s 1) fuel
  let (s, closed) := go s (s.bytes.size + 1)
  let s := if isJSDoc then addFlg s TokenFlags.precedingJSDocComment else s
  let s := if !closed then addFlg (err s "Expected '*/'") TokenFlags.unterminated else s
  (s, closed)

-- ============================================================
-- Main scan (Go: scanner.go:431-917)
-- ============================================================

def scan (s : Scanner) : Scanner :=
  let s := { s with state := { s.state with fullStartPos := s.state.pos, tokenFlags := TokenFlags.none } }
  let bsz := s.bytes.size
  let rec go (s : Scanner) (fuel : Nat) : Scanner :=
    match fuel with
    | 0 => setTok s Kind.endOfFile
    | fuel + 1 =>
      let s := { s with state := { s.state with tokenStart := s.state.pos } }
      let c := ch s
      match c with
      -- Whitespace (Go: 439)
      | 0x09 | 0x0B | 0x0C | 0x20 =>
        let s := adv s 1
        if s.skipTrivia then go s fuel
        else setTok (skipWs s fuel) Kind.whitespaceTrivia
      -- Newline (Go: 452)
      | 0x0A | 0x0D =>
        let s := addFlg s TokenFlags.precedingLineBreak
        let s := if c == 0x0D && chAt s 1 == 0x0A then adv s 2 else adv s 1
        if s.skipTrivia then go s fuel else setTok s Kind.newLineTrivia
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
        else if chAt s 1 == 0x2E && chAt s 2 == 0x2E then setTok (adv s 3) Kind.dotDotDotToken
        else setTok (adv s 1) Kind.dotToken
      -- '/' (Go: 569)
      | 0x2F =>
        match chAt s 1 with
        | 0x2F =>  -- //
          let s := scanSLComment s
          if s.skipTrivia then go s fuel else setTok s Kind.singleLineCommentTrivia
        | 0x2A =>  -- /*
          let (s, _) := scanMLComment s
          if s.skipTrivia then go s fuel else setTok s Kind.multiLineCommentTrivia
        | 0x3D => setTok (adv s 2) Kind.slashEqualsToken                 -- /=
        | _    => setTok (adv s 1) Kind.slashToken                        -- /
      -- '0' prefix (Go: 644)
      | 0x30 =>
        let nx := chAt s 1
        match nx with
        | 0x58 | 0x78 =>  -- 'X' 'x' hex
          let s := addFlg (adv s 2) TokenFlags.hexSpecifier
          let start := s.state.pos - 2
          let s := scanHexDigits s (bsz + 1)
          let s := setVal s (extract s start s.state.pos)
          if ch s == 0x6E then setTok (adv s 1) Kind.bigIntLiteral else setTok s Kind.numericLiteral
        | 0x42 | 0x62 =>  -- 'B' 'b' binary
          let s := addFlg (adv s 2) TokenFlags.binarySpecifier
          let start := s.state.pos - 2
          let s := scanBinDigits s (bsz + 1)
          let s := setVal s (extract s start s.state.pos)
          if ch s == 0x6E then setTok (adv s 1) Kind.bigIntLiteral else setTok s Kind.numericLiteral
        | 0x4F | 0x6F =>  -- 'O' 'o' octal
          let s := addFlg (adv s 2) TokenFlags.octalSpecifier
          let start := s.state.pos - 2
          let s := scanOctDigits s (bsz + 1)
          let s := setVal s (extract s start s.state.pos)
          if ch s == 0x6E then setTok (adv s 1) Kind.bigIntLiteral else setTok s Kind.numericLiteral
        | _ => let (s, k) := scanNum s; setTok s k
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
      -- '^' (Go: 791)
      | 0x5E =>
        match chAt s 1 with
        | 0x3D => setTok (adv s 2) Kind.caretEqualsToken                 -- ^=
        | _    => setTok (adv s 1) Kind.caretToken                        -- ^
      -- '`' (Go: 480)
      | 0x60 => scanTmpl s
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
        let (s, ok) := scanIdent s 1
        if ok then setTok s Kind.privateIdentifier
        else setTok (setVal (err s "Invalid character") "#") Kind.privateIdentifier
      -- EOF (Go: 874)
      | 0xFFFFFFFF => setTok s Kind.endOfFile
      -- Default: identifier or unknown (Go: 878)
      | _ =>
        let (s, ok) := scanIdent s 0
        if ok then setTok s (getIdentifierToken s.state.tokenValue)
        else setTok (err (adv s 1) "Invalid character") Kind.unknown
  go s (bsz + 2)

-- ============================================================
-- ReScan methods
-- ============================================================

/-- Based on Go: scanner.go:968 (ReScanGreaterThanToken) -/
def reScanGreaterThanToken (s : Scanner) : Scanner :=
  if s.state.token == Kind.greaterThanToken then
    let c := ch s
    if c == 0x3E then
      if chAt s 1 == 0x3E then
        if chAt s 2 == 0x3D then setTok (adv s 3) Kind.greaterThanGreaterThanGreaterThanEqualsToken
        else setTok (adv s 2) Kind.greaterThanGreaterThanGreaterThanToken
      else if chAt s 1 == 0x3D then setTok (adv s 2) Kind.greaterThanGreaterThanEqualsToken
      else setTok (adv s 1) Kind.greaterThanGreaterThanToken
    else if c == 0x3D then setTok (adv s 1) Kind.greaterThanEqualsToken
    else s
  else s

/-- Based on Go: scanner.go:1011 (ReScanSlashToken) -/
def reScanSlashToken (s : Scanner) : Scanner :=
  if s.state.token == Kind.slashToken || s.state.token == Kind.slashEqualsToken then
    let start := s.state.tokenStart
    let s := { s with state := { s.state with pos := start + 1 } }
    let rec body (s : Scanner) (inCC : Bool) (fuel : Nat) : Scanner := match fuel with
      | 0 => s
      | fuel + 1 =>
        let c := ch s
        if c == 0xFFFFFFFF || isLB c then addFlg (err s "Unterminated regex") TokenFlags.unterminated
        else if c == 0x5C then body (adv s 2) inCC fuel
        else if c == 0x5B then body (adv s 1) true fuel
        else if c == 0x5D && inCC then body (adv s 1) false fuel
        else if c == 0x2F && !inCC then adv s 1
        else body (adv s 1) inCC fuel
    let s := body s false (s.bytes.size + 1)
    let rec flg (s : Scanner) (fuel : Nat) : Scanner := match fuel with
      | 0 => s | fuel + 1 => if isAsciiLet (ch s) then flg (adv s 1) fuel else s
    let s := flg s 10
    setTok (setVal s (extract s start s.state.pos)) Kind.regularExpressionLiteral
  else s

-- ============================================================
-- Convenience
-- ============================================================

/-- Scan all tokens, useful for testing. -/
def scanAll (text : String) : Array (Kind × String) :=
  let s := Scanner.new |>.setText text
  let rec go (s : Scanner) (acc : Array (Kind × String)) (fuel : Nat) : Array (Kind × String) :=
    match fuel with
    | 0 => acc
    | fuel + 1 =>
      let s := s.scan
      if s.token == Kind.endOfFile then acc
      else go s (acc.push (s.token, s.state.tokenValue)) fuel
  go s #[] (text.length + 2)

end Scanner

end TSLean.Compiler
