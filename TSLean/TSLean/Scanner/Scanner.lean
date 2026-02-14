-- TSLean.Scanner.Scanner: Core scanner (lexer) state machine.
-- Mirrors TypeScript's scanner. Pure functions: Scanner → Scanner.
-- The parser calls `scan` repeatedly to advance through tokens.

import TSLean.Ast.SyntaxKind
import TSLean.Ast.Flags
import TSLean.Scanner.CharCodes
import TSLean.Scanner.Keywords

namespace TSLean.Scanner

open TSLean.Ast

/-- Language variant affects JSX parsing. -/
inductive LanguageVariant where
  | standard
  | jsx
  deriving BEq, Repr, Inhabited

/-- Script target affects keyword recognition (e.g., `using`). -/
inductive ScriptTarget where
  | es3 | es5 | es2015 | es2016 | es2017 | es2018 | es2019 | es2020
  | es2021 | es2022 | es2023 | es2024 | esNext | latest
  deriving BEq, Repr, Inhabited

/-- The scanner state. All positions are byte offsets into the UTF-8 encoded `text`.
    We store the text as a `ByteArray` for O(1) byte access, plus the original `String`
    for `extract`. -/
structure Scanner where
  text             : String
  bytes            : ByteArray
  pos              : Nat          -- current scan position (byte offset)
  len              : Nat          -- total byte length
  startPos         : Nat          -- start of current token (before trivia)
  tokenStart       : Nat          -- start of current token value (after trivia)
  token            : SyntaxKind   -- current token kind
  tokenValue       : String       -- current token text value
  tokenFlags       : TokenFlags   -- flags for current token
  skipTrivia       : Bool         -- whether to skip trivia (usually true)
  languageVariant  : LanguageVariant
  scriptTarget     : ScriptTarget
  inTemplateString : Bool         -- currently inside a template literal
  deriving Inhabited

namespace Scanner

/-- Create a scanner for the given source text. -/
def create (text : String) (languageVariant : LanguageVariant := .standard)
    (scriptTarget : ScriptTarget := .latest) : Scanner :=
  let bytes := text.toUTF8
  { text := text
    bytes := bytes
    pos := 0
    len := bytes.size
    startPos := 0
    tokenStart := 0
    token := .unknown
    tokenValue := ""
    tokenFlags := TokenFlags.none
    skipTrivia := true
    languageVariant := languageVariant
    scriptTarget := scriptTarget
    inTemplateString := false }

/-- Get the byte at position `p`, or 0 if past end. For ASCII-range dispatch. -/
@[inline] private def byteAt (s : Scanner) (p : Nat) : UInt8 :=
  if h : p < s.bytes.size then s.bytes[p] else 0

/-- Get the character at position `p` by decoding from the UTF-8 bytes. -/
@[inline] private def charAt (s : Scanner) (p : Nat) : Char :=
  if p >= s.len then '\x00'
  else String.Pos.Raw.get s.text ⟨p⟩

/-- Extract a substring from byte offset `start` to `stop`. -/
@[inline] private def extract (s : Scanner) (start stop : Nat) : String :=
  Substring.Raw.toString { str := s.text, startPos := ⟨start⟩, stopPos := ⟨stop⟩ }

/-- Advance position past whitespace and comments. Returns updated scanner.
    Uses `partial` since termination depends on position advancing toward end. -/
partial def scanTrivia (s : Scanner) : Scanner :=
  if s.pos >= s.len then s
  else
    let b := s.byteAt s.pos
    -- Fast path: ASCII whitespace
    if b == 0x20 || b == 0x09 then -- space or tab
      scanTrivia { s with pos := s.pos + 1 }
    else if b == 0x0A then -- \n
      scanTrivia { s with pos := s.pos + 1,
                          tokenFlags := s.tokenFlags ||| TokenFlags.precedingLineBreak }
    else if b == 0x0D then -- \r
      let next := s.pos + 1
      let next := if s.byteAt next == 0x0A then next + 1 else next
      scanTrivia { s with pos := next,
                          tokenFlags := s.tokenFlags ||| TokenFlags.precedingLineBreak }
    else if b == 0x0B || b == 0x0C then -- vertical tab or form feed
      scanTrivia { s with pos := s.pos + 1 }
    else if b == 0x2F then -- '/'
      let next := s.byteAt (s.pos + 1)
      if next == 0x2F then -- '//' single-line comment
        let s := { s with pos := s.pos + 2 }
        let rec skipLine (s : Scanner) : Scanner :=
          if s.pos >= s.len then s
          else
            let b := s.byteAt s.pos
            if b == 0x0A || b == 0x0D then s
            else skipLine { s with pos := s.pos + 1 }
        scanTrivia (skipLine s)
      else if next == 0x2A then -- '/*' multi-line comment
        let s := { s with pos := s.pos + 2 }
        let rec skipBlock (s : Scanner) : Scanner :=
          if s.pos >= s.len then s
          else if s.byteAt s.pos == 0x2A && s.byteAt (s.pos + 1) == 0x2F then
            { s with pos := s.pos + 2 }
          else
            let b := s.byteAt s.pos
            let s := if b == 0x0A || b == 0x0D then
              { s with tokenFlags := s.tokenFlags ||| TokenFlags.precedingLineBreak }
            else s
            skipBlock { s with pos := s.pos + 1 }
        scanTrivia (skipBlock s)
      else s
    else if b > 0x7F then
      -- Non-ASCII: check for unicode whitespace
      let ch := s.charAt s.pos
      if isWhiteSpaceSingleLine ch then
        scanTrivia { s with pos := s.pos + ch.utf8Size }
      else if isLineBreak ch then
        scanTrivia { s with pos := s.pos + ch.utf8Size,
                            tokenFlags := s.tokenFlags ||| TokenFlags.precedingLineBreak }
      else s
    else s

/-- Scan an identifier or keyword starting at current position. -/
partial def scanIdentifier (s : Scanner) : Scanner :=
  let startPos := s.pos
  let rec loop (p : Nat) : Nat :=
    if p >= s.len then p
    else
      let b := s.byteAt p
      -- Fast path: ASCII identifier chars
      if (b >= 0x61 && b <= 0x7A) || (b >= 0x41 && b <= 0x5A) ||
         (b >= 0x30 && b <= 0x39) || b == 0x5F || b == 0x24 then
        loop (p + 1)
      else if b > 0x7F then
        let ch := s.charAt p
        if isIdentifierPart ch then loop (p + ch.utf8Size)
        else p
      else p
  let endPos := loop (s.pos + 1)
  let value := s.extract startPos endPos
  let token := match lookupKeyword value with
    | some kw => kw
    | none => SyntaxKind.identifier
  { s with pos := endPos, token := token, tokenValue := value }

/-- Scan a numeric literal. -/
partial def scanNumber (s : Scanner) : Scanner :=
  let startPos := s.pos
  let b0 := s.byteAt s.pos
  if b0 == 0x30 then -- '0'
    let b1 := s.byteAt (s.pos + 1)
    if b1 == 0x78 || b1 == 0x58 then -- '0x' or '0X'
      let rec loopHex (p : Nat) : Nat :=
        if p >= s.len then p
        else
          let b := s.byteAt p
          if (b >= 0x30 && b <= 0x39) || (b >= 0x61 && b <= 0x66) ||
             (b >= 0x41 && b <= 0x46) || b == 0x5F then loopHex (p + 1) -- hex digit or _
          else p
      let endPos := loopHex (s.pos + 2)
      let (endPos, tok) := if s.byteAt endPos == 0x6E then (endPos + 1, SyntaxKind.bigIntLiteral)
                           else (endPos, SyntaxKind.numericLiteral)
      { s with pos := endPos, token := tok,
               tokenValue := s.extract startPos endPos,
               tokenFlags := s.tokenFlags ||| TokenFlags.hexSpecifier }
    else if b1 == 0x62 || b1 == 0x42 then -- '0b' or '0B'
      let rec loopBin (p : Nat) : Nat :=
        if p >= s.len then p
        else
          let b := s.byteAt p
          if b == 0x30 || b == 0x31 || b == 0x5F then loopBin (p + 1) -- 0, 1, or _
          else p
      let endPos := loopBin (s.pos + 2)
      let (endPos, tok) := if s.byteAt endPos == 0x6E then (endPos + 1, SyntaxKind.bigIntLiteral)
                           else (endPos, SyntaxKind.numericLiteral)
      { s with pos := endPos, token := tok,
               tokenValue := s.extract startPos endPos,
               tokenFlags := s.tokenFlags ||| TokenFlags.binarySpecifier }
    else if b1 == 0x6F || b1 == 0x4F then -- '0o' or '0O'
      let rec loopOct (p : Nat) : Nat :=
        if p >= s.len then p
        else
          let b := s.byteAt p
          if (b >= 0x30 && b <= 0x37) || b == 0x5F then loopOct (p + 1) -- octal digit or _
          else p
      let endPos := loopOct (s.pos + 2)
      let (endPos, tok) := if s.byteAt endPos == 0x6E then (endPos + 1, SyntaxKind.bigIntLiteral)
                           else (endPos, SyntaxKind.numericLiteral)
      { s with pos := endPos, token := tok,
               tokenValue := s.extract startPos endPos,
               tokenFlags := s.tokenFlags ||| TokenFlags.octalSpecifier }
    else
      scanDecimalDigits s startPos
  else
    scanDecimalDigits s startPos
where
  scanDecimalDigits (s : Scanner) (startPos : Nat) : Scanner :=
    let rec loop (p : Nat) : Nat :=
      if p >= s.len then p
      else
        let b := s.byteAt p
        if (b >= 0x30 && b <= 0x39) || b == 0x5F then loop (p + 1) -- digit or _
        else if b == 0x2E then -- '.'
          -- Check if next is also digit (avoid `1..toString()`)
          let p' := p + 1
          if p' < s.len && (s.byteAt p' >= 0x30 && s.byteAt p' <= 0x39) then loop p'
          else p
        else if b == 0x65 || b == 0x45 then -- 'e' or 'E'
          let p' := p + 1
          let p' := if p' < s.len && (s.byteAt p' == 0x2B || s.byteAt p' == 0x2D) then p' + 1 else p'
          loop p'
        else p
    let endPos := loop (s.pos + 1)
    let (endPos, tok) := if s.byteAt endPos == 0x6E then (endPos + 1, SyntaxKind.bigIntLiteral)
                         else (endPos, SyntaxKind.numericLiteral)
    { s with pos := endPos, token := tok, tokenValue := s.extract startPos endPos }

/-- Scan a string literal (single or double quoted). -/
partial def scanString (s : Scanner) (quote : UInt8) : Scanner :=
  let startPos := s.pos
  let rec loop (p : Nat) : Scanner :=
    if p >= s.len then
      { s with pos := p, token := .stringLiteral,
               tokenValue := s.extract startPos p,
               tokenFlags := s.tokenFlags ||| TokenFlags.unterminated }
    else
      let b := s.byteAt p
      if b == quote then
        { s with pos := p + 1, token := .stringLiteral,
                 tokenValue := s.extract startPos (p + 1) }
      else if b == 0x5C then -- '\\'
        loop (p + 2)
      else if b == 0x0A || b == 0x0D then
        { s with pos := p, token := .stringLiteral,
                 tokenValue := s.extract startPos p,
                 tokenFlags := s.tokenFlags ||| TokenFlags.unterminated }
      else
        loop (p + 1)
  loop (s.pos + 1)

/-- Scan a template literal part (after ` or }). -/
partial def scanTemplatePart (s : Scanner) : Scanner :=
  let startPos := s.pos
  let rec loop (p : Nat) : Scanner :=
    if p >= s.len then
      let tok := if s.inTemplateString then SyntaxKind.templateTail
                 else SyntaxKind.noSubstitutionTemplateLiteral
      { s with pos := p, token := tok,
               tokenValue := s.extract startPos p,
               tokenFlags := s.tokenFlags ||| TokenFlags.unterminated }
    else
      let b := s.byteAt p
      if b == 0x60 then -- '`'
        let tok := if s.inTemplateString then SyntaxKind.templateTail
                   else SyntaxKind.noSubstitutionTemplateLiteral
        { s with pos := p + 1, token := tok,
                 tokenValue := s.extract startPos (p + 1),
                 inTemplateString := false }
      else if b == 0x24 && s.byteAt (p + 1) == 0x7B then -- '${'
        let tok := if s.inTemplateString then SyntaxKind.templateMiddle
                   else SyntaxKind.templateHead
        { s with pos := p + 2, token := tok,
                 tokenValue := s.extract startPos (p + 2),
                 inTemplateString := true }
      else if b == 0x5C then -- '\\'
        loop (p + 2)
      else if b == 0x0A || b == 0x0D then
        loop (p + 1)  -- newlines are allowed in templates
      else
        loop (p + 1)
  loop s.pos

/-- The main scan function. Advances to the next token and returns the updated scanner. -/
def scan (s : Scanner) : Scanner :=
  let s := { s with startPos := s.pos, tokenFlags := TokenFlags.none }
  let s := if s.skipTrivia then s.scanTrivia else s
  let s := { s with tokenStart := s.pos }
  if s.pos >= s.len then
    { s with token := .endOfFileToken, tokenValue := "" }
  else
    let b := s.byteAt s.pos
    -- Fast path: ASCII identifier start (a-z, A-Z, _, $)
    if (b >= 0x61 && b <= 0x7A) || (b >= 0x41 && b <= 0x5A) ||
       b == 0x5F || b == 0x24 then
      s.scanIdentifier
    -- Digit (0-9)
    else if b >= 0x30 && b <= 0x39 then
      s.scanNumber
    -- Non-ASCII: might be identifier start
    else if b > 0x7F then
      let ch := s.charAt s.pos
      if isIdentifierStart ch then s.scanIdentifier
      else { s with pos := s.pos + ch.utf8Size, token := .unknown, tokenValue := ch.toString }
    else
    -- Punctuation / operator dispatch
    match b with
    | 0x7B => { s with pos := s.pos + 1, token := .openBraceToken, tokenValue := "{" }     -- {
    | 0x7D =>                                                                                 -- }
      if s.inTemplateString then
        scanTemplatePart { s with pos := s.pos + 1 }
      else
        { s with pos := s.pos + 1, token := .closeBraceToken, tokenValue := "}" }
    | 0x28 => { s with pos := s.pos + 1, token := .openParenToken, tokenValue := "(" }      -- (
    | 0x29 => { s with pos := s.pos + 1, token := .closeParenToken, tokenValue := ")" }     -- )
    | 0x5B => { s with pos := s.pos + 1, token := .openBracketToken, tokenValue := "[" }    -- [
    | 0x5D => { s with pos := s.pos + 1, token := .closeBracketToken, tokenValue := "]" }   -- ]
    | 0x3B => { s with pos := s.pos + 1, token := .semicolonToken, tokenValue := ";" }      -- ;
    | 0x2C => { s with pos := s.pos + 1, token := .commaToken, tokenValue := "," }          -- ,
    | 0x7E => { s with pos := s.pos + 1, token := .tildeToken, tokenValue := "~" }          -- ~
    | 0x40 => { s with pos := s.pos + 1, token := .atToken, tokenValue := "@" }             -- @
    | 0x22 => s.scanString 0x22                                                               -- "
    | 0x27 => s.scanString 0x27                                                               -- '
    | 0x60 => scanTemplatePart { s with pos := s.pos + 1 }                                    -- `
    | 0x2E =>                                                                                 -- .
      let b1 := s.byteAt (s.pos + 1)
      if b1 >= 0x30 && b1 <= 0x39 then s.scanNumber
      else if b1 == 0x2E && s.byteAt (s.pos + 2) == 0x2E then
        { s with pos := s.pos + 3, token := .dotDotDotToken, tokenValue := "..." }
      else
        { s with pos := s.pos + 1, token := .dotToken, tokenValue := "." }
    | 0x21 =>                                                                                 -- !
      let b1 := s.byteAt (s.pos + 1)
      if b1 == 0x3D then
        if s.byteAt (s.pos + 2) == 0x3D then
          { s with pos := s.pos + 3, token := .exclamationEqualsEqualsToken, tokenValue := "!==" }
        else
          { s with pos := s.pos + 2, token := .exclamationEqualsToken, tokenValue := "!=" }
      else
        { s with pos := s.pos + 1, token := .exclamationToken, tokenValue := "!" }
    | 0x3F =>                                                                                 -- ?
      let b1 := s.byteAt (s.pos + 1)
      if b1 == 0x2E then
        let b2 := s.byteAt (s.pos + 2)
        if b2 < 0x30 || b2 > 0x39 then  -- not a digit after ?.
          { s with pos := s.pos + 2, token := .questionDotToken, tokenValue := "?." }
        else
          { s with pos := s.pos + 1, token := .questionToken, tokenValue := "?" }
      else if b1 == 0x3F then
        if s.byteAt (s.pos + 2) == 0x3D then
          { s with pos := s.pos + 3, token := .questionQuestionEqualsToken, tokenValue := "??=" }
        else
          { s with pos := s.pos + 2, token := .questionQuestionToken, tokenValue := "??" }
      else
        { s with pos := s.pos + 1, token := .questionToken, tokenValue := "?" }
    | 0x3A => { s with pos := s.pos + 1, token := .colonToken, tokenValue := ":" }          -- :
    | 0x2B =>                                                                                 -- +
      let b1 := s.byteAt (s.pos + 1)
      if b1 == 0x2B then
        { s with pos := s.pos + 2, token := .plusPlusToken, tokenValue := "++" }
      else if b1 == 0x3D then
        { s with pos := s.pos + 2, token := .plusEqualsToken, tokenValue := "+=" }
      else
        { s with pos := s.pos + 1, token := .plusToken, tokenValue := "+" }
    | 0x2D =>                                                                                 -- -
      let b1 := s.byteAt (s.pos + 1)
      if b1 == 0x2D then
        { s with pos := s.pos + 2, token := .minusMinusToken, tokenValue := "--" }
      else if b1 == 0x3D then
        { s with pos := s.pos + 2, token := .minusEqualsToken, tokenValue := "-=" }
      else
        { s with pos := s.pos + 1, token := .minusToken, tokenValue := "-" }
    | 0x2A =>                                                                                 -- *
      let b1 := s.byteAt (s.pos + 1)
      if b1 == 0x2A then
        if s.byteAt (s.pos + 2) == 0x3D then
          { s with pos := s.pos + 3, token := .asteriskAsteriskEqualsToken, tokenValue := "**=" }
        else
          { s with pos := s.pos + 2, token := .asteriskAsteriskToken, tokenValue := "**" }
      else if b1 == 0x3D then
        { s with pos := s.pos + 2, token := .asteriskEqualsToken, tokenValue := "*=" }
      else
        { s with pos := s.pos + 1, token := .asteriskToken, tokenValue := "*" }
    | 0x2F =>                                                                                 -- /
      if s.byteAt (s.pos + 1) == 0x3D then
        { s with pos := s.pos + 2, token := .slashEqualsToken, tokenValue := "/=" }
      else
        { s with pos := s.pos + 1, token := .slashToken, tokenValue := "/" }
    | 0x25 =>                                                                                 -- %
      if s.byteAt (s.pos + 1) == 0x3D then
        { s with pos := s.pos + 2, token := .percentEqualsToken, tokenValue := "%=" }
      else
        { s with pos := s.pos + 1, token := .percentToken, tokenValue := "%" }
    | 0x3C =>                                                                                 -- <
      let b1 := s.byteAt (s.pos + 1)
      if b1 == 0x3C then
        if s.byteAt (s.pos + 2) == 0x3D then
          { s with pos := s.pos + 3, token := .lessThanLessThanEqualsToken, tokenValue := "<<=" }
        else
          { s with pos := s.pos + 2, token := .lessThanLessThanToken, tokenValue := "<<" }
      else if b1 == 0x3D then
        { s with pos := s.pos + 2, token := .lessThanEqualsToken, tokenValue := "<=" }
      else if b1 == 0x2F && s.languageVariant == .jsx then
        { s with pos := s.pos + 2, token := .lessThanSlashToken, tokenValue := "</" }
      else
        { s with pos := s.pos + 1, token := .lessThanToken, tokenValue := "<" }
    | 0x3E =>                                                                                 -- >
      if s.byteAt (s.pos + 1) == 0x3D then
        { s with pos := s.pos + 2, token := .greaterThanEqualsToken, tokenValue := ">=" }
      else
        { s with pos := s.pos + 1, token := .greaterThanToken, tokenValue := ">" }
    | 0x3D =>                                                                                 -- =
      let b1 := s.byteAt (s.pos + 1)
      if b1 == 0x3D then
        if s.byteAt (s.pos + 2) == 0x3D then
          { s with pos := s.pos + 3, token := .equalsEqualsEqualsToken, tokenValue := "===" }
        else
          { s with pos := s.pos + 2, token := .equalsEqualsToken, tokenValue := "==" }
      else if b1 == 0x3E then
        { s with pos := s.pos + 2, token := .equalsGreaterThanToken, tokenValue := "=>" }
      else
        { s with pos := s.pos + 1, token := .equalsToken, tokenValue := "=" }
    | 0x26 =>                                                                                 -- &
      let b1 := s.byteAt (s.pos + 1)
      if b1 == 0x26 then
        if s.byteAt (s.pos + 2) == 0x3D then
          { s with pos := s.pos + 3, token := .ampersandAmpersandEqualsToken, tokenValue := "&&=" }
        else
          { s with pos := s.pos + 2, token := .ampersandAmpersandToken, tokenValue := "&&" }
      else if b1 == 0x3D then
        { s with pos := s.pos + 2, token := .ampersandEqualsToken, tokenValue := "&=" }
      else
        { s with pos := s.pos + 1, token := .ampersandToken, tokenValue := "&" }
    | 0x7C =>                                                                                 -- |
      let b1 := s.byteAt (s.pos + 1)
      if b1 == 0x7C then
        if s.byteAt (s.pos + 2) == 0x3D then
          { s with pos := s.pos + 3, token := .barBarEqualsToken, tokenValue := "||=" }
        else
          { s with pos := s.pos + 2, token := .barBarToken, tokenValue := "||" }
      else if b1 == 0x3D then
        { s with pos := s.pos + 2, token := .barEqualsToken, tokenValue := "|=" }
      else
        { s with pos := s.pos + 1, token := .barToken, tokenValue := "|" }
    | 0x5E =>                                                                                 -- ^
      if s.byteAt (s.pos + 1) == 0x3D then
        { s with pos := s.pos + 2, token := .caretEqualsToken, tokenValue := "^=" }
      else
        { s with pos := s.pos + 1, token := .caretToken, tokenValue := "^" }
    | 0x23 =>                                                                                 -- #
      if s.pos == 0 && s.byteAt 1 == 0x21 then -- shebang #!
        let rec skipLine (p : Nat) : Nat :=
          if p >= s.len then p
          else if s.byteAt p == 0x0A || s.byteAt p == 0x0D then p
          else skipLine (p + 1)
        let endPos := skipLine (s.pos + 2)
        { s with pos := endPos, token := .shebangTrivia,
                 tokenValue := s.extract s.pos endPos }
      else
        { s with pos := s.pos + 1, token := .hashToken, tokenValue := "#" }
    | _ =>
      { s with pos := s.pos + 1, token := .unknown, tokenValue := "" }

/-- Get the current token. -/
@[inline] def getToken (s : Scanner) : SyntaxKind := s.token

/-- Get the current token's text value. -/
@[inline] def getTokenValue (s : Scanner) : String := s.tokenValue

/-- Get the start position of the current token (after trivia). -/
@[inline] def getTokenStart (s : Scanner) : Nat := s.tokenStart

/-- Get the start position including leading trivia. -/
@[inline] def getStartPos (s : Scanner) : Nat := s.startPos

/-- Get the current position (end of current token). -/
@[inline] def getPos (s : Scanner) : Nat := s.pos

/-- Whether the current token was preceded by a line break. -/
@[inline] def hasPrecedingLineBreak (s : Scanner) : Bool :=
  TokenFlags.hasFlag s.tokenFlags TokenFlags.precedingLineBreak

/-- Set the scanner position (for lookahead/backtracking by the parser). -/
def setPos (s : Scanner) (newPos : Nat) : Scanner :=
  { s with pos := newPos, token := .unknown, tokenValue := "" }

/-- Re-scan the current > token to see if it's part of >> or >>>. -/
def reScanGreaterToken (s : Scanner) : Scanner :=
  if s.token == .greaterThanToken then
    let b := s.byteAt s.pos
    if b == 0x3E then -- >
      let b2 := s.byteAt (s.pos + 1)
      if b2 == 0x3E then -- >>>
        if s.byteAt (s.pos + 2) == 0x3D then
          { s with pos := s.pos + 3, token := .greaterThanGreaterThanGreaterThanEqualsToken,
                   tokenValue := ">>>=" }
        else
          { s with pos := s.pos + 2, token := .greaterThanGreaterThanGreaterThanToken,
                   tokenValue := ">>>" }
      else if b2 == 0x3D then -- >>=
        { s with pos := s.pos + 2, token := .greaterThanGreaterThanEqualsToken,
                 tokenValue := ">>=" }
      else -- >>
        { s with pos := s.pos + 1, token := .greaterThanGreaterThanToken,
                 tokenValue := ">>" }
    else s
  else s

/-- Re-scan the current / token as the start of a regular expression. -/
partial def reScanSlashToken (s : Scanner) : Scanner :=
  if s.token == .slashToken || s.token == .slashEqualsToken then
    let startPos := s.tokenStart
    let rec loop (p : Nat) (inCharClass : Bool) : Scanner :=
      if p >= s.len then
        { s with pos := p, token := .regularExpressionLiteral,
                 tokenFlags := s.tokenFlags ||| TokenFlags.unterminated }
      else
        let b := s.byteAt p
        if b == 0x0A || b == 0x0D then -- line break = unterminated
          { s with pos := p, token := .regularExpressionLiteral,
                   tokenFlags := s.tokenFlags ||| TokenFlags.unterminated }
        else if b == 0x5C then -- backslash: skip next
          loop (p + 2) inCharClass
        else if b == 0x5B then -- [
          loop (p + 1) true
        else if b == 0x5D && inCharClass then -- ]
          loop (p + 1) false
        else if b == 0x2F && !inCharClass then -- / end of body
          -- Scan regex flags
          let rec scanFlags (p : Nat) : Nat :=
            if p >= s.len then p
            else
              let b := s.byteAt p
              if (b >= 0x61 && b <= 0x7A) || (b >= 0x41 && b <= 0x5A) then
                scanFlags (p + 1)
              else p
          let endPos := scanFlags (p + 1)
          { s with pos := endPos, token := .regularExpressionLiteral,
                   tokenValue := s.extract startPos endPos }
        else
          loop (p + 1) inCharClass
    loop (startPos + 1) false
  else s

end Scanner

end TSLean.Scanner
