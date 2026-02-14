-- TSLean.Scanner.CharCodes: Character classification for the scanner.
-- Mirrors the character utilities in TypeScript's scanner.

namespace TSLean.Scanner

-- Character code constants used by the scanner.
namespace CharCodes
  def nullChar          : Char := '\x00'
  def tab               : Char := '\t'
  def lineFeed          : Char := '\n'
  def verticalTab       : Char := '\x0B'
  def formFeed          : Char := '\x0C'
  def carriageReturn    : Char := '\r'
  def space             : Char := ' '
  def exclamation       : Char := '!'
  def doubleQuote       : Char := '"'
  def hash              : Char := '#'
  def dollar            : Char := '$'
  def percent           : Char := '%'
  def ampersand         : Char := '&'
  def singleQuote       : Char := '\''
  def openParen         : Char := '('
  def closeParen        : Char := ')'
  def asterisk          : Char := '*'
  def plus              : Char := '+'
  def comma             : Char := ','
  def minus             : Char := '-'
  def dot               : Char := '.'
  def slash             : Char := '/'
  def _0                : Char := '0'
  def _9                : Char := '9'
  def colon             : Char := ':'
  def semicolon         : Char := ';'
  def lessThan          : Char := '<'
  def equals            : Char := '='
  def greaterThan       : Char := '>'
  def question          : Char := '?'
  def at_               : Char := '@'
  def A                 : Char := 'A'
  def E                 : Char := 'E'
  def F                 : Char := 'F'
  def Z                 : Char := 'Z'
  def openBracket       : Char := '['
  def backslash         : Char := '\\'
  def closeBracket      : Char := ']'
  def caret             : Char := '^'
  def underscore        : Char := '_'
  def backtick          : Char := '`'
  def a                 : Char := 'a'
  def b                 : Char := 'b'
  def e                 : Char := 'e'
  def f                 : Char := 'f'
  def n                 : Char := 'n'
  def o                 : Char := 'o'
  def r                 : Char := 'r'
  def t                 : Char := 't'
  def u                 : Char := 'u'
  def v                 : Char := 'v'
  def x                 : Char := 'x'
  def z                 : Char := 'z'
  def openBrace         : Char := '{'
  def bar               : Char := '|'
  def closeBrace        : Char := '}'
  def tilde             : Char := '~'
  def maxAsciiChar      : Char := '\x7F'

  -- Unicode whitespace/line terminator code points
  def nonBreakingSpace     : Char := '\u00A0'
  def ogham                : Char := '\u1680'
  def enQuad               : Char := '\u2000'
  def hairSpace            : Char := '\u200A'
  def zeroWidthSpace       : Char := '\u200B'
  def narrowNoBreakSpace   : Char := '\u202F'
  def mathematicalSpace    : Char := '\u205F'
  def ideographicSpace     : Char := '\u3000'
  def byteOrderMark        : Char := '\uFEFF'
  def lineSeparator        : Char := '\u2028'
  def paragraphSeparator   : Char := '\u2029'
  def nextLine             : Char := '\u0085'
end CharCodes

/-- Is the character a decimal digit (0-9)? -/
@[inline] def isDigit (ch : Char) : Bool :=
  ch >= '0' && ch <= '9'

/-- Is the character an octal digit (0-7)? -/
@[inline] def isOctalDigit (ch : Char) : Bool :=
  ch >= '0' && ch <= '7'

/-- Is the character a hex digit (0-9, a-f, A-F)? -/
@[inline] def isHexDigit (ch : Char) : Bool :=
  (ch >= '0' && ch <= '9') || (ch >= 'a' && ch <= 'f') || (ch >= 'A' && ch <= 'F')

/-- Is the character a binary digit (0-1)? -/
@[inline] def isBinaryDigit (ch : Char) : Bool :=
  ch == '0' || ch == '1'

/-- Is the character a line break? -/
@[inline] def isLineBreak (ch : Char) : Bool :=
  ch == '\n' || ch == '\r' ||
  ch == CharCodes.lineSeparator || ch == CharCodes.paragraphSeparator

/-- Is the character whitespace (but not a line break)? -/
@[inline] def isWhiteSpaceSingleLine (ch : Char) : Bool :=
  ch == ' ' || ch == '\t' || ch == CharCodes.verticalTab || ch == CharCodes.formFeed ||
  ch == CharCodes.nonBreakingSpace || ch == CharCodes.ogham ||
  (ch >= CharCodes.enQuad && ch <= CharCodes.hairSpace) ||
  ch == CharCodes.zeroWidthSpace || ch == CharCodes.narrowNoBreakSpace ||
  ch == CharCodes.mathematicalSpace || ch == CharCodes.ideographicSpace ||
  ch == CharCodes.byteOrderMark || ch == CharCodes.nextLine

/-- Is the character any whitespace (including line breaks)? -/
@[inline] def isWhiteSpace (ch : Char) : Bool :=
  isWhiteSpaceSingleLine ch || isLineBreak ch

/-- Is the character an ASCII letter? -/
@[inline] def isASCIILetter (ch : Char) : Bool :=
  (ch >= 'a' && ch <= 'z') || (ch >= 'A' && ch <= 'Z')

/-- Can this character start an identifier?
    For now, covers ASCII + underscore + dollar. Unicode identifier support deferred. -/
@[inline] def isIdentifierStart (ch : Char) : Bool :=
  isASCIILetter ch || ch == '_' || ch == '$' || ch == '\\'  ||
  ch.val > 127  -- simplified: treat non-ASCII as potential identifier start

/-- Can this character continue an identifier?
    For now, covers ASCII letters, digits, underscore, dollar. Unicode deferred. -/
@[inline] def isIdentifierPart (ch : Char) : Bool :=
  isASCIILetter ch || isDigit ch || ch == '_' || ch == '$' || ch == '\\' ||
  ch == CharCodes.zeroWidthSpace ||
  ch.val > 127  -- simplified: treat non-ASCII as potential identifier part

/-- Convert a hex character to its numeric value (0-15). Returns 0 for invalid. -/
@[inline] def hexCharToValue (ch : Char) : UInt32 :=
  if ch >= '0' && ch <= '9' then ch.val - '0'.val
  else if ch >= 'a' && ch <= 'f' then ch.val - 'a'.val + 10
  else if ch >= 'A' && ch <= 'F' then ch.val - 'A'.val + 10
  else 0

end TSLean.Scanner
