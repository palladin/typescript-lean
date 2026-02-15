/-
  TSLean.Compiler.Ast.TokenFlags — Token flags (bitfield).

  Based on Go: internal/ast/tokenflags.go (lines 1-31)
  Go type: ast.TokenFlags (int32)
-/

namespace TSLean.Compiler

/-- Based on Go: internal/ast/tokenflags.go:3 (TokenFlags) -/
structure TokenFlags where
  val : UInt32
  deriving BEq, Repr, Inhabited

namespace TokenFlags

/-- Go: tokenflags.go:6 -/ def none : TokenFlags := ⟨0⟩
/-- Go: tokenflags.go:7 -/ def precedingLineBreak : TokenFlags := ⟨(1 : UInt32) <<< (0 : UInt32)⟩
/-- Go: tokenflags.go:8 -/ def precedingJSDocComment : TokenFlags := ⟨(1 : UInt32) <<< (1 : UInt32)⟩
/-- Go: tokenflags.go:9 -/ def unterminated : TokenFlags := ⟨(1 : UInt32) <<< (2 : UInt32)⟩
/-- Go: tokenflags.go:10 -/ def extendedUnicodeEscape : TokenFlags := ⟨(1 : UInt32) <<< (3 : UInt32)⟩
/-- Go: tokenflags.go:11 -/ def scientific : TokenFlags := ⟨(1 : UInt32) <<< (4 : UInt32)⟩
/-- Go: tokenflags.go:12 -/ def octal : TokenFlags := ⟨(1 : UInt32) <<< (5 : UInt32)⟩
/-- Go: tokenflags.go:13 -/ def hexSpecifier : TokenFlags := ⟨(1 : UInt32) <<< (6 : UInt32)⟩
/-- Go: tokenflags.go:14 -/ def binarySpecifier : TokenFlags := ⟨(1 : UInt32) <<< (7 : UInt32)⟩
/-- Go: tokenflags.go:15 -/ def octalSpecifier : TokenFlags := ⟨(1 : UInt32) <<< (8 : UInt32)⟩
/-- Go: tokenflags.go:16 -/ def containsSeparator : TokenFlags := ⟨(1 : UInt32) <<< (9 : UInt32)⟩
/-- Go: tokenflags.go:17 -/ def unicodeEscape : TokenFlags := ⟨(1 : UInt32) <<< (10 : UInt32)⟩
/-- Go: tokenflags.go:18 -/ def containsInvalidEscape : TokenFlags := ⟨(1 : UInt32) <<< (11 : UInt32)⟩
/-- Go: tokenflags.go:19 -/ def hexEscape : TokenFlags := ⟨(1 : UInt32) <<< (12 : UInt32)⟩
/-- Go: tokenflags.go:20 -/ def containsLeadingZero : TokenFlags := ⟨(1 : UInt32) <<< (13 : UInt32)⟩
/-- Go: tokenflags.go:21 -/ def containsInvalidSeparator : TokenFlags := ⟨(1 : UInt32) <<< (14 : UInt32)⟩
/-- Go: tokenflags.go:22 -/ def precedingJSDocLeadingAsterisks : TokenFlags := ⟨(1 : UInt32) <<< (15 : UInt32)⟩
/-- Go: tokenflags.go:23 -/ def singleQuote : TokenFlags := ⟨(1 : UInt32) <<< (16 : UInt32)⟩

-- Composite flags (Go: tokenflags.go:24-30)
/-- Go: tokenflags.go:24 -/ def binaryOrOctalSpecifier : TokenFlags :=
  ⟨binarySpecifier.val ||| octalSpecifier.val⟩
/-- Go: tokenflags.go:25 -/ def withSpecifier : TokenFlags :=
  ⟨hexSpecifier.val ||| binaryOrOctalSpecifier.val⟩
/-- Go: tokenflags.go:26 -/ def stringLiteralFlags : TokenFlags :=
  ⟨unterminated.val ||| hexEscape.val ||| unicodeEscape.val ||| extendedUnicodeEscape.val ||| containsInvalidEscape.val ||| singleQuote.val⟩
/-- Go: tokenflags.go:27 -/ def numericLiteralFlags : TokenFlags :=
  ⟨scientific.val ||| octal.val ||| containsLeadingZero.val ||| withSpecifier.val ||| containsSeparator.val ||| containsInvalidSeparator.val⟩
/-- Go: tokenflags.go:28 -/ def templateLiteralLikeFlags : TokenFlags :=
  ⟨unterminated.val ||| hexEscape.val ||| unicodeEscape.val ||| extendedUnicodeEscape.val ||| containsInvalidEscape.val⟩
/-- Go: tokenflags.go:29 -/ def regularExpressionLiteralFlags : TokenFlags :=
  unterminated
/-- Go: tokenflags.go:30 -/ def isInvalid : TokenFlags :=
  ⟨octal.val ||| containsLeadingZero.val ||| containsInvalidSeparator.val ||| containsInvalidEscape.val⟩

-- Bitwise operations
def or (a b : TokenFlags) : TokenFlags := ⟨a.val ||| b.val⟩
def and (a b : TokenFlags) : TokenFlags := ⟨a.val &&& b.val⟩
def has (flags flag : TokenFlags) : Bool := (flags.val &&& flag.val) != 0

instance : OrOp TokenFlags where
  or := TokenFlags.or

instance : AndOp TokenFlags where
  and := TokenFlags.and

end TokenFlags

end TSLean.Compiler
