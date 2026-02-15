/-
  TSLean.Compiler.Core — Foundational types for the TypeScript compiler.

  Based on Go: internal/core/text.go, languagevariant.go, scriptkind.go
-/

namespace TSLean.Compiler

/-- Based on Go: internal/core/text.go:5 (TextPos) -/
abbrev TextPos := Int32

/-- Based on Go: internal/core/text.go:9-12 (TextRange) -/
structure TextRange where
  pos : Int32
  end_ : Int32
  deriving BEq, Repr, Inhabited

namespace TextRange

/-- Based on Go: internal/core/text.go:14-16 (NewTextRange) -/
def mk' (pos : Int) (end_ : Int) : TextRange :=
  { pos := Int32.ofNat pos.toNat, end_ := Int32.ofNat end_.toNat }

/-- Based on Go: internal/core/text.go:18-20 (UndefinedTextRange) -/
def undefined : TextRange :=
  { pos := -1, end_ := -1 }

/-- Based on Go: internal/core/text.go:30-32 (Len) -/
def len (t : TextRange) : Int :=
  (t.end_ - t.pos).toInt

/-- Based on Go: internal/core/text.go:34-36 (IsValid) -/
def isValid (t : TextRange) : Bool :=
  t.pos >= 0 || t.end_ >= 0

/-- Based on Go: internal/core/text.go:38-40 (Contains) -/
def contains (t : TextRange) (pos : Int) : Bool :=
  pos >= t.pos.toInt && pos < t.end_.toInt

/-- Based on Go: internal/core/text.go:42-44 (ContainsInclusive) -/
def containsInclusive (t : TextRange) (pos : Int) : Bool :=
  pos >= t.pos.toInt && pos <= t.end_.toInt

end TextRange

/-- Based on Go: internal/core/languagevariant.go:8-11 (LanguageVariant) -/
inductive LanguageVariant where
  | standard
  | jsx
  deriving BEq, Repr, Inhabited

/-- Based on Go: internal/core/scriptkind.go:8-21 (ScriptKind) -/
inductive ScriptKind where
  | unknown
  | js
  | jsx
  | ts
  | tsx
  | external
  | json
  | deferred
  deriving BEq, Repr, Inhabited

end TSLean.Compiler
