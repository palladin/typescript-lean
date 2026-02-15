/-
  TSLean.Compiler.Ast.JSDocParsingMode — JSDoc parsing mode enum.

  Based on Go: internal/ast/parseoptions.go (lines 8-15)
-/

namespace TSLean.Compiler

/-- Based on Go: internal/ast/parseoptions.go:8 (JSDocParsingMode) -/
inductive JSDocParsingMode where
  | parseAll
  | parseNone
  | parseForTypeErrors
  | parseForTypeInfo
  deriving BEq, Repr, Inhabited

end TSLean.Compiler
