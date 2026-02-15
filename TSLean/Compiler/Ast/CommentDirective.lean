/-
  TSLean.Compiler.Ast.CommentDirective — Comment directive types.

  Based on Go: internal/ast/ast.go (lines 10884-10895)
-/
import TSLean.Compiler.Core

namespace TSLean.Compiler

/-- Based on Go: internal/ast/ast.go:10884 (CommentDirectiveKind) -/
inductive CommentDirectiveKind where
  | unknown
  | expectError
  | ignore
  deriving BEq, Repr, Inhabited

/-- Based on Go: internal/ast/ast.go:10892 (CommentDirective) -/
structure CommentDirective where
  loc : TextRange
  kind : CommentDirectiveKind
  deriving BEq, Repr, Inhabited

end TSLean.Compiler
