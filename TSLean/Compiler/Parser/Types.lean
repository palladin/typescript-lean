/-
  TSLean.Compiler.Parser.Types — Parser types and state.

  Based on Go: internal/parser/parser.go (lines 17-89, 258-269)
-/
import TSLean.Compiler.Core
import TSLean.Compiler.Ast.Kind
import TSLean.Compiler.Ast.NodeFlags
import TSLean.Compiler.Ast.Node
import TSLean.Compiler.Diagnostics
import TSLean.Compiler.Scanner.Scanner
import Std.Data.HashMap

open Std

namespace TSLean.Compiler

/-- Based on Go: internal/parser/parser.go:17-47 (ParsingContext) -/
inductive ParsingContext where
  | sourceElements            -- 0: Elements in source file
  | blockStatements           -- 1: Statements in block
  | switchClauses             -- 2: Clauses in switch statement
  | switchClauseStatements    -- 3: Statements in switch clause
  | typeMembers               -- 4: Members in interface or type literal
  | classMembers              -- 5: Members in class declaration
  | enumMembers               -- 6: Members in enum declaration
  | heritageClauseElement     -- 7: Elements in a heritage clause
  | variableDeclarations      -- 8: Variable declarations
  | objectBindingElements     -- 9: Binding elements in object binding
  | arrayBindingElements      -- 10: Binding elements in array binding
  | argumentExpressions       -- 11: Expressions in argument list
  | objectLiteralMembers      -- 12: Members in object literal
  | jsxAttributes             -- 13
  | jsxChildren               -- 14
  | arrayLiteralMembers       -- 15: Members in array literal
  | parameters                -- 16: Parameters in parameter list
  | jsDocParameters           -- 17
  | restProperties            -- 18
  | typeParameters            -- 19: Type parameters
  | typeArguments             -- 20: Type arguments
  | tupleElementTypes         -- 21
  | heritageClauses           -- 22
  | importOrExportSpecifiers  -- 23
  | importAttributes          -- 24
  | jsDocComment              -- 25
  deriving BEq, Repr, Inhabited

namespace ParsingContext

def toNat : ParsingContext → Nat
  | sourceElements => 0
  | blockStatements => 1
  | switchClauses => 2
  | switchClauseStatements => 3
  | typeMembers => 4
  | classMembers => 5
  | enumMembers => 6
  | heritageClauseElement => 7
  | variableDeclarations => 8
  | objectBindingElements => 9
  | arrayBindingElements => 10
  | argumentExpressions => 11
  | objectLiteralMembers => 12
  | jsxAttributes => 13
  | jsxChildren => 14
  | arrayLiteralMembers => 15
  | parameters => 16
  | jsDocParameters => 17
  | restProperties => 18
  | typeParameters => 19
  | typeArguments => 20
  | tupleElementTypes => 21
  | heritageClauses => 22
  | importOrExportSpecifiers => 23
  | importAttributes => 24
  | jsDocComment => 25

/-- Go: parser.go:46 -/
def count : Nat := 26

end ParsingContext

-- Inhabited instances needed for partial mutual recursion in Parser.lean
instance : Inhabited ScannerState := ⟨{}⟩
instance : Inhabited Scanner := ⟨{}⟩

/-- Based on Go: internal/parser/parser.go:51-89 (Parser)
    Main parser struct. -/
structure Parser where
  scanner : Scanner
  sourceText : String
  token : Kind := Kind.unknown
  contextFlags : NodeFlags := NodeFlags.none
  parsingContexts : UInt32 := 0
  hasParseError : Bool := false
  diagnostics : Array Diagnostic := #[]
  identifiers : HashMap String String := HashMap.ofList []
  identifierCount : Nat := 0
  /-- Global recursion budget shared by parser.
      Decremented by `loop` on every recursive call.
      When zero, recursion stops and default values are returned. -/
  fuel : Nat
  /-- Enable debug tracing (false by default for performance). -/
  debug : Bool := false
  /-- Collected trace messages when debug is enabled. -/
  traceLog : Array String := #[]

instance : Inhabited Parser := ⟨{ scanner := default, sourceText := "", fuel := 0 }⟩

/-- Parsing halts immediately when fuel is exhausted. -/
inductive ParseError where
  | fuelExhausted
  deriving Repr

/-- Parser monad — ExceptT over StateM for fuel-exhaustion-as-exception.
    When fuel reaches zero, `loop` throws `fuelExhausted` which
    propagates through every `do` block automatically. -/
abbrev ParserM (α : Type) := ExceptT ParseError (StateM Parser) α

/-- Result of parsing a source file.
    Based on Go: parser.go — ParseSourceFile returns (SourceFile, diagnostics) -/
structure ParseResult where
  sourceFile : Node
  diagnostics : Array Diagnostic
  fuelExhausted : Bool := false

end TSLean.Compiler
