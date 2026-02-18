/-
  TSLean.Compiler.Ast.Precedence — Operator precedence for Pratt parsing.

  Based on Go: internal/ast/precedence.go (lines 7-368)
-/
import TSLean.Compiler.Ast.Kind

namespace TSLean.Compiler

/-- Based on Go: internal/ast/precedence.go:7 (OperatorPrecedence) -/
inductive OperatorPrecedence where
  | invalid     -- -1: lower than all, stops binary parsing
  | comma       -- 0
  | spread      -- 1
  | yield       -- 2
  | assignment  -- 3
  | conditional -- 4
  | logicalOR   -- 5
  | logicalAND  -- 6
  | bitwiseOR   -- 7
  | bitwiseXOR  -- 8
  | bitwiseAND  -- 9
  | equality    -- 10
  | relational  -- 11
  | shift       -- 12
  | additive    -- 13
  | multiplicative -- 14
  | exponentiation -- 15
  | unary       -- 16
  | update      -- 17
  | leftHandSide -- 18
  | optionalChain -- 19
  | member      -- 20
  | primary     -- 21
  | parentheses -- 22
  deriving BEq, Repr, Inhabited

namespace OperatorPrecedence

/-- Go: precedence.go:172 -/ def lowest := comma
/-- Go: precedence.go:173 -/ def highest := parentheses
/-- Go: precedence.go:174 -/ def disallowComma := yield
/-- Go: precedence.go:183 -/ def coalesce := logicalOR

def toInt : OperatorPrecedence → Int
  | invalid => -1
  | comma => 0
  | spread => 1
  | yield => 2
  | assignment => 3
  | conditional => 4
  | logicalOR => 5
  | logicalAND => 6
  | bitwiseOR => 7
  | bitwiseXOR => 8
  | bitwiseAND => 9
  | equality => 10
  | relational => 11
  | shift => 12
  | additive => 13
  | multiplicative => 14
  | exponentiation => 15
  | unary => 16
  | update => 17
  | leftHandSide => 18
  | optionalChain => 19
  | member => 20
  | primary => 21
  | parentheses => 22

instance : Ord OperatorPrecedence where
  compare a b := compare a.toInt b.toInt

instance : LT OperatorPrecedence where
  lt a b := a.toInt < b.toInt

instance : LE OperatorPrecedence where
  le a b := a.toInt ≤ b.toInt

end OperatorPrecedence

open Kind in
/-- Based on Go: internal/ast/precedence.go:337-368 (GetBinaryOperatorPrecedence) -/
def getBinaryOperatorPrecedence (kind : Kind) : OperatorPrecedence :=
  match kind with
  | .questionQuestionToken => OperatorPrecedence.coalesce
  | .barBarToken => OperatorPrecedence.logicalOR
  | .ampersandAmpersandToken => OperatorPrecedence.logicalAND
  | .barToken => OperatorPrecedence.bitwiseOR
  | .caretToken => OperatorPrecedence.bitwiseXOR
  | .ampersandToken => OperatorPrecedence.bitwiseAND
  | .equalsEqualsToken
  | .exclamationEqualsToken
  | .equalsEqualsEqualsToken
  | .exclamationEqualsEqualsToken => OperatorPrecedence.equality
  | .lessThanToken
  | .greaterThanToken
  | .lessThanEqualsToken
  | .greaterThanEqualsToken
  | .instanceOfKeyword
  | .inKeyword
  | .asKeyword
  | .satisfiesKeyword => OperatorPrecedence.relational
  | .lessThanLessThanToken
  | .greaterThanGreaterThanToken
  | .greaterThanGreaterThanGreaterThanToken => OperatorPrecedence.shift
  | .plusToken
  | .minusToken => OperatorPrecedence.additive
  | .asteriskToken
  | .slashToken
  | .percentToken => OperatorPrecedence.multiplicative
  | .asteriskAsteriskToken => OperatorPrecedence.exponentiation
  | _ => OperatorPrecedence.invalid

end TSLean.Compiler
