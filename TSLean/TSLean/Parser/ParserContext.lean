-- TSLean.Parser.ParserContext: Parsing context flags.
-- These flags track the syntactic context during recursive descent parsing,
-- controlling how ambiguous constructs are resolved.

import TSLean.Ast.SyntaxKind

namespace TSLean.Parser

open TSLean.Ast

/-- Parsing context flags control disambiguation in the recursive descent parser.
    For example, `inYieldContext` affects whether `yield` is parsed as an expression
    or an identifier. -/
structure ParsingContext where
  val : UInt32
  deriving BEq, Repr, Inhabited

namespace ParsingContext
  instance : OrOp ParsingContext where or a b := ⟨a.val ||| b.val⟩
  instance : AndOp ParsingContext where and a b := ⟨a.val &&& b.val⟩
  def hasFlag (flags flag : ParsingContext) : Bool := (flags.val &&& flag.val) != 0

  def none                    : ParsingContext := ⟨0⟩
  def sourceElements          : ParsingContext := ⟨0x1⟩
  def blockStatements         : ParsingContext := ⟨0x2⟩
  def switchClauses           : ParsingContext := ⟨0x4⟩
  def switchClauseStatements  : ParsingContext := ⟨0x8⟩
  def typeMembers             : ParsingContext := ⟨0x10⟩
  def classMembers            : ParsingContext := ⟨0x20⟩
  def enumMembers             : ParsingContext := ⟨0x40⟩
  def heritageClauseElement   : ParsingContext := ⟨0x80⟩
  def variableDeclarations    : ParsingContext := ⟨0x100⟩
  def objectBindingElements   : ParsingContext := ⟨0x200⟩
  def arrayBindingElements    : ParsingContext := ⟨0x400⟩
  def argumentExpressions     : ParsingContext := ⟨0x800⟩
  def objectLiteralMembers    : ParsingContext := ⟨0x1000⟩
  def jsxAttributes           : ParsingContext := ⟨0x2000⟩
  def jsxChildren             : ParsingContext := ⟨0x4000⟩
  def arrayLiteralMembers     : ParsingContext := ⟨0x8000⟩
  def parameters              : ParsingContext := ⟨0x10000⟩
  def jsDocParameters         : ParsingContext := ⟨0x20000⟩
  def restProperties          : ParsingContext := ⟨0x40000⟩
  def typeParameters          : ParsingContext := ⟨0x80000⟩
  def typeArguments           : ParsingContext := ⟨0x100000⟩
  def tupleElementTypes       : ParsingContext := ⟨0x200000⟩
  def heritageClauses         : ParsingContext := ⟨0x400000⟩
  def importOrExportSpecifiers : ParsingContext := ⟨0x800000⟩
  def importAttributes        : ParsingContext := ⟨0x1000000⟩
end ParsingContext

/-- Binary operator precedence levels for Pratt parsing. -/
inductive Precedence where
  | comma             -- 0
  | spread            -- 1
  | yield             -- 2
  | assignment        -- 3
  | conditional       -- 4
  | coalesce          -- 5
  | logicalOr         -- 6
  | logicalAnd        -- 7
  | bitwiseOr         -- 8
  | bitwiseXor        -- 9
  | bitwiseAnd        -- 10
  | equality          -- 11
  | relational        -- 12
  | shift             -- 13
  | additive          -- 14
  | multiplicative    -- 15
  | exponentiation    -- 16
  | unary             -- 17
  | update            -- 18
  | leftHandSide      -- 19
  | member            -- 20
  | primary           -- 21
  | highest           -- 22
  deriving BEq, Repr, Inhabited, Ord

/-- Get the numeric precedence value for comparison. -/
def Precedence.toNat : Precedence → Nat
  | .comma          => 0
  | .spread         => 1
  | .yield          => 2
  | .assignment     => 3
  | .conditional    => 4
  | .coalesce       => 5
  | .logicalOr      => 6
  | .logicalAnd     => 7
  | .bitwiseOr      => 8
  | .bitwiseXor     => 9
  | .bitwiseAnd     => 10
  | .equality       => 11
  | .relational     => 12
  | .shift          => 13
  | .additive       => 14
  | .multiplicative => 15
  | .exponentiation => 16
  | .unary          => 17
  | .update         => 18
  | .leftHandSide   => 19
  | .member         => 20
  | .primary        => 21
  | .highest        => 22

instance : LT Precedence where
  lt a b := a.toNat < b.toNat

instance : LE Precedence where
  le a b := a.toNat ≤ b.toNat

instance (a b : Precedence) : Decidable (a < b) := Nat.decLt a.toNat b.toNat
instance (a b : Precedence) : Decidable (a ≤ b) := Nat.decLe a.toNat b.toNat

/-- Get the binary operator precedence for a given token. -/
def getBinaryOperatorPrecedence (token : SyntaxKind) : Precedence :=
  match token with
  | .barBarToken             => .logicalOr
  | .ampersandAmpersandToken => .logicalAnd
  | .barToken                => .bitwiseOr
  | .caretToken              => .bitwiseXor
  | .ampersandToken          => .bitwiseAnd
  | .equalsEqualsToken       => .equality
  | .exclamationEqualsToken  => .equality
  | .equalsEqualsEqualsToken => .equality
  | .exclamationEqualsEqualsToken => .equality
  | .lessThanToken           => .relational
  | .greaterThanToken        => .relational
  | .lessThanEqualsToken     => .relational
  | .greaterThanEqualsToken  => .relational
  | .instanceOfKeyword       => .relational
  | .inKeyword               => .relational
  | .asKeyword               => .relational
  | .satisfiesKeyword        => .relational
  | .lessThanLessThanToken   => .shift
  | .greaterThanGreaterThanToken => .shift
  | .greaterThanGreaterThanGreaterThanToken => .shift
  | .plusToken                => .additive
  | .minusToken              => .additive
  | .asteriskToken           => .multiplicative
  | .slashToken              => .multiplicative
  | .percentToken            => .multiplicative
  | .asteriskAsteriskToken   => .exponentiation
  | .questionQuestionToken   => .coalesce
  | _                        => .comma

end TSLean.Parser
