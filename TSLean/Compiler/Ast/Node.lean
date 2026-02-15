/-
  TSLean.Compiler.Ast.Node — AST node types.

  Based on Go: internal/ast/ast.go (Node struct, nodeData interface, concrete node types)
  Lean approach: Inductive type with one constructor per node kind, named fields.
-/
import TSLean.Compiler.Core
import TSLean.Compiler.Ast.Kind
import TSLean.Compiler.Ast.NodeFlags

namespace TSLean.Compiler

/-- Base data shared by all AST nodes.
    Based on Go: internal/ast/ast.go (Node.Loc, Node.Flags) -/
structure NodeBase where
  loc : TextRange := TextRange.undefined
  flags : NodeFlags := NodeFlags.none
  deriving Repr

/-- AST node type — one constructor per node kind.
    Based on Go: internal/ast/ast.go (Node struct + concrete nodeData types)
    Minimal set covering the four target inputs. -/
inductive Node where
  -- Tokens (keyword/operator/punctuation used as AST nodes)
  -- Based on Go: ast.go — Token nodes created by factory.NewToken
  | token (base : NodeBase) (kind : Kind)
  -- Names
  -- Based on Go: ast.go — Identifier struct (Text field)
  | identifier (base : NodeBase) (text : String)
  -- Literals
  -- Based on Go: ast.go — NumericLiteral, StringLiteral structs
  | numericLiteral (base : NodeBase) (text : String)
  | stringLiteral (base : NodeBase) (text : String)
  -- Expressions
  -- Based on Go: ast.go — BinaryExpression struct (Left, OperatorToken, Right)
  | binaryExpression (base : NodeBase) (left : Node) (operatorToken : Node) (right : Node)
  -- Based on Go: ast.go — ParenthesizedExpression struct
  | parenthesizedExpression (base : NodeBase) (expression : Node)
  -- Based on Go: ast.go — PrefixUnaryExpression struct (Operator, Operand)
  | prefixUnaryExpression (base : NodeBase) (operator : Kind) (operand : Node)
  -- Based on Go: ast.go — PostfixUnaryExpression struct (Operand, Operator)
  | postfixUnaryExpression (base : NodeBase) (operand : Node) (operator : Kind)
  -- Based on Go: ast.go — PropertyAccessExpression struct
  | propertyAccessExpression (base : NodeBase) (expression : Node) (name : Node)
  -- Based on Go: ast.go — ElementAccessExpression struct
  | elementAccessExpression (base : NodeBase) (expression : Node) (argumentExpression : Node)
  -- Based on Go: ast.go — CallExpression struct
  | callExpression (base : NodeBase) (expression : Node) (arguments : Array Node)
  -- Statements
  -- Based on Go: ast.go — ExpressionStatement struct
  | expressionStatement (base : NodeBase) (expression : Node)
  -- Based on Go: ast.go — EmptyStatement struct
  | emptyStatement (base : NodeBase)
  -- Based on Go: ast.go — Block struct (Statements)
  | block (base : NodeBase) (statements : Array Node)
  -- Based on Go: ast.go — IfStatement struct (Expression, ThenStatement, ElseStatement)
  | ifStatement (base : NodeBase) (expression : Node) (thenStatement : Node)
      (elseStatement : Option Node)
  -- Based on Go: ast.go — ReturnStatement struct (Expression)
  | returnStatement (base : NodeBase) (expression : Option Node)
  -- Based on Go: ast.go — ThrowStatement struct
  | throwStatement (base : NodeBase) (expression : Option Node)
  -- Based on Go: ast.go — BreakStatement / ContinueStatement struct
  | breakStatement (base : NodeBase) (label : Option Node)
  | continueStatement (base : NodeBase) (label : Option Node)
  -- Based on Go: ast.go — DebuggerStatement struct
  | debuggerStatement (base : NodeBase)
  -- Based on Go: ast.go — WhileStatement struct
  | whileStatement (base : NodeBase) (expression : Node) (statement : Node)
  -- Based on Go: ast.go — DoStatement struct
  | doStatement (base : NodeBase) (statement : Node) (expression : Node)
  -- Based on Go: ast.go — ForStatement struct
  | forStatement (base : NodeBase) (initializer : Option Node)
      (condition : Option Node) (incrementor : Option Node) (statement : Node)
  -- Based on Go: ast.go — ForInStatement struct
  | forInStatement (base : NodeBase) (initializer : Option Node) (expression : Node)
      (statement : Node)
  -- Based on Go: ast.go — ForOfStatement struct
  | forOfStatement (base : NodeBase) (initializer : Option Node) (expression : Node)
      (statement : Node)
  -- Based on Go: ast.go — SwitchStatement struct
  | switchStatement (base : NodeBase) (expression : Node) (clauses : Array Node)
  -- Based on Go: ast.go — CaseClause / DefaultClause struct
  | caseClause (base : NodeBase) (expression : Node) (statements : Array Node)
  | defaultClause (base : NodeBase) (statements : Array Node)
  -- Based on Go: ast.go — TryStatement struct
  | tryStatement (base : NodeBase) (tryBlock : Node)
      (catchClause : Option Node) (finallyBlock : Option Node)
  -- Based on Go: ast.go — CatchClause struct
  | catchClause (base : NodeBase) (variableDeclaration : Option Node) (block : Node)
  -- Based on Go: ast.go — WithStatement struct
  | withStatement (base : NodeBase) (expression : Node) (statement : Node)
  -- Based on Go: ast.go — LabeledStatement struct
  | labeledStatement (base : NodeBase) (label : Node) (statement : Node)
  -- Based on Go: ast.go — VariableStatement struct (DeclarationList)
  | variableStatement (base : NodeBase) (declarationList : Node)
  -- Declarations
  -- Based on Go: ast.go — VariableDeclarationList struct (Flags, Declarations)
  | variableDeclarationList (base : NodeBase) (declFlags : NodeFlags)
      (declarations : Array Node)
  -- Based on Go: ast.go — VariableDeclaration struct (Name, Type, Initializer)
  | variableDeclaration (base : NodeBase) (name : Node) (typeNode : Option Node)
      (initializer : Option Node)
  -- Based on Go: ast.go — FunctionDeclaration struct
  | functionDeclaration (base : NodeBase) (name : Option Node)
      (typeParameters : Option (Array Node)) (parameters : Array Node)
      (returnType : Option Node) (body : Option Node)
  -- Based on Go: ast.go — ParameterDeclaration struct
  | parameterDeclaration (base : NodeBase) (dotDotDot : Option Node) (name : Node)
      (questionToken : Option Node) (typeNode : Option Node) (initializer : Option Node)
  -- Based on Go: ast.go — ClassDeclaration struct
  | classDeclaration (base : NodeBase) (name : Option Node)
      (typeParameters : Option (Array Node)) (heritageClauses : Option (Array Node))
      (members : Array Node)
  -- Based on Go: ast.go — MethodDeclaration struct
  | methodDeclaration (base : NodeBase) (name : Node) (questionToken : Option Node)
      (typeParameters : Option (Array Node)) (parameters : Array Node)
      (returnType : Option Node) (body : Option Node)
  -- Based on Go: ast.go — SemicolonClassElement
  | semicolonClassElement (base : NodeBase)
  -- Type nodes
  -- Based on Go: ast.go — TypeReference struct (TypeName, TypeArguments)
  | typeReference (base : NodeBase) (typeName : Node) (typeArguments : Option (Array Node))
  -- Top-level
  -- Based on Go: ast.go — SourceFile struct (Statements, EndOfFileToken)
  | sourceFile (base : NodeBase) (statements : Array Node) (endOfFileToken : Node)
  -- Error recovery
  | missing (base : NodeBase) (kind : Kind)
  deriving Repr

instance : Inhabited Node := ⟨Node.emptyStatement {}⟩

namespace Node

/-- Get the Kind for a node (derived from constructor).
    Based on Go: ast.go — Node.Kind field -/
def kind : Node → Kind
  | token _ k => k
  | identifier .. => Kind.identifier
  | numericLiteral .. => Kind.numericLiteral
  | stringLiteral .. => Kind.stringLiteral
  | binaryExpression .. => Kind.binaryExpression
  | parenthesizedExpression .. => Kind.parenthesizedExpression
  | prefixUnaryExpression .. => Kind.prefixUnaryExpression
  | postfixUnaryExpression .. => Kind.postfixUnaryExpression
  | propertyAccessExpression .. => Kind.propertyAccessExpression
  | elementAccessExpression .. => Kind.elementAccessExpression
  | callExpression .. => Kind.callExpression
  | expressionStatement .. => Kind.expressionStatement
  | emptyStatement .. => Kind.emptyStatement
  | block .. => Kind.block
  | ifStatement .. => Kind.ifStatement
  | returnStatement .. => Kind.returnStatement
  | throwStatement .. => Kind.throwStatement
  | breakStatement .. => Kind.breakStatement
  | continueStatement .. => Kind.continueStatement
  | debuggerStatement .. => Kind.debuggerStatement
  | whileStatement .. => Kind.whileStatement
  | doStatement .. => Kind.doStatement
  | forStatement .. => Kind.forStatement
  | forInStatement .. => Kind.forInStatement
  | forOfStatement .. => Kind.forOfStatement
  | switchStatement .. => Kind.switchStatement
  | caseClause .. => Kind.caseClause
  | defaultClause .. => Kind.defaultClause
  | tryStatement .. => Kind.tryStatement
  | catchClause .. => Kind.catchClause
  | withStatement .. => Kind.withStatement
  | labeledStatement .. => Kind.labeledStatement
  | variableStatement .. => Kind.variableStatement
  | variableDeclarationList .. => Kind.variableDeclarationList
  | variableDeclaration .. => Kind.variableDeclaration
  | functionDeclaration .. => Kind.functionDeclaration
  | parameterDeclaration .. => Kind.parameter
  | classDeclaration .. => Kind.classDeclaration
  | methodDeclaration .. => Kind.methodDeclaration
  | semicolonClassElement .. => Kind.semicolonClassElement
  | typeReference .. => Kind.typeReference
  | sourceFile .. => Kind.sourceFile
  | missing _ k => k

/-- Get the base data for a node. -/
def base : Node → NodeBase
  | token b _ => b
  | identifier b _ => b
  | numericLiteral b _ => b
  | stringLiteral b _ => b
  | binaryExpression b .. => b
  | parenthesizedExpression b _ => b
  | prefixUnaryExpression b .. => b
  | postfixUnaryExpression b .. => b
  | propertyAccessExpression b .. => b
  | elementAccessExpression b .. => b
  | callExpression b .. => b
  | expressionStatement b _ => b
  | emptyStatement b => b
  | block b _ => b
  | ifStatement b .. => b
  | returnStatement b _ => b
  | throwStatement b _ => b
  | breakStatement b _ => b
  | continueStatement b _ => b
  | debuggerStatement b => b
  | whileStatement b .. => b
  | doStatement b .. => b
  | forStatement b .. => b
  | forInStatement b .. => b
  | forOfStatement b .. => b
  | switchStatement b .. => b
  | caseClause b .. => b
  | defaultClause b .. => b
  | tryStatement b .. => b
  | catchClause b .. => b
  | withStatement b .. => b
  | labeledStatement b .. => b
  | variableStatement b _ => b
  | variableDeclarationList b .. => b
  | variableDeclaration b .. => b
  | functionDeclaration b .. => b
  | parameterDeclaration b .. => b
  | classDeclaration b .. => b
  | methodDeclaration b .. => b
  | semicolonClassElement b => b
  | typeReference b .. => b
  | sourceFile b .. => b
  | missing b _ => b

/-- Update the base data for a node. -/
def withBase : Node → NodeBase → Node
  | token _ k, b => token b k
  | identifier _ t, b => identifier b t
  | numericLiteral _ t, b => numericLiteral b t
  | stringLiteral _ t, b => stringLiteral b t
  | binaryExpression _ l o r, b => binaryExpression b l o r
  | parenthesizedExpression _ e, b => parenthesizedExpression b e
  | prefixUnaryExpression _ op e, b => prefixUnaryExpression b op e
  | postfixUnaryExpression _ e op, b => postfixUnaryExpression b e op
  | propertyAccessExpression _ e n, b => propertyAccessExpression b e n
  | elementAccessExpression _ e a, b => elementAccessExpression b e a
  | callExpression _ e a, b => callExpression b e a
  | expressionStatement _ e, b => expressionStatement b e
  | emptyStatement _, b => emptyStatement b
  | block _ s, b => block b s
  | ifStatement _ e t el, b => ifStatement b e t el
  | returnStatement _ e, b => returnStatement b e
  | throwStatement _ e, b => throwStatement b e
  | breakStatement _ l, b => breakStatement b l
  | continueStatement _ l, b => continueStatement b l
  | debuggerStatement _, b => debuggerStatement b
  | whileStatement _ e s, b => whileStatement b e s
  | doStatement _ s e, b => doStatement b s e
  | forStatement _ i c inc s, b => forStatement b i c inc s
  | forInStatement _ i e s, b => forInStatement b i e s
  | forOfStatement _ i e s, b => forOfStatement b i e s
  | switchStatement _ e c, b => switchStatement b e c
  | caseClause _ e s, b => caseClause b e s
  | defaultClause _ s, b => defaultClause b s
  | tryStatement _ tb cc fb, b => tryStatement b tb cc fb
  | catchClause _ v bl, b => catchClause b v bl
  | withStatement _ e s, b => withStatement b e s
  | labeledStatement _ l s, b => labeledStatement b l s
  | variableStatement _ d, b => variableStatement b d
  | variableDeclarationList _ f d, b => variableDeclarationList b f d
  | variableDeclaration _ n t i, b => variableDeclaration b n t i
  | functionDeclaration _ n tp p rt bd, b => functionDeclaration b n tp p rt bd
  | parameterDeclaration _ d n q t i, b => parameterDeclaration b d n q t i
  | classDeclaration _ n tp hc m, b => classDeclaration b n tp hc m
  | methodDeclaration _ n q tp p rt bd, b => methodDeclaration b n q tp p rt bd
  | semicolonClassElement _, b => semicolonClassElement b
  | typeReference _ tn ta, b => typeReference b tn ta
  | sourceFile _ s e, b => sourceFile b s e
  | missing _ k, b => missing b k

end Node

end TSLean.Compiler
