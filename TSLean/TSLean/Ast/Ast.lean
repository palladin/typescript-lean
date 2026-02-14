-- TSLean.Ast.Ast: Core AST types
-- Uses a single `Node` inductive to avoid mutual recursion limits.
-- Type-safe accessors and category predicates provide compile-time guidance.
-- This approach mirrors how TypeScript itself uses a single Node type with SyntaxKind discrimination.

import TSLean.Ast.SyntaxKind
import TSLean.Ast.NodeData

namespace TSLean.Ast

/-- A modifier keyword (public, private, static, async, etc.). -/
structure Modifier where
  data : NodeData
  kind : SyntaxKind
  deriving Inhabited, BEq, Repr

set_option maxHeartbeats 800000 in
set_option genInjectivity false in
/-- The core AST node type. All AST nodes are constructors of this single inductive.
    Children are `Node` references. Category safety is enforced by convention and
    helper predicates (isExpression, isStatement, etc.).

    This is necessary because Lean 4's kernel check for mutual inductive types
    is inherently quadratic (see leanprover/lean4#6820), making large mutual
    blocks with 30+ types impractical. -/
inductive Node where
  -- Expression nodes
  | identifier (data : NodeData) (escapedText : String)
  | numericLiteral (data : NodeData) (text : String)
  | stringLiteral (data : NodeData) (text : String) (singleQuote : Bool)
  | regexpLiteral (data : NodeData) (text : String)
  | noSubstitutionTemplate (data : NodeData) (text : String)
  | templateExpression (data : NodeData) (head : Node) (templateSpans : Array Node)
  | arrayLiteral (data : NodeData) (elements : Array Node)
  | objectLiteral (data : NodeData) (properties : Array Node)
  | propertyAccess (data : NodeData) (expression : Node) (name : Node)
  | elementAccess (data : NodeData) (expression : Node) (argumentExpression : Node)
  | call (data : NodeData) (expression : Node)
      (typeArguments : Option (Array Node)) (arguments : Array Node)
  | new_ (data : NodeData) (expression : Node)
      (typeArguments : Option (Array Node)) (arguments : Option (Array Node))
  | taggedTemplate (data : NodeData) (tag : Node)
      (typeArguments : Option (Array Node)) (template : Node)
  | typeAssertion (data : NodeData) (type_ : Node) (expression : Node)
  | parenthesized (data : NodeData) (expression : Node)
  | functionExpr (data : NodeData) (modifiers : Array Modifier)
      (asteriskToken : Bool) (name : Option Node)
      (typeParameters : Option (Array Node)) (parameters : Array Node)
      (type_ : Option Node) (body : Option Node)
  | arrowFunction (data : NodeData) (modifiers : Array Modifier)
      (typeParameters : Option (Array Node)) (parameters : Array Node)
      (type_ : Option Node) (equalsGreaterThanToken : NodeData) (body : Node)
  | delete_ (data : NodeData) (expression : Node)
  | typeof_ (data : NodeData) (expression : Node)
  | void_ (data : NodeData) (expression : Node)
  | await_ (data : NodeData) (expression : Node)
  | prefixUnary (data : NodeData) (operator : SyntaxKind) (operand : Node)
  | postfixUnary (data : NodeData) (operand : Node) (operator : SyntaxKind)
  | binary (data : NodeData) (left : Node) (operatorToken : SyntaxKind) (right : Node)
  | conditional (data : NodeData) (condition : Node) (whenTrue : Node) (whenFalse : Node)
  | yield_ (data : NodeData) (asteriskToken : Bool) (expression : Option Node)
  | spread (data : NodeData) (expression : Node)
  | classExpr (data : NodeData) (modifiers : Array Modifier)
      (name : Option Node) (typeParameters : Option (Array Node))
      (heritageClauses : Array Node) (members : Array Node)
  | asExpr (data : NodeData) (expression : Node) (type_ : Node)
  | satisfiesExpr (data : NodeData) (expression : Node) (type_ : Node)
  | nonNullAssertion (data : NodeData) (expression : Node)
  | metaProperty (data : NodeData) (keywordToken : SyntaxKind) (name : Node)
  | expressionWithTypeArguments (data : NodeData) (expression : Node)
      (typeArguments : Option (Array Node))
  -- Keyword expressions
  | trueKeyword (data : NodeData)
  | falseKeyword (data : NodeData)
  | nullKeyword (data : NodeData)
  | thisKeyword (data : NodeData)
  | superKeyword (data : NodeData)
  -- JSX expressions
  | jsxElement (data : NodeData) (openingElement : Node)
      (children : Array Node) (closingElement : Node)
  | jsxSelfClosingElement (data : NodeData) (tagName : Node)
      (typeArguments : Option (Array Node)) (attributes : Node)
  | jsxFragment (data : NodeData) (children : Array Node)
  | jsxOpeningElement (data : NodeData) (tagName : Node)
      (typeArguments : Option (Array Node)) (attributes : Node)
  | jsxClosingElement (data : NodeData) (tagName : Node)
  | jsxText (data : NodeData) (text : String) (containsOnlyTriviaWhiteSpaces : Bool)
  | jsxExpression (data : NodeData) (dotDotDotToken : Bool) (expression : Option Node)
  | jsxAttribute (data : NodeData) (name : Node) (initializer : Option Node)
  | jsxSpreadAttribute (data : NodeData) (expression : Node)
  | jsxAttributes (data : NodeData) (properties : Array Node)
  -- Misc expression
  | omitted (data : NodeData)
  | comma (data : NodeData) (elements : Array Node)
  | partiallyEmitted (data : NodeData) (expression : Node)
  | syntheticExpression (data : NodeData)
  -- TypeNode nodes
  | typeReference (data : NodeData) (typeName : Node) (typeArguments : Option (Array Node))
  | functionType (data : NodeData)
      (typeParameters : Option (Array Node)) (parameters : Array Node) (type_ : Node)
  | constructorType (data : NodeData) (modifiers : Array Modifier)
      (typeParameters : Option (Array Node)) (parameters : Array Node) (type_ : Node)
  | typeQuery (data : NodeData) (exprName : Node) (typeArguments : Option (Array Node))
  | typeLiteral (data : NodeData) (members : Array Node)
  | arrayType (data : NodeData) (elementType : Node)
  | tupleType (data : NodeData) (elements : Array Node)
  | optionalType (data : NodeData) (type_ : Node)
  | restType (data : NodeData) (type_ : Node)
  | unionType (data : NodeData) (types : Array Node)
  | intersectionType (data : NodeData) (types : Array Node)
  | conditionalType (data : NodeData) (checkType : Node)
      (extendsType : Node) (trueType : Node) (falseType : Node)
  | inferType (data : NodeData) (typeParameter : Node)
  | parenthesizedType (data : NodeData) (type_ : Node)
  | thisType (data : NodeData)
  | typeOperator (data : NodeData) (operator : SyntaxKind) (type_ : Node)
  | indexedAccessType (data : NodeData) (objectType : Node) (indexType : Node)
  | mappedType (data : NodeData) (readonlyToken : Option SyntaxKind)
      (typeParameter : Node) (nameType : Option Node)
      (questionToken : Option SyntaxKind) (type_ : Option Node)
  | literalType (data : NodeData) (literal : Node)
  | namedTupleMember (data : NodeData) (dotDotDotToken : Bool)
      (name : Node) (questionToken : Bool) (type_ : Node)
  | templateLiteralType (data : NodeData) (head : Node) (templateSpans : Array Node)
  | importType (data : NodeData) (isTypeOf : Bool) (argument : Node)
      (attributes : Option Node) (qualifier : Option Node) (typeArguments : Option (Array Node))
  | typePredicate (data : NodeData) (assertsModifier : Bool)
      (parameterName : Node) (type_ : Option Node)
  -- Keyword types
  | anyKeyword (data : NodeData)
  | unknownKeyword (data : NodeData)
  | stringKeyword (data : NodeData)
  | numberKeyword (data : NodeData)
  | booleanKeyword (data : NodeData)
  | bigIntKeyword (data : NodeData)
  | symbolKeyword (data : NodeData)
  | objectKeyword (data : NodeData)
  | voidKeyword (data : NodeData)
  | undefinedKeyword (data : NodeData)
  | neverKeyword (data : NodeData)
  | intrinsicKeyword (data : NodeData)
  -- Statement nodes
  | block (data : NodeData) (statements : Array Node)
  | emptyStatement (data : NodeData)
  | variableStatement (data : NodeData) (modifiers : Array Modifier)
      (declarationList : Node)
  | expressionStatement (data : NodeData) (expression : Node)
  | ifStatement (data : NodeData) (expression : Node)
      (thenStatement : Node) (elseStatement : Option Node)
  | doStatement (data : NodeData) (statement : Node) (expression : Node)
  | whileStatement (data : NodeData) (expression : Node) (statement : Node)
  | forStatement (data : NodeData) (initializer : Option Node)
      (condition : Option Node) (incrementor : Option Node) (statement : Node)
  | forInStatement (data : NodeData) (initializer : Node)
      (expression : Node) (statement : Node)
  | forOfStatement (data : NodeData) (awaitModifier : Bool) (initializer : Node)
      (expression : Node) (statement : Node)
  | continueStatement (data : NodeData) (label : Option Node)
  | breakStatement (data : NodeData) (label : Option Node)
  | returnStatement (data : NodeData) (expression : Option Node)
  | withStatement (data : NodeData) (expression : Node) (statement : Node)
  | switchStatement (data : NodeData) (expression : Node) (caseBlock : Node)
  | labeledStatement (data : NodeData) (label : Node) (statement : Node)
  | throwStatement (data : NodeData) (expression : Node)
  | tryStatement (data : NodeData) (tryBlock : Node)
      (catchClause : Option Node) (finallyBlock : Option Node)
  | debuggerStatement (data : NodeData)
  | notEmittedStatement (data : NodeData)
  -- Declaration nodes
  | variableDeclaration (data : NodeData) (name : Node)
      (exclamationToken : Bool) (type_ : Option Node) (initializer : Option Node)
  | variableDeclarationList (data : NodeData) (declarations : Array Node)
  | functionDeclaration (data : NodeData) (modifiers : Array Modifier)
      (asteriskToken : Bool) (name : Option Node)
      (typeParameters : Option (Array Node)) (parameters : Array Node)
      (type_ : Option Node) (body : Option Node)
  | classDeclaration (data : NodeData) (modifiers : Array Modifier)
      (name : Option Node) (typeParameters : Option (Array Node))
      (heritageClauses : Array Node) (members : Array Node)
  | interfaceDeclaration (data : NodeData) (modifiers : Array Modifier)
      (name : Node) (typeParameters : Option (Array Node))
      (heritageClauses : Array Node) (members : Array Node)
  | typeAliasDeclaration (data : NodeData) (modifiers : Array Modifier)
      (name : Node) (typeParameters : Option (Array Node)) (type_ : Node)
  | enumDeclaration (data : NodeData) (modifiers : Array Modifier)
      (name : Node) (members : Array Node)
  | moduleDeclaration (data : NodeData) (modifiers : Array Modifier)
      (name : Node) (body : Option Node)
  | importDeclaration (data : NodeData) (modifiers : Array Modifier)
      (importClause : Option Node) (moduleSpecifier : Node)
      (attributes : Option Node)
  | exportDeclaration (data : NodeData) (modifiers : Array Modifier)
      (isTypeOnly : Bool) (exportClause : Option Node)
      (moduleSpecifier : Option Node) (attributes : Option Node)
  | exportAssignment (data : NodeData) (modifiers : Array Modifier)
      (isExportEquals : Bool) (expression : Node)
  | namespaceExportDeclaration (data : NodeData) (name : Node)
  | importEqualsDeclaration (data : NodeData) (modifiers : Array Modifier)
      (isTypeOnly : Bool) (name : Node) (moduleReference : Node)
  | missingDeclaration (data : NodeData)
  -- Supporting nodes
  | qualifiedName (data : NodeData) (left : Node) (right : Node)
  | computedPropertyName (data : NodeData) (expression : Node)
  | privateIdentifier (data : NodeData) (escapedText : String)
  | typeParameter (data : NodeData) (name : Node)
      (constraint : Option Node) (default_ : Option Node)
  | parameter (data : NodeData) (modifiers : Array Modifier)
      (dotDotDotToken : Bool) (name : Node) (questionToken : Bool)
      (type_ : Option Node) (initializer : Option Node)
  | decorator (data : NodeData) (expression : Node)
  -- Binding patterns
  | objectBindingPattern (data : NodeData) (elements : Array Node)
  | arrayBindingPattern (data : NodeData) (elements : Array Node)
  | bindingElement (data : NodeData) (dotDotDotToken : Bool)
      (propertyName : Option Node) (name : Node) (initializer : Option Node)
  -- Object literal members
  | propertyAssignment (data : NodeData) (name : Node)
      (questionToken : Bool) (initializer : Node)
  | shorthandPropertyAssignment (data : NodeData) (name : Node)
      (objectAssignmentInitializer : Option Node)
  | spreadAssignment (data : NodeData) (expression : Node)
  -- Class members
  | propertyDeclaration (data : NodeData) (modifiers : Array Modifier) (name : Node)
      (questionToken : Bool) (exclamationToken : Bool)
      (type_ : Option Node) (initializer : Option Node)
  | methodDeclaration (data : NodeData) (modifiers : Array Modifier) (asteriskToken : Bool)
      (name : Node) (questionToken : Bool)
      (typeParameters : Option (Array Node)) (parameters : Array Node)
      (type_ : Option Node) (body : Option Node)
  | constructor_ (data : NodeData) (modifiers : Array Modifier)
      (parameters : Array Node) (body : Option Node)
  | getAccessor (data : NodeData) (modifiers : Array Modifier) (name : Node)
      (parameters : Array Node) (type_ : Option Node) (body : Option Node)
  | setAccessor (data : NodeData) (modifiers : Array Modifier) (name : Node)
      (parameters : Array Node) (body : Option Node)
  | classStaticBlockDeclaration (data : NodeData) (body : Node)
  | semicolonClassElement (data : NodeData)
  -- Type members (signatures)
  | propertySignature (data : NodeData) (modifiers : Array Modifier)
      (name : Node) (questionToken : Bool) (type_ : Option Node)
  | callSignature (data : NodeData) (typeParameters : Option (Array Node))
      (parameters : Array Node) (type_ : Option Node)
  | constructSignature (data : NodeData) (typeParameters : Option (Array Node))
      (parameters : Array Node) (type_ : Option Node)
  | indexSignature (data : NodeData) (modifiers : Array Modifier)
      (parameters : Array Node) (type_ : Option Node)
  | methodSignature (data : NodeData) (name : Node) (questionToken : Bool)
      (typeParameters : Option (Array Node)) (parameters : Array Node)
      (type_ : Option Node)
  -- Template spans
  | templateSpan (data : NodeData) (expression : Node) (literal : Node)
  | templateLiteralTypeSpan (data : NodeData) (type_ : Node) (literal : Node)
  -- Clauses
  | caseBlock (data : NodeData) (clauses : Array Node)
  | caseClause (data : NodeData) (expression : Node) (statements : Array Node)
  | defaultClause (data : NodeData) (statements : Array Node)
  | heritageClause (data : NodeData) (token : SyntaxKind) (types : Array Node)
  | catchClause (data : NodeData) (variableDeclaration : Option Node) (block : Node)
  -- Import/export
  | importClause (data : NodeData) (isTypeOnly : Bool)
      (name : Option Node) (namedBindings : Option Node)
  | namespaceImport (data : NodeData) (name : Node)
  | namedImports (data : NodeData) (elements : Array Node)
  | importSpecifier (data : NodeData) (isTypeOnly : Bool)
      (propertyName : Option Node) (name : Node)
  | namespaceExport (data : NodeData) (name : Node)
  | namedExports (data : NodeData) (elements : Array Node)
  | exportSpecifier (data : NodeData) (isTypeOnly : Bool)
      (propertyName : Option Node) (name : Node)
  | externalModuleReference (data : NodeData) (expression : Node)
  | importAttributes (data : NodeData) (token : SyntaxKind) (elements : Array Node)
  | importAttribute (data : NodeData) (name : Node) (value : Node)
  -- Enum
  | enumMember (data : NodeData) (name : Node) (initializer : Option Node)
  -- Module
  | moduleBlock (data : NodeData) (statements : Array Node)
  -- Source file
  | sourceFile (data : NodeData) (fileName : String)
      (statements : Array Node) (endOfFileToken : NodeData)
      (isDeclarationFile : Bool)
  -- JSDoc (abbreviated for now)
  | jsDoc (data : NodeData) (comment : Option String) (tags : Array Node)
  | jsDocTag (data : NodeData) (tagName : Node) (comment : Option String)
  | jsDocParameterTag (data : NodeData) (tagName : Node)
      (name : Node) (isBracketed : Bool) (typeExpression : Option Node)
  | jsDocReturnTag (data : NodeData) (tagName : Node) (typeExpression : Option Node)
  | jsDocTypeTag (data : NodeData) (tagName : Node) (typeExpression : Node)
  | jsDocTypeExpression (data : NodeData) (type_ : Node)
  -- Token placeholder for generic tokens
  | token (data : NodeData) (kind : SyntaxKind)
  deriving Inhabited

namespace Node

/-- Extract NodeData from any Node. -/
def getData : Node → NodeData
  | identifier d _ | numericLiteral d _ | stringLiteral d _ _ | regexpLiteral d _
  | noSubstitutionTemplate d _ | templateExpression d _ _ | arrayLiteral d _
  | objectLiteral d _ | propertyAccess d _ _ | elementAccess d _ _
  | call d _ _ _ | new_ d _ _ _ | taggedTemplate d _ _ _ | typeAssertion d _ _
  | parenthesized d _ | functionExpr d _ _ _ _ _ _ _ | arrowFunction d _ _ _ _ _ _
  | delete_ d _ | typeof_ d _ | void_ d _ | await_ d _
  | prefixUnary d _ _ | postfixUnary d _ _ | binary d _ _ _ | conditional d _ _ _
  | yield_ d _ _ | spread d _ | classExpr d _ _ _ _ _
  | asExpr d _ _ | satisfiesExpr d _ _ | nonNullAssertion d _
  | metaProperty d _ _ | expressionWithTypeArguments d _ _
  | trueKeyword d | falseKeyword d | nullKeyword d | thisKeyword d | superKeyword d
  | jsxElement d _ _ _ | jsxSelfClosingElement d _ _ _ | jsxFragment d _
  | jsxOpeningElement d _ _ _ | jsxClosingElement d _ | jsxText d _ _
  | jsxExpression d _ _ | jsxAttribute d _ _ | jsxSpreadAttribute d _
  | jsxAttributes d _ | omitted d | comma d _ | partiallyEmitted d _
  | syntheticExpression d
  | typeReference d _ _ | functionType d _ _ _ | constructorType d _ _ _ _
  | typeQuery d _ _ | typeLiteral d _ | arrayType d _ | tupleType d _
  | optionalType d _ | restType d _ | unionType d _ | intersectionType d _
  | conditionalType d _ _ _ _ | inferType d _ | parenthesizedType d _
  | thisType d | typeOperator d _ _ | indexedAccessType d _ _ | mappedType d _ _ _ _ _
  | literalType d _ | namedTupleMember d _ _ _ _ | templateLiteralType d _ _
  | importType d _ _ _ _ _ | typePredicate d _ _ _
  | anyKeyword d | unknownKeyword d | stringKeyword d | numberKeyword d
  | booleanKeyword d | bigIntKeyword d | symbolKeyword d | objectKeyword d
  | voidKeyword d | undefinedKeyword d | neverKeyword d | intrinsicKeyword d
  | block d _ | emptyStatement d | variableStatement d _ _ | expressionStatement d _
  | ifStatement d _ _ _ | doStatement d _ _ | whileStatement d _ _
  | forStatement d _ _ _ _ | forInStatement d _ _ _ | forOfStatement d _ _ _ _
  | continueStatement d _ | breakStatement d _ | returnStatement d _
  | withStatement d _ _ | switchStatement d _ _ | labeledStatement d _ _
  | throwStatement d _ | tryStatement d _ _ _ | debuggerStatement d
  | notEmittedStatement d
  | variableDeclaration d _ _ _ _ | variableDeclarationList d _
  | functionDeclaration d _ _ _ _ _ _ _ | classDeclaration d _ _ _ _ _
  | interfaceDeclaration d _ _ _ _ _ | typeAliasDeclaration d _ _ _ _
  | enumDeclaration d _ _ _ | moduleDeclaration d _ _ _
  | importDeclaration d _ _ _ _ | exportDeclaration d _ _ _ _ _
  | exportAssignment d _ _ _ | namespaceExportDeclaration d _
  | importEqualsDeclaration d _ _ _ _ | missingDeclaration d
  | qualifiedName d _ _ | computedPropertyName d _ | privateIdentifier d _
  | typeParameter d _ _ _ | parameter d _ _ _ _ _ _ | decorator d _
  | objectBindingPattern d _ | arrayBindingPattern d _ | bindingElement d _ _ _ _
  | propertyAssignment d _ _ _ | shorthandPropertyAssignment d _ _
  | spreadAssignment d _ | propertyDeclaration d _ _ _ _ _ _
  | methodDeclaration d _ _ _ _ _ _ _ _ | constructor_ d _ _ _
  | getAccessor d _ _ _ _ _ | setAccessor d _ _ _ _ | classStaticBlockDeclaration d _
  | semicolonClassElement d | propertySignature d _ _ _ _ | callSignature d _ _ _
  | constructSignature d _ _ _ | indexSignature d _ _ _ | methodSignature d _ _ _ _ _
  | templateSpan d _ _ | templateLiteralTypeSpan d _ _ | caseBlock d _
  | caseClause d _ _ | defaultClause d _ | heritageClause d _ _ | catchClause d _ _
  | importClause d _ _ _ | namespaceImport d _ | namedImports d _
  | importSpecifier d _ _ _ | namespaceExport d _ | namedExports d _
  | exportSpecifier d _ _ _ | externalModuleReference d _ | importAttributes d _ _
  | importAttribute d _ _ | enumMember d _ _ | moduleBlock d _
  | sourceFile d _ _ _ _ | jsDoc d _ _ | jsDocTag d _ _ | jsDocParameterTag d _ _ _ _
  | jsDocReturnTag d _ _ | jsDocTypeTag d _ _ | jsDocTypeExpression d _
  | token d _ => d

end Node

end TSLean.Ast
