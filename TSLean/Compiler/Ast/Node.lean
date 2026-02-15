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
    Based on Go: internal/ast/ast.go (Node struct + concrete nodeData types) -/
inductive Node where
  -- Tokens (keyword/operator/punctuation used as AST nodes)
  | token (base : NodeBase) (kind : Kind)
  -- Names
  | identifier (base : NodeBase) (text : String)
  | qualifiedName (base : NodeBase) (left : Node) (right : Node)
  | computedPropertyName (base : NodeBase) (expression : Node)
  -- Literals
  | numericLiteral (base : NodeBase) (text : String)
  | stringLiteral (base : NodeBase) (text : String)
  | noSubstitutionTemplateLiteral (base : NodeBase) (text : String)
  -- Expressions
  | binaryExpression (base : NodeBase) (left : Node) (operatorToken : Node) (right : Node)
  | parenthesizedExpression (base : NodeBase) (expression : Node)
  | prefixUnaryExpression (base : NodeBase) (operator : Kind) (operand : Node)
  | postfixUnaryExpression (base : NodeBase) (operand : Node) (operator : Kind)
  | propertyAccessExpression (base : NodeBase) (expression : Node) (name : Node)
  | elementAccessExpression (base : NodeBase) (expression : Node) (argumentExpression : Node)
  | callExpression (base : NodeBase) (expression : Node) (arguments : Array Node)
  | newExpression (base : NodeBase) (expression : Node) (arguments : Option (Array Node))
  | taggedTemplateExpression (base : NodeBase) (tag : Node) (template : Node)
  | arrayLiteralExpression (base : NodeBase) (elements : Array Node)
  | objectLiteralExpression (base : NodeBase) (properties : Array Node)
  | functionExpression (base : NodeBase) (name : Option Node)
      (typeParameters : Option (Array Node)) (parameters : Array Node)
      (returnType : Option Node) (body : Option Node)
  | arrowFunction (base : NodeBase) (typeParameters : Option (Array Node))
      (parameters : Array Node) (returnType : Option Node) (body : Node)
  | conditionalExpression (base : NodeBase) (condition : Node)
      (whenTrue : Node) (whenFalse : Node)
  | templateExpression (base : NodeBase) (head : Node) (spans : Array Node)
  | templateSpan (base : NodeBase) (expression : Node) (literal : Node)
  | spreadElement (base : NodeBase) (expression : Node)
  | deleteExpression (base : NodeBase) (expression : Node)
  | typeOfExpression (base : NodeBase) (expression : Node)
  | voidExpression (base : NodeBase) (expression : Node)
  | awaitExpression (base : NodeBase) (expression : Node)
  | yieldExpression (base : NodeBase) (expression : Option Node)
  | asExpression (base : NodeBase) (expression : Node) (typeNode : Node)
  | nonNullExpression (base : NodeBase) (expression : Node)
  | satisfiesExpression (base : NodeBase) (expression : Node) (typeNode : Node)
  | expressionWithTypeArguments (base : NodeBase) (expression : Node)
      (typeArguments : Option (Array Node))
  -- Object literal members
  | propertyAssignment (base : NodeBase) (name : Node) (initializer : Option Node)
  | shorthandPropertyAssignment (base : NodeBase) (name : Node)
  | spreadAssignment (base : NodeBase) (expression : Node)
  -- Binding patterns (destructuring)
  | objectBindingPattern (base : NodeBase) (elements : Array Node)
  | arrayBindingPattern (base : NodeBase) (elements : Array Node)
  | bindingElement (base : NodeBase) (dotDotDot : Option Node)
      (propertyName : Option Node) (name : Node) (initializer : Option Node)
  | omittedExpression (base : NodeBase)
  -- Statements
  | expressionStatement (base : NodeBase) (expression : Node)
  | emptyStatement (base : NodeBase)
  | block (base : NodeBase) (statements : Array Node)
  | ifStatement (base : NodeBase) (expression : Node) (thenStatement : Node)
      (elseStatement : Option Node)
  | returnStatement (base : NodeBase) (expression : Option Node)
  | throwStatement (base : NodeBase) (expression : Option Node)
  | breakStatement (base : NodeBase) (label : Option Node)
  | continueStatement (base : NodeBase) (label : Option Node)
  | debuggerStatement (base : NodeBase)
  | whileStatement (base : NodeBase) (expression : Node) (statement : Node)
  | doStatement (base : NodeBase) (statement : Node) (expression : Node)
  | forStatement (base : NodeBase) (initializer : Option Node)
      (condition : Option Node) (incrementor : Option Node) (statement : Node)
  | forInStatement (base : NodeBase) (initializer : Option Node) (expression : Node)
      (statement : Node)
  | forOfStatement (base : NodeBase) (initializer : Option Node) (expression : Node)
      (statement : Node)
  | switchStatement (base : NodeBase) (expression : Node) (clauses : Array Node)
  | caseClause (base : NodeBase) (expression : Node) (statements : Array Node)
  | defaultClause (base : NodeBase) (statements : Array Node)
  | tryStatement (base : NodeBase) (tryBlock : Node)
      (catchClause : Option Node) (finallyBlock : Option Node)
  | catchClause (base : NodeBase) (variableDeclaration : Option Node) (block : Node)
  | withStatement (base : NodeBase) (expression : Node) (statement : Node)
  | labeledStatement (base : NodeBase) (label : Node) (statement : Node)
  | variableStatement (base : NodeBase) (declarationList : Node)
  -- Declarations
  | variableDeclarationList (base : NodeBase) (declFlags : NodeFlags)
      (declarations : Array Node)
  | variableDeclaration (base : NodeBase) (name : Node) (typeNode : Option Node)
      (initializer : Option Node)
  | functionDeclaration (base : NodeBase) (name : Option Node)
      (typeParameters : Option (Array Node)) (parameters : Array Node)
      (returnType : Option Node) (body : Option Node)
  | parameterDeclaration (base : NodeBase) (dotDotDot : Option Node) (name : Node)
      (questionToken : Option Node) (typeNode : Option Node) (initializer : Option Node)
  | classDeclaration (base : NodeBase) (name : Option Node)
      (typeParameters : Option (Array Node)) (heritageClauses : Option (Array Node))
      (members : Array Node)
  | methodDeclaration (base : NodeBase) (name : Node) (questionToken : Option Node)
      (typeParameters : Option (Array Node)) (parameters : Array Node)
      (returnType : Option Node) (body : Option Node)
  | propertyDeclaration (base : NodeBase) (name : Node)
      (questionToken : Option Node) (typeNode : Option Node) (initializer : Option Node)
  | constructor_ (base : NodeBase) (parameters : Array Node) (body : Option Node)
  | semicolonClassElement (base : NodeBase)
  -- Interface and type members
  | interfaceDeclaration (base : NodeBase) (name : Node)
      (typeParameters : Option (Array Node))
      (heritageClauses : Option (Array Node)) (members : Array Node)
  | typeAliasDeclaration (base : NodeBase) (name : Node)
      (typeParameters : Option (Array Node)) (typeNode : Node)
  | enumDeclaration (base : NodeBase) (name : Node) (members : Array Node)
  | enumMember (base : NodeBase) (name : Node) (initializer : Option Node)
  | moduleDeclaration (base : NodeBase) (name : Node) (body : Option Node)
  | moduleBlock (base : NodeBase) (statements : Array Node)
  | propertySignature (base : NodeBase) (name : Node)
      (questionToken : Option Node) (typeNode : Option Node)
  | methodSignature (base : NodeBase) (name : Node)
      (questionToken : Option Node) (typeParameters : Option (Array Node))
      (parameters : Array Node) (returnType : Option Node)
  | callSignature (base : NodeBase) (typeParameters : Option (Array Node))
      (parameters : Array Node) (returnType : Option Node)
  | constructSignature (base : NodeBase) (typeParameters : Option (Array Node))
      (parameters : Array Node) (returnType : Option Node)
  | indexSignature (base : NodeBase) (parameters : Array Node) (typeNode : Option Node)
  | heritageClause (base : NodeBase) (clauseToken : Kind) (types : Array Node)
  -- Import/Export
  | importDeclaration (base : NodeBase) (importClause : Option Node)
      (moduleSpecifier : Node)
  | importClause (base : NodeBase) (name : Option Node)
      (namedBindings : Option Node)
  | namedImports (base : NodeBase) (elements : Array Node)
  | importSpecifier (base : NodeBase) (propertyName : Option Node) (name : Node)
  | namespaceImport (base : NodeBase) (name : Node)
  | importEqualsDeclaration (base : NodeBase) (name : Node) (moduleReference : Node)
  | externalModuleReference (base : NodeBase) (expression : Node)
  | exportDeclaration (base : NodeBase) (exportClause : Option Node)
      (moduleSpecifier : Option Node)
  | exportAssignment (base : NodeBase) (expression : Node)
  | namedExports (base : NodeBase) (elements : Array Node)
  | exportSpecifier (base : NodeBase) (propertyName : Option Node) (name : Node)
  | namespaceExport (base : NodeBase) (name : Node)
  | importAttributes (base : NodeBase) (token : Kind) (elements : Array Node)
  | importAttribute (base : NodeBase) (name : Node) (value : Node)
  -- Type nodes
  | typeReference (base : NodeBase) (typeName : Node) (typeArguments : Option (Array Node))
  | unionType (base : NodeBase) (types : Array Node)
  | intersectionType (base : NodeBase) (types : Array Node)
  | arrayType (base : NodeBase) (elementType : Node)
  | tupleType (base : NodeBase) (elements : Array Node)
  | functionType (base : NodeBase) (typeParameters : Option (Array Node))
      (parameters : Array Node) (returnType : Option Node)
  | constructorType (base : NodeBase) (typeParameters : Option (Array Node))
      (parameters : Array Node) (returnType : Option Node)
  | typeLiteral (base : NodeBase) (members : Array Node)
  | parenthesizedType (base : NodeBase) (typeNode : Node)
  | typeQuery (base : NodeBase) (exprName : Node)
  | typeOperator (base : NodeBase) (operator : Kind) (typeNode : Node)
  | literalType (base : NodeBase) (literal : Node)
  | conditionalType (base : NodeBase) (checkType : Node) (extendsType : Node)
      (trueType : Node) (falseType : Node)
  | inferType (base : NodeBase) (typeParameter : Node)
  | indexedAccessType (base : NodeBase) (objectType : Node) (indexType : Node)
  | mappedType (base : NodeBase) (typeParameter : Node) (nameType : Option Node)
      (typeNode : Option Node)
  | typePredicate (base : NodeBase) (parameterName : Node) (typeNode : Option Node)
  -- Top-level
  | sourceFile (base : NodeBase) (statements : Array Node) (endOfFileToken : Node)
  -- Error recovery
  | missing (base : NodeBase) (kind : Kind)
  deriving Repr

instance : Inhabited Node := ⟨Node.emptyStatement {}⟩

namespace Node

/-- Get the Kind for a node (derived from constructor). -/
def kind : Node → Kind
  | token _ k => k
  | identifier .. => Kind.identifier
  | qualifiedName .. => Kind.qualifiedName
  | computedPropertyName .. => Kind.computedPropertyName
  | numericLiteral .. => Kind.numericLiteral
  | stringLiteral .. => Kind.stringLiteral
  | noSubstitutionTemplateLiteral .. => Kind.noSubstitutionTemplateLiteral
  | binaryExpression .. => Kind.binaryExpression
  | parenthesizedExpression .. => Kind.parenthesizedExpression
  | prefixUnaryExpression .. => Kind.prefixUnaryExpression
  | postfixUnaryExpression .. => Kind.postfixUnaryExpression
  | propertyAccessExpression .. => Kind.propertyAccessExpression
  | elementAccessExpression .. => Kind.elementAccessExpression
  | callExpression .. => Kind.callExpression
  | newExpression .. => Kind.newExpression
  | taggedTemplateExpression .. => Kind.taggedTemplateExpression
  | arrayLiteralExpression .. => Kind.arrayLiteralExpression
  | objectLiteralExpression .. => Kind.objectLiteralExpression
  | functionExpression .. => Kind.functionExpression
  | arrowFunction .. => Kind.arrowFunction
  | conditionalExpression .. => Kind.conditionalExpression
  | templateExpression .. => Kind.templateExpression
  | templateSpan .. => Kind.templateSpan
  | spreadElement .. => Kind.spreadElement
  | deleteExpression .. => Kind.deleteExpression
  | typeOfExpression .. => Kind.typeOfExpression
  | voidExpression .. => Kind.voidExpression
  | awaitExpression .. => Kind.awaitExpression
  | yieldExpression .. => Kind.yieldExpression
  | asExpression .. => Kind.asExpression
  | nonNullExpression .. => Kind.nonNullExpression
  | satisfiesExpression .. => Kind.satisfiesExpression
  | expressionWithTypeArguments .. => Kind.expressionWithTypeArguments
  | propertyAssignment .. => Kind.propertyAssignment
  | shorthandPropertyAssignment .. => Kind.shorthandPropertyAssignment
  | spreadAssignment .. => Kind.spreadAssignment
  | objectBindingPattern .. => Kind.objectBindingPattern
  | arrayBindingPattern .. => Kind.arrayBindingPattern
  | bindingElement .. => Kind.bindingElement
  | omittedExpression .. => Kind.omittedExpression
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
  | propertyDeclaration .. => Kind.propertyDeclaration
  | constructor_ .. => Kind.constructor
  | semicolonClassElement .. => Kind.semicolonClassElement
  | interfaceDeclaration .. => Kind.interfaceDeclaration
  | typeAliasDeclaration .. => Kind.typeAliasDeclaration
  | enumDeclaration .. => Kind.enumDeclaration
  | enumMember .. => Kind.enumMember
  | moduleDeclaration .. => Kind.moduleDeclaration
  | moduleBlock .. => Kind.moduleBlock
  | propertySignature .. => Kind.propertySignature
  | methodSignature .. => Kind.methodSignature
  | callSignature .. => Kind.callSignature
  | constructSignature .. => Kind.constructSignature
  | indexSignature .. => Kind.indexSignature
  | heritageClause .. => Kind.heritageClause
  | importDeclaration .. => Kind.importDeclaration
  | importClause .. => Kind.importClause
  | namedImports .. => Kind.namedImports
  | importSpecifier .. => Kind.importSpecifier
  | namespaceImport .. => Kind.namespaceImport
  | importEqualsDeclaration .. => Kind.importEqualsDeclaration
  | externalModuleReference .. => Kind.externalModuleReference
  | exportDeclaration .. => Kind.exportDeclaration
  | exportAssignment .. => Kind.exportAssignment
  | namedExports .. => Kind.namedExports
  | exportSpecifier .. => Kind.exportSpecifier
  | namespaceExport .. => Kind.namespaceExport
  | importAttributes .. => Kind.importAttributes
  | importAttribute .. => Kind.importAttribute
  | typeReference .. => Kind.typeReference
  | unionType .. => Kind.unionType
  | intersectionType .. => Kind.intersectionType
  | arrayType .. => Kind.arrayType
  | tupleType .. => Kind.tupleType
  | functionType .. => Kind.functionType
  | constructorType .. => Kind.constructorType
  | typeLiteral .. => Kind.typeLiteral
  | parenthesizedType .. => Kind.parenthesizedType
  | typeQuery .. => Kind.typeQuery
  | typeOperator .. => Kind.typeOperator
  | literalType .. => Kind.literalType
  | conditionalType .. => Kind.conditionalType
  | inferType .. => Kind.inferType
  | indexedAccessType .. => Kind.indexedAccessType
  | mappedType .. => Kind.mappedType
  | typePredicate .. => Kind.typePredicate
  | sourceFile .. => Kind.sourceFile
  | missing _ k => k

/-- Get the base data for a node. -/
def base : Node → NodeBase
  | token b _ | identifier b _ | numericLiteral b _ | stringLiteral b _
  | noSubstitutionTemplateLiteral b _ | emptyStatement b | debuggerStatement b
  | semicolonClassElement b | omittedExpression b | missing b _ => b
  | qualifiedName b .. | computedPropertyName b .. | binaryExpression b ..
  | parenthesizedExpression b .. | prefixUnaryExpression b .. | postfixUnaryExpression b ..
  | propertyAccessExpression b .. | elementAccessExpression b .. | callExpression b ..
  | newExpression b .. | taggedTemplateExpression b .. | arrayLiteralExpression b ..
  | objectLiteralExpression b .. | functionExpression b .. | arrowFunction b ..
  | conditionalExpression b .. | templateExpression b .. | templateSpan b ..
  | spreadElement b .. | deleteExpression b .. | typeOfExpression b ..
  | voidExpression b .. | awaitExpression b .. | yieldExpression b ..
  | asExpression b .. | nonNullExpression b .. | satisfiesExpression b ..
  | expressionWithTypeArguments b ..
  | propertyAssignment b .. | shorthandPropertyAssignment b .. | spreadAssignment b ..
  | objectBindingPattern b .. | arrayBindingPattern b .. | bindingElement b ..
  | expressionStatement b .. | block b .. | ifStatement b .. | returnStatement b ..
  | throwStatement b .. | breakStatement b .. | continueStatement b ..
  | whileStatement b .. | doStatement b .. | forStatement b .. | forInStatement b ..
  | forOfStatement b .. | switchStatement b .. | caseClause b .. | defaultClause b ..
  | tryStatement b .. | catchClause b .. | withStatement b .. | labeledStatement b ..
  | variableStatement b .. | variableDeclarationList b .. | variableDeclaration b ..
  | functionDeclaration b .. | parameterDeclaration b .. | classDeclaration b ..
  | methodDeclaration b .. | propertyDeclaration b .. | constructor_ b ..
  | interfaceDeclaration b .. | typeAliasDeclaration b .. | enumDeclaration b ..
  | enumMember b .. | moduleDeclaration b .. | moduleBlock b ..
  | propertySignature b .. | methodSignature b .. | callSignature b ..
  | constructSignature b .. | indexSignature b .. | heritageClause b ..
  | importDeclaration b .. | importClause b .. | namedImports b ..
  | importSpecifier b .. | namespaceImport b .. | importEqualsDeclaration b ..
  | externalModuleReference b .. | exportDeclaration b .. | exportAssignment b ..
  | namedExports b .. | exportSpecifier b .. | namespaceExport b ..
  | importAttributes b .. | importAttribute b ..
  | typeReference b .. | unionType b .. | intersectionType b .. | arrayType b ..
  | tupleType b .. | functionType b .. | constructorType b .. | typeLiteral b ..
  | parenthesizedType b .. | typeQuery b .. | typeOperator b .. | literalType b ..
  | conditionalType b .. | inferType b .. | indexedAccessType b ..
  | mappedType b .. | typePredicate b ..
  | sourceFile b .. => b

/-- Update the base data for a node. -/
def withBase : Node → NodeBase → Node
  | token _ k, b => token b k
  | identifier _ t, b => identifier b t
  | qualifiedName _ l r, b => qualifiedName b l r
  | computedPropertyName _ e, b => computedPropertyName b e
  | numericLiteral _ t, b => numericLiteral b t
  | stringLiteral _ t, b => stringLiteral b t
  | noSubstitutionTemplateLiteral _ t, b => noSubstitutionTemplateLiteral b t
  | binaryExpression _ l o r, b => binaryExpression b l o r
  | parenthesizedExpression _ e, b => parenthesizedExpression b e
  | prefixUnaryExpression _ op e, b => prefixUnaryExpression b op e
  | postfixUnaryExpression _ e op, b => postfixUnaryExpression b e op
  | propertyAccessExpression _ e n, b => propertyAccessExpression b e n
  | elementAccessExpression _ e a, b => elementAccessExpression b e a
  | callExpression _ e a, b => callExpression b e a
  | newExpression _ e a, b => newExpression b e a
  | taggedTemplateExpression _ t tl, b => taggedTemplateExpression b t tl
  | arrayLiteralExpression _ e, b => arrayLiteralExpression b e
  | objectLiteralExpression _ p, b => objectLiteralExpression b p
  | functionExpression _ n tp p rt bd, b => functionExpression b n tp p rt bd
  | arrowFunction _ tp p rt bd, b => arrowFunction b tp p rt bd
  | conditionalExpression _ c wt wf, b => conditionalExpression b c wt wf
  | templateExpression _ h s, b => templateExpression b h s
  | templateSpan _ e l, b => templateSpan b e l
  | spreadElement _ e, b => spreadElement b e
  | deleteExpression _ e, b => deleteExpression b e
  | typeOfExpression _ e, b => typeOfExpression b e
  | voidExpression _ e, b => voidExpression b e
  | awaitExpression _ e, b => awaitExpression b e
  | yieldExpression _ e, b => yieldExpression b e
  | asExpression _ e t, b => asExpression b e t
  | nonNullExpression _ e, b => nonNullExpression b e
  | satisfiesExpression _ e t, b => satisfiesExpression b e t
  | expressionWithTypeArguments _ e ta, b => expressionWithTypeArguments b e ta
  | propertyAssignment _ n i, b => propertyAssignment b n i
  | shorthandPropertyAssignment _ n, b => shorthandPropertyAssignment b n
  | spreadAssignment _ e, b => spreadAssignment b e
  | objectBindingPattern _ e, b => objectBindingPattern b e
  | arrayBindingPattern _ e, b => arrayBindingPattern b e
  | bindingElement _ d pn n i, b => bindingElement b d pn n i
  | omittedExpression _, b => omittedExpression b
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
  | propertyDeclaration _ n q t i, b => propertyDeclaration b n q t i
  | constructor_ _ p bd, b => constructor_ b p bd
  | semicolonClassElement _, b => semicolonClassElement b
  | interfaceDeclaration _ n tp hc m, b => interfaceDeclaration b n tp hc m
  | typeAliasDeclaration _ n tp t, b => typeAliasDeclaration b n tp t
  | enumDeclaration _ n m, b => enumDeclaration b n m
  | enumMember _ n i, b => enumMember b n i
  | moduleDeclaration _ n bd, b => moduleDeclaration b n bd
  | moduleBlock _ s, b => moduleBlock b s
  | propertySignature _ n q t, b => propertySignature b n q t
  | methodSignature _ n q tp p rt, b => methodSignature b n q tp p rt
  | callSignature _ tp p rt, b => callSignature b tp p rt
  | constructSignature _ tp p rt, b => constructSignature b tp p rt
  | indexSignature _ p t, b => indexSignature b p t
  | heritageClause _ ct ts, b => heritageClause b ct ts
  | importDeclaration _ ic ms, b => importDeclaration b ic ms
  | importClause _ n nb, b => importClause b n nb
  | namedImports _ e, b => namedImports b e
  | importSpecifier _ pn n, b => importSpecifier b pn n
  | namespaceImport _ n, b => namespaceImport b n
  | importEqualsDeclaration _ n mr, b => importEqualsDeclaration b n mr
  | externalModuleReference _ e, b => externalModuleReference b e
  | exportDeclaration _ ec ms, b => exportDeclaration b ec ms
  | exportAssignment _ e, b => exportAssignment b e
  | namedExports _ e, b => namedExports b e
  | exportSpecifier _ pn n, b => exportSpecifier b pn n
  | namespaceExport _ n, b => namespaceExport b n
  | importAttributes _ t e, b => importAttributes b t e
  | importAttribute _ n v, b => importAttribute b n v
  | typeReference _ tn ta, b => typeReference b tn ta
  | unionType _ ts, b => unionType b ts
  | intersectionType _ ts, b => intersectionType b ts
  | arrayType _ et, b => arrayType b et
  | tupleType _ es, b => tupleType b es
  | functionType _ tp p rt, b => functionType b tp p rt
  | constructorType _ tp p rt, b => constructorType b tp p rt
  | typeLiteral _ m, b => typeLiteral b m
  | parenthesizedType _ t, b => parenthesizedType b t
  | typeQuery _ en, b => typeQuery b en
  | typeOperator _ op t, b => typeOperator b op t
  | literalType _ l, b => literalType b l
  | conditionalType _ c e t f, b => conditionalType b c e t f
  | inferType _ tp, b => inferType b tp
  | indexedAccessType _ o i, b => indexedAccessType b o i
  | mappedType _ tp nt t, b => mappedType b tp nt t
  | typePredicate _ pn t, b => typePredicate b pn t
  | sourceFile _ s e, b => sourceFile b s e
  | missing _ k, b => missing b k

end Node

end TSLean.Compiler
