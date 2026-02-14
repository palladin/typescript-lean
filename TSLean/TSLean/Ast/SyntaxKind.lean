-- TSLean.Ast.SyntaxKind: All token and node kinds
-- Mirrors TypeScript's `const enum SyntaxKind` (~390 constructors)
-- Lean compiles parameterless inductives to uint tags at runtime.

namespace TSLean.Ast

set_option genInjectivity false in
/-- SyntaxKind enumerates every token and AST node type. -/
inductive SyntaxKind where
  -- Unknown
  | unknown
  | endOfFileToken
  -- Trivia
  | singleLineCommentTrivia
  | multiLineCommentTrivia
  | newLineTrivia
  | whitespaceTrivia
  | shebangTrivia
  | conflictMarkerTrivia
  | nonTextFileMarkerTrivia
  -- Literals
  | numericLiteral
  | bigIntLiteral
  | stringLiteral
  | jsxText
  | jsxTextAllWhiteSpaces
  | regularExpressionLiteral
  | noSubstitutionTemplateLiteral
  -- Pseudo-literals
  | templateHead
  | templateMiddle
  | templateTail
  -- Punctuation
  | openBraceToken
  | closeBraceToken
  | openParenToken
  | closeParenToken
  | openBracketToken
  | closeBracketToken
  | dotToken
  | dotDotDotToken
  | semicolonToken
  | commaToken
  | questionDotToken
  | lessThanToken
  | lessThanSlashToken
  | greaterThanToken
  | lessThanEqualsToken
  | greaterThanEqualsToken
  | equalsEqualsToken
  | exclamationEqualsToken
  | equalsEqualsEqualsToken
  | exclamationEqualsEqualsToken
  | equalsGreaterThanToken
  | plusToken
  | minusToken
  | asteriskToken
  | asteriskAsteriskToken
  | slashToken
  | percentToken
  | plusPlusToken
  | minusMinusToken
  | lessThanLessThanToken
  | greaterThanGreaterThanToken
  | greaterThanGreaterThanGreaterThanToken
  | ampersandToken
  | barToken
  | caretToken
  | exclamationToken
  | tildeToken
  | ampersandAmpersandToken
  | barBarToken
  | questionToken
  | colonToken
  | atToken
  | questionQuestionToken
  | backtickToken
  | hashToken
  -- Assignments
  | equalsToken
  | plusEqualsToken
  | minusEqualsToken
  | asteriskEqualsToken
  | asteriskAsteriskEqualsToken
  | slashEqualsToken
  | percentEqualsToken
  | lessThanLessThanEqualsToken
  | greaterThanGreaterThanEqualsToken
  | greaterThanGreaterThanGreaterThanEqualsToken
  | ampersandEqualsToken
  | barEqualsToken
  | barBarEqualsToken
  | ampersandAmpersandEqualsToken
  | questionQuestionEqualsToken
  | caretEqualsToken
  -- Identifiers
  | identifier
  | privateIdentifier
  | jsDocCommentTextToken
  -- Reserved words
  | breakKeyword
  | caseKeyword
  | catchKeyword
  | classKeyword
  | constKeyword
  | continueKeyword
  | debuggerKeyword
  | defaultKeyword
  | deleteKeyword
  | doKeyword
  | elseKeyword
  | enumKeyword
  | exportKeyword
  | extendsKeyword
  | falseKeyword
  | finallyKeyword
  | forKeyword
  | functionKeyword
  | ifKeyword
  | importKeyword
  | inKeyword
  | instanceOfKeyword
  | newKeyword
  | nullKeyword
  | returnKeyword
  | superKeyword
  | switchKeyword
  | thisKeyword
  | throwKeyword
  | trueKeyword
  | tryKeyword
  | typeOfKeyword
  | varKeyword
  | voidKeyword
  | whileKeyword
  | withKeyword
  -- Strict mode reserved words
  | implementsKeyword
  | interfaceKeyword
  | letKeyword
  | packageKeyword
  | privateKeyword
  | protectedKeyword
  | publicKeyword
  | staticKeyword
  | yieldKeyword
  -- Contextual keywords
  | abstractKeyword
  | accessorKeyword
  | asKeyword
  | assertsKeyword
  | assertKeyword
  | anyKeyword
  | asyncKeyword
  | awaitKeyword
  | booleanKeyword
  | constructorKeyword
  | declareKeyword
  | getKeyword
  | inferKeyword
  | intrinsicKeyword
  | isKeyword
  | keyOfKeyword
  | moduleKeyword
  | namespaceKeyword
  | neverKeyword
  | outKeyword
  | readonlyKeyword
  | requireKeyword
  | numberKeyword
  | objectKeyword
  | satisfiesKeyword
  | setKeyword
  | stringKeyword
  | symbolKeyword
  | typeKeyword
  | undefinedKeyword
  | uniqueKeyword
  | unknownKeyword
  | usingKeyword
  | fromKeyword
  | globalKeyword
  | bigIntKeyword
  | overrideKeyword
  | ofKeyword
  -- Parse tree nodes: Names
  | qualifiedName
  | computedPropertyName
  -- Signature elements
  | typeParameter
  | parameter
  | decorator
  -- Type members
  | propertySignature
  | propertyDeclaration
  | methodSignature
  | methodDeclaration
  | classStaticBlockDeclaration
  | constructor_
  | getAccessor
  | setAccessor
  | callSignature
  | constructSignature
  | indexSignature
  -- Type nodes
  | typePredicate
  | typeReference
  | functionType
  | constructorType
  | typeQuery
  | typeLiteral
  | arrayType
  | tupleType
  | optionalType
  | restType
  | unionType
  | intersectionType
  | conditionalType
  | inferType
  | parenthesizedType
  | thisType
  | typeOperator
  | indexedAccessType
  | mappedType
  | literalType
  | namedTupleMember
  | templateLiteralType
  | templateLiteralTypeSpan
  | importType
  -- Binding patterns
  | objectBindingPattern
  | arrayBindingPattern
  | bindingElement
  -- Expressions
  | arrayLiteralExpression
  | objectLiteralExpression
  | propertyAccessExpression
  | elementAccessExpression
  | callExpression
  | newExpression
  | taggedTemplateExpression
  | typeAssertionExpression
  | parenthesizedExpression
  | functionExpression
  | arrowFunction
  | deleteExpression
  | typeOfExpression
  | voidExpression
  | awaitExpression
  | prefixUnaryExpression
  | postfixUnaryExpression
  | binaryExpression
  | conditionalExpression
  | templateExpression
  | yieldExpression
  | spreadElement
  | classExpression
  | omittedExpression
  | expressionWithTypeArguments
  | asExpression
  | nonNullExpression
  | metaProperty
  | syntheticExpression
  | satisfiesExpression
  -- Misc
  | templateSpan
  | semicolonClassElement
  -- Statements
  | block
  | emptyStatement
  | variableStatement
  | expressionStatement
  | ifStatement
  | doStatement
  | whileStatement
  | forStatement
  | forInStatement
  | forOfStatement
  | continueStatement
  | breakStatement
  | returnStatement
  | withStatement
  | switchStatement
  | labeledStatement
  | throwStatement
  | tryStatement
  | debuggerStatement
  -- Declarations
  | variableDeclaration
  | variableDeclarationList
  | functionDeclaration
  | classDeclaration
  | interfaceDeclaration
  | typeAliasDeclaration
  | enumDeclaration
  | moduleDeclaration
  | moduleBlock
  | caseBlock
  | namespaceExportDeclaration
  | importEqualsDeclaration
  | importDeclaration
  | importClause
  | namespaceImport
  | namedImports
  | importSpecifier
  | exportAssignment
  | exportDeclaration
  | namedExports
  | namespaceExport
  | exportSpecifier
  | missingDeclaration
  -- Module references
  | externalModuleReference
  -- JSX
  | jsxElement
  | jsxSelfClosingElement
  | jsxOpeningElement
  | jsxClosingElement
  | jsxFragment
  | jsxOpeningFragment
  | jsxClosingFragment
  | jsxAttribute
  | jsxAttributes
  | jsxSpreadAttribute
  | jsxExpression
  | jsxNamespacedName
  -- Clauses
  | caseClause
  | defaultClause
  | heritageClause
  | catchClause
  -- Import attributes
  | importAttributes
  | importAttribute
  -- Property assignments
  | propertyAssignment
  | shorthandPropertyAssignment
  | spreadAssignment
  -- Enum
  | enumMember
  -- Top-level nodes
  | sourceFile
  | bundle
  -- JSDoc nodes
  | jsDocTypeExpression
  | jsDocNameReference
  | jsDocMemberName
  | jsDocAllType
  | jsDocUnknownType
  | jsDocNullableType
  | jsDocNonNullableType
  | jsDocOptionalType
  | jsDocFunctionType
  | jsDocVariadicType
  | jsDocNamepathType
  | jsDoc
  | jsDocText
  | jsDocTypeLiteral
  | jsDocSignature
  | jsDocLink
  | jsDocLinkCode
  | jsDocLinkPlain
  | jsDocTag
  | jsDocAugmentsTag
  | jsDocImplementsTag
  | jsDocAuthorTag
  | jsDocDeprecatedTag
  | jsDocClassTag
  | jsDocPublicTag
  | jsDocPrivateTag
  | jsDocProtectedTag
  | jsDocReadonlyTag
  | jsDocOverrideTag
  | jsDocCallbackTag
  | jsDocOverloadTag
  | jsDocEnumTag
  | jsDocParameterTag
  | jsDocReturnTag
  | jsDocThisTag
  | jsDocTypeTag
  | jsDocTemplateTag
  | jsDocTypedefTag
  | jsDocSeeTag
  | jsDocPropertyTag
  | jsDocThrowsTag
  | jsDocSatisfiesTag
  | jsDocImportTag
  -- Synthesized list
  | syntaxList
  -- Transformation nodes
  | notEmittedStatement
  | notEmittedTypeElement
  | partiallyEmittedExpression
  | commaListExpression
  | syntheticReferenceExpression
  -- Sentinel
  | count
  deriving BEq, Hashable, Repr, Inhabited

namespace SyntaxKind

/-! ## Range markers (for classification queries) -/

def firstAssignment := SyntaxKind.equalsToken
def lastAssignment := SyntaxKind.caretEqualsToken
def firstCompoundAssignment := SyntaxKind.plusEqualsToken
def lastCompoundAssignment := SyntaxKind.caretEqualsToken
def firstReservedWord := SyntaxKind.breakKeyword
def lastReservedWord := SyntaxKind.withKeyword
def firstKeyword := SyntaxKind.breakKeyword
def lastKeyword := SyntaxKind.ofKeyword
def firstFutureReservedWord := SyntaxKind.implementsKeyword
def lastFutureReservedWord := SyntaxKind.yieldKeyword
def firstTypeNode := SyntaxKind.typePredicate
def lastTypeNode := SyntaxKind.importType
def firstPunctuation := SyntaxKind.openBraceToken
def lastPunctuation := SyntaxKind.caretEqualsToken
def firstToken := SyntaxKind.unknown
def lastToken := SyntaxKind.ofKeyword
def firstTriviaToken := SyntaxKind.singleLineCommentTrivia
def lastTriviaToken := SyntaxKind.conflictMarkerTrivia
def firstLiteralToken := SyntaxKind.numericLiteral
def lastLiteralToken := SyntaxKind.noSubstitutionTemplateLiteral
def firstTemplateToken := SyntaxKind.noSubstitutionTemplateLiteral
def lastTemplateToken := SyntaxKind.templateTail
def firstBinaryOperator := SyntaxKind.lessThanToken
def lastBinaryOperator := SyntaxKind.caretEqualsToken
def firstStatement := SyntaxKind.variableStatement
def lastStatement := SyntaxKind.debuggerStatement
def firstNode := SyntaxKind.qualifiedName
def firstJSDocNode := SyntaxKind.jsDocTypeExpression
def lastJSDocNode := SyntaxKind.jsDocImportTag
def firstJSDocTagNode := SyntaxKind.jsDocTag
def lastJSDocTagNode := SyntaxKind.jsDocImportTag
def firstContextualKeyword := SyntaxKind.abstractKeyword
def lastContextualKeyword := SyntaxKind.ofKeyword

end SyntaxKind

end TSLean.Ast
