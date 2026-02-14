-- TSLean.Parser.Parser: Recursive descent parser producing typed AST nodes.
-- Uses StateT ParserState (Except String) as the parsing monad.
-- The parser drives the scanner and builds the AST.

import TSLean.Ast.SyntaxKind
import TSLean.Ast.NodeData
import TSLean.Ast.Flags
import TSLean.Ast.Ast
import TSLean.Scanner.Scanner
import TSLean.Parser.ParserContext
import TSLean.Diagnostics.Category

namespace TSLean.Parser

open TSLean.Ast
open TSLean.Scanner
open TSLean.Diagnostics

-- ============================================================================
-- Parser State
-- ============================================================================

structure ParserState where
  scanner          : Scanner
  nextNodeId       : UInt32
  contextFlags     : NodeFlags
  diagnostics      : Array Diagnostic
  identifiers      : Array String
  identifierCount  : Nat
  sourceFlags      : NodeFlags
  deriving Inhabited

abbrev ParserM := StateT ParserState (Except String)

-- ============================================================================
-- Core Utilities
-- ============================================================================

def freshNodeId : ParserM NodeId := do
  let st ← get
  let id := NodeId.mk st.nextNodeId
  set { st with nextNodeId := st.nextNodeId + 1 }
  return id

def makeNodeData (pos end_ : Nat) : ParserM NodeData := do
  let id ← freshNodeId
  let st ← get
  return { id := id, flags := st.contextFlags,
           range := { pos := pos.toUInt32, «end» := end_.toUInt32 } }

@[inline] def currentToken : ParserM SyntaxKind := do
  return (← get).scanner.token

@[inline] def currentTokenValue : ParserM String := do
  return (← get).scanner.tokenValue

@[inline] def getPos : ParserM Nat := do
  return (← get).scanner.pos

@[inline] def getTokenStart : ParserM Nat := do
  return (← get).scanner.tokenStart

@[inline] def getStartPos : ParserM Nat := do
  return (← get).scanner.startPos

@[inline] def hasPrecedingLineBreak : ParserM Bool := do
  return (← get).scanner.hasPrecedingLineBreak

def nextToken : ParserM SyntaxKind := do
  let st ← get
  let scanner' := st.scanner.scan
  set { st with scanner := scanner' }
  return scanner'.token

def parseError (message : String) : ParserM Unit := do
  let st ← get
  let pos := st.scanner.tokenStart
  let diag : Diagnostic := {
    file := none
    start := pos.toUInt32
    length := (st.scanner.pos - pos).toUInt32
    category := .error
    code := 1002
    messageText := message
    relatedInformation := #[]
  }
  set { st with diagnostics := st.diagnostics.push diag }

def parseErrorAtPosition (pos end_ : Nat) (message : String) : ParserM Unit := do
  let st ← get
  let diag : Diagnostic := {
    file := none
    start := pos.toUInt32
    length := (end_ - pos).toUInt32
    category := .error
    code := 1002
    messageText := message
    relatedInformation := #[]
  }
  set { st with diagnostics := st.diagnostics.push diag }

-- ============================================================================
-- Token Predicates and Consumption
-- ============================================================================

@[inline] def isToken (kind : SyntaxKind) : ParserM Bool := do
  return (← currentToken) == kind

def parseOptional (kind : SyntaxKind) : ParserM Bool := do
  if (← currentToken) == kind then
    let _ ← nextToken
    return true
  else
    return false

def parseExpected (kind : SyntaxKind) : ParserM Bool := do
  if (← currentToken) == kind then
    let _ ← nextToken
    return true
  else
    parseError s!"'{repr kind}' expected"
    return false

def parseSemicolon : ParserM Bool := do
  let tok ← currentToken
  if tok == .semicolonToken then
    let _ ← nextToken
    return true
  else if tok == .closeBraceToken || tok == .endOfFileToken || (← hasPrecedingLineBreak) then
    return true
  else
    parseError "';' expected"
    return false

def canFollowSemicolon : ParserM Bool := do
  let tok ← currentToken
  return tok == .semicolonToken || tok == .closeBraceToken || tok == .endOfFileToken

-- ============================================================================
-- Lookahead
-- ============================================================================

def saveState : ParserM Scanner := do
  return (← get).scanner

def restoreState (saved : Scanner) : ParserM Unit := do
  modify fun st => { st with scanner := saved }

def tryParse {α : Type} (f : ParserM α) : ParserM (Option α) := do
  let saved ← saveState
  try
    let a ← f
    return some a
  catch _ =>
    restoreState saved
    return none

def lookAhead (f : ParserM Bool) : ParserM Bool := do
  let saved ← saveState
  let result ← f
  restoreState saved
  return result

-- ============================================================================
-- Non-recursive parsing helpers
-- ============================================================================

def parseIdentifier : ParserM Node := do
  let tok ← currentToken
  if tok == .identifier then
    let start ← getTokenStart
    let value ← currentTokenValue
    let _ ← nextToken
    let pos ← getPos
    let nd ← makeNodeData start pos
    return .identifier nd value
  else
    let pos ← getPos
    let nd ← makeNodeData pos pos
    parseError "Identifier expected"
    return .identifier nd "<missing>"

def parseTokenNode : ParserM Node := do
  let start ← getTokenStart
  let kind ← currentToken
  let _ ← nextToken
  let pos ← getPos
  let nd ← makeNodeData start pos
  return .token nd kind

-- ============================================================================
-- List parsing (higher-order, not mutually recursive)
-- ============================================================================

partial def parseDelimitedList (closingToken : SyntaxKind)
    (parseElement : ParserM Node) : ParserM (Array Node) := do
  let mut result : Array Node := #[]
  while (← currentToken) != closingToken && (← currentToken) != .endOfFileToken do
    result := result.push (← parseElement)
    if !(← parseOptional .commaToken) then
      break
  return result

partial def parseList (closingToken : SyntaxKind)
    (parseElement : ParserM Node) : ParserM (Array Node) := do
  let mut result : Array Node := #[]
  while (← currentToken) != closingToken && (← currentToken) != .endOfFileToken do
    result := result.push (← parseElement)
  return result

-- ============================================================================
-- Pure helpers
-- ============================================================================

private def isKeywordUsableAsIdentifier (tok : SyntaxKind) : Bool :=
  match tok with
  | .abstractKeyword | .accessorKeyword | .asKeyword | .assertsKeyword
  | .assertKeyword | .anyKeyword | .asyncKeyword | .awaitKeyword
  | .booleanKeyword | .constructorKeyword | .declareKeyword | .getKeyword
  | .inferKeyword | .intrinsicKeyword | .isKeyword | .keyOfKeyword
  | .moduleKeyword | .namespaceKeyword | .neverKeyword | .outKeyword
  | .readonlyKeyword | .requireKeyword | .numberKeyword | .objectKeyword
  | .satisfiesKeyword | .setKeyword | .stringKeyword | .symbolKeyword
  | .typeKeyword | .undefinedKeyword | .uniqueKeyword | .unknownKeyword
  | .usingKeyword | .fromKeyword | .globalKeyword | .bigIntKeyword
  | .overrideKeyword | .ofKeyword => true
  | _ => false

private def isAssignmentOperator (tok : SyntaxKind) : Bool :=
  match tok with
  | .equalsToken | .plusEqualsToken | .minusEqualsToken
  | .asteriskEqualsToken | .asteriskAsteriskEqualsToken
  | .slashEqualsToken | .percentEqualsToken
  | .lessThanLessThanEqualsToken | .greaterThanGreaterThanEqualsToken
  | .greaterThanGreaterThanGreaterThanEqualsToken
  | .ampersandEqualsToken | .barEqualsToken | .caretEqualsToken
  | .barBarEqualsToken | .ampersandAmpersandEqualsToken
  | .questionQuestionEqualsToken => true
  | _ => false

-- ============================================================================
-- Mutually recursive parsing functions
-- ============================================================================

mutual

-- Expression parsing

partial def parsePrimaryExpression : ParserM Node := do
  let tok ← currentToken
  match tok with
  | .numericLiteral => do
    let start ← getTokenStart
    let value ← currentTokenValue
    let _ ← nextToken
    let nd ← makeNodeData start (← getPos)
    return .numericLiteral nd value
  | .bigIntLiteral => do
    let start ← getTokenStart
    let value ← currentTokenValue
    let _ ← nextToken
    let nd ← makeNodeData start (← getPos)
    return .numericLiteral nd value
  | .stringLiteral => do
    let start ← getTokenStart
    let value ← currentTokenValue
    let _ ← nextToken
    let nd ← makeNodeData start (← getPos)
    -- TODO: detect single-quote from raw source text
    return .stringLiteral nd value false
  | .noSubstitutionTemplateLiteral => do
    let start ← getTokenStart
    let value ← currentTokenValue
    let _ ← nextToken
    let nd ← makeNodeData start (← getPos)
    return .noSubstitutionTemplate nd value
  | .trueKeyword => do
    let start ← getTokenStart
    let _ ← nextToken
    let nd ← makeNodeData start (← getPos)
    return .trueKeyword nd
  | .falseKeyword => do
    let start ← getTokenStart
    let _ ← nextToken
    let nd ← makeNodeData start (← getPos)
    return .falseKeyword nd
  | .nullKeyword => do
    let start ← getTokenStart
    let _ ← nextToken
    let nd ← makeNodeData start (← getPos)
    return .nullKeyword nd
  | .thisKeyword => do
    let start ← getTokenStart
    let _ ← nextToken
    let nd ← makeNodeData start (← getPos)
    return .thisKeyword nd
  | .superKeyword => do
    let start ← getTokenStart
    let _ ← nextToken
    let nd ← makeNodeData start (← getPos)
    return .superKeyword nd
  | .identifier => parseIdentifier
  | .openParenToken => do
    let start ← getTokenStart
    let _ ← nextToken
    let expr ← parseAssignmentExpressionOrHigher
    let _ ← parseExpected .closeParenToken
    let nd ← makeNodeData start (← getPos)
    return .parenthesized nd expr
  | .openBracketToken => do
    let start ← getTokenStart
    let _ ← nextToken
    let elements ← parseDelimitedList .closeBracketToken parseAssignmentExpressionOrHigher
    let _ ← parseExpected .closeBracketToken
    let nd ← makeNodeData start (← getPos)
    return .arrayLiteral nd elements
  | .openBraceToken => do
    let start ← getTokenStart
    let _ ← nextToken
    let properties ← parseDelimitedList .closeBraceToken parseObjectLiteralElement
    let _ ← parseExpected .closeBraceToken
    let nd ← makeNodeData start (← getPos)
    return .objectLiteral nd properties
  | .functionKeyword => parseFunctionExpression
  | .classKeyword => parseClassExpression
  | .newKeyword => parseNewExpression
  | .templateHead => parseTemplateExpression
  | .slashToken | .slashEqualsToken => do
    let st ← get
    let scanner' := st.scanner.reScanSlashToken
    set { st with scanner := scanner' }
    let start ← getTokenStart
    let value ← currentTokenValue
    let _ ← nextToken
    let nd ← makeNodeData start (← getPos)
    return .regexpLiteral nd value
  | _ => do
    if isKeywordUsableAsIdentifier tok then
      parseIdentifier
    else do
      let pos ← getPos
      let nd ← makeNodeData pos pos
      parseError "Expression expected"
      return .omitted nd

partial def parseMemberExpressionRest (expr : Node) : ParserM Node := do
  let tok ← currentToken
  match tok with
  | .dotToken => do
    let _ ← nextToken
    let name ← parseIdentifier
    let nd ← makeNodeData (expr.getData.range.pos.toNat) (← getPos)
    parseMemberExpressionRest (.propertyAccess nd expr name)
  | .openBracketToken => do
    let _ ← nextToken
    let index ← parseAssignmentExpressionOrHigher
    let _ ← parseExpected .closeBracketToken
    let nd ← makeNodeData (expr.getData.range.pos.toNat) (← getPos)
    parseMemberExpressionRest (.elementAccess nd expr index)
  | .exclamationToken => do
    if !(← hasPrecedingLineBreak) then
      let _ ← nextToken
      let nd ← makeNodeData (expr.getData.range.pos.toNat) (← getPos)
      parseMemberExpressionRest (.nonNullAssertion nd expr)
    else
      return expr
  | .openParenToken => do
    let _ ← nextToken
    let args ← parseDelimitedList .closeParenToken parseAssignmentExpressionOrHigher
    let _ ← parseExpected .closeParenToken
    let nd ← makeNodeData (expr.getData.range.pos.toNat) (← getPos)
    parseMemberExpressionRest (.call nd expr none args)
  | .questionDotToken => do
    let _ ← nextToken
    let next ← currentToken
    if next == .openBracketToken then
      let _ ← nextToken
      let index ← parseAssignmentExpressionOrHigher
      let _ ← parseExpected .closeBracketToken
      let nd ← makeNodeData (expr.getData.range.pos.toNat) (← getPos)
      parseMemberExpressionRest (.elementAccess nd expr index)
    else if next == .openParenToken then
      let _ ← nextToken
      let args ← parseDelimitedList .closeParenToken parseAssignmentExpressionOrHigher
      let _ ← parseExpected .closeParenToken
      let nd ← makeNodeData (expr.getData.range.pos.toNat) (← getPos)
      parseMemberExpressionRest (.call nd expr none args)
    else
      let name ← parseIdentifier
      let nd ← makeNodeData (expr.getData.range.pos.toNat) (← getPos)
      parseMemberExpressionRest (.propertyAccess nd expr name)
  | .templateHead => do
    let template ← parseTemplateExpression
    let nd ← makeNodeData (expr.getData.range.pos.toNat) (← getPos)
    parseMemberExpressionRest (.taggedTemplate nd expr none template)
  | .noSubstitutionTemplateLiteral => do
    let start ← getTokenStart
    let value ← currentTokenValue
    let _ ← nextToken
    let tNd ← makeNodeData start (← getPos)
    let template := Node.noSubstitutionTemplate tNd value
    let nd ← makeNodeData (expr.getData.range.pos.toNat) (← getPos)
    parseMemberExpressionRest (.taggedTemplate nd expr none template)
  | _ => return expr

partial def parseUnaryExpression : ParserM Node := do
  let tok ← currentToken
  match tok with
  | .plusToken | .minusToken | .tildeToken | .exclamationToken => do
    let start ← getTokenStart
    let _ ← nextToken
    let operand ← parseUnaryExpression
    let nd ← makeNodeData start (← getPos)
    return .prefixUnary nd tok operand
  | .plusPlusToken | .minusMinusToken => do
    let start ← getTokenStart
    let _ ← nextToken
    let operand ← parseUnaryExpression
    let nd ← makeNodeData start (← getPos)
    return .prefixUnary nd tok operand
  | .deleteKeyword => do
    let start ← getTokenStart
    let _ ← nextToken
    let operand ← parseUnaryExpression
    let nd ← makeNodeData start (← getPos)
    return .delete_ nd operand
  | .typeOfKeyword => do
    let start ← getTokenStart
    let _ ← nextToken
    let operand ← parseUnaryExpression
    let nd ← makeNodeData start (← getPos)
    return .typeof_ nd operand
  | .voidKeyword => do
    let start ← getTokenStart
    let _ ← nextToken
    let operand ← parseUnaryExpression
    let nd ← makeNodeData start (← getPos)
    return .void_ nd operand
  | .awaitKeyword => do
    let start ← getTokenStart
    let _ ← nextToken
    let operand ← parseUnaryExpression
    let nd ← makeNodeData start (← getPos)
    return .await_ nd operand
  | _ => do
    let expr ← parsePrimaryExpression
    let expr ← parseMemberExpressionRest expr
    let tok' ← currentToken
    if (tok' == .plusPlusToken || tok' == .minusMinusToken) && !(← hasPrecedingLineBreak) then
      let _ ← nextToken
      let nd ← makeNodeData (expr.getData.range.pos.toNat) (← getPos)
      return .postfixUnary nd expr tok'
    else
      return expr

partial def parseBinaryExpressionRest (precedence : Precedence) (left : Node) : ParserM Node := do
  let tok ← currentToken
  let newPrec := getBinaryOperatorPrecedence tok
  if newPrec <= precedence then
    return left
  else
    let _ ← nextToken
    let right ← parseUnaryExpression
    let right ← parseBinaryExpressionRest newPrec right
    let nd ← makeNodeData (left.getData.range.pos.toNat) (← getPos)
    let result := Node.binary nd left tok right
    parseBinaryExpressionRest precedence result

partial def parseAssignmentExpressionOrHigher : ParserM Node := do
  let expr ← parseUnaryExpression
  let expr ← parseBinaryExpressionRest .assignment expr
  let tok ← currentToken
  if tok == .questionToken then
    let _ ← nextToken
    let whenTrue ← parseAssignmentExpressionOrHigher
    let _ ← parseExpected .colonToken
    let whenFalse ← parseAssignmentExpressionOrHigher
    let nd ← makeNodeData (expr.getData.range.pos.toNat) (← getPos)
    return .conditional nd expr whenTrue whenFalse
  else if isAssignmentOperator tok then
    let _ ← nextToken
    let right ← parseAssignmentExpressionOrHigher
    let nd ← makeNodeData (expr.getData.range.pos.toNat) (← getPos)
    return .binary nd expr tok right
  else
    return expr

partial def parseExpression : ParserM Node := do
  let expr ← parseAssignmentExpressionOrHigher
  let tok ← currentToken
  if tok == .commaToken then
    let mut elements : Array Node := #[expr]
    while (← parseOptional .commaToken) do
      elements := elements.push (← parseAssignmentExpressionOrHigher)
    let nd ← makeNodeData (expr.getData.range.pos.toNat) (← getPos)
    return .comma nd elements
  else
    return expr

-- Type parsing

partial def parseTypeNode : ParserM Node := do
  let tok ← currentToken
  match tok with
  | .stringKeyword => do
    let start ← getTokenStart; let _ ← nextToken
    let nd ← makeNodeData start (← getPos); return .stringKeyword nd
  | .numberKeyword => do
    let start ← getTokenStart; let _ ← nextToken
    let nd ← makeNodeData start (← getPos); return .numberKeyword nd
  | .booleanKeyword => do
    let start ← getTokenStart; let _ ← nextToken
    let nd ← makeNodeData start (← getPos); return .booleanKeyword nd
  | .anyKeyword => do
    let start ← getTokenStart; let _ ← nextToken
    let nd ← makeNodeData start (← getPos); return .anyKeyword nd
  | .voidKeyword => do
    let start ← getTokenStart; let _ ← nextToken
    let nd ← makeNodeData start (← getPos); return .voidKeyword nd
  | .neverKeyword => do
    let start ← getTokenStart; let _ ← nextToken
    let nd ← makeNodeData start (← getPos); return .neverKeyword nd
  | .unknownKeyword => do
    let start ← getTokenStart; let _ ← nextToken
    let nd ← makeNodeData start (← getPos); return .unknownKeyword nd
  | .undefinedKeyword => do
    let start ← getTokenStart; let _ ← nextToken
    let nd ← makeNodeData start (← getPos); return .undefinedKeyword nd
  | .objectKeyword => do
    let start ← getTokenStart; let _ ← nextToken
    let nd ← makeNodeData start (← getPos); return .objectKeyword nd
  | .bigIntKeyword => do
    let start ← getTokenStart; let _ ← nextToken
    let nd ← makeNodeData start (← getPos); return .bigIntKeyword nd
  | .symbolKeyword => do
    let start ← getTokenStart; let _ ← nextToken
    let nd ← makeNodeData start (← getPos); return .symbolKeyword nd
  | .identifier => do
    let start ← getTokenStart
    let name ← parseIdentifier
    let typeArgs ← if (← currentToken) == .lessThanToken then
      some <$> parseTypeArguments
    else
      pure none
    let nd ← makeNodeData start (← getPos)
    return .typeReference nd name typeArgs
  | .openBracketToken => do
    let start ← getTokenStart
    let _ ← nextToken
    let elements ← parseDelimitedList .closeBracketToken parseTypeNode
    let _ ← parseExpected .closeBracketToken
    let nd ← makeNodeData start (← getPos)
    return .tupleType nd elements
  | .openParenToken => do
    let start ← getTokenStart
    let _ ← nextToken
    let inner ← parseTypeNode
    let _ ← parseExpected .closeParenToken
    let nd ← makeNodeData start (← getPos)
    return .parenthesizedType nd inner
  | .openBraceToken => do
    let start ← getTokenStart
    let _ ← nextToken
    let members ← parseList .closeBraceToken parseTypeMember
    let _ ← parseExpected .closeBraceToken
    let nd ← makeNodeData start (← getPos)
    return .typeLiteral nd members
  | _ => do
    let start ← getTokenStart
    let name ← parseIdentifier
    let nd ← makeNodeData start (← getPos)
    return .typeReference nd name none

partial def parseTypeArguments : ParserM (Array Node) := do
  let _ ← parseExpected .lessThanToken
  let args ← parseDelimitedList .greaterThanToken parseTypeNode
  let _ ← parseExpected .greaterThanToken
  return args

partial def parseTypeMember : ParserM Node := do
  let start ← getTokenStart
  let name ← parseIdentifier
  let questionToken ← parseOptional .questionToken
  let type_ ← if (← parseOptional .colonToken) then some <$> parseTypeNode else pure none
  let _ ← parseOptional .semicolonToken
  let _ ← parseOptional .commaToken
  let nd ← makeNodeData start (← getPos)
  return .propertySignature nd #[] name questionToken type_

-- Statement parsing

partial def parseBlock : ParserM Node := do
  let start ← getTokenStart
  let _ ← parseExpected .openBraceToken
  let stmts ← parseList .closeBraceToken parseStatement
  let _ ← parseExpected .closeBraceToken
  let nd ← makeNodeData start (← getPos)
  return .block nd stmts

partial def parseVariableDeclaration : ParserM Node := do
  let start ← getTokenStart
  let name ← parseIdentifier
  let excl ← parseOptional .exclamationToken
  let type_ ← if (← parseOptional .colonToken) then some <$> parseTypeNode else pure none
  let init ← if (← parseOptional .equalsToken) then
    some <$> parseAssignmentExpressionOrHigher
  else
    pure none
  let nd ← makeNodeData start (← getPos)
  return .variableDeclaration nd name excl type_ init

partial def parseVariableDeclarationList : ParserM Node := do
  let start ← getTokenStart
  let mut decls : Array Node := #[]
  decls := decls.push (← parseVariableDeclaration)
  while (← parseOptional .commaToken) do
    decls := decls.push (← parseVariableDeclaration)
  let nd ← makeNodeData start (← getPos)
  return .variableDeclarationList nd decls

partial def parseVariableStatement : ParserM Node := do
  let start ← getTokenStart
  let _ ← nextToken  -- consume var/let/const
  let declList ← parseVariableDeclarationList
  let _ ← parseSemicolon
  let nd ← makeNodeData start (← getPos)
  return .variableStatement nd #[] declList

partial def parseReturnStatement : ParserM Node := do
  let start ← getTokenStart
  let _ ← nextToken  -- consume 'return'
  let expr ← if !(← canFollowSemicolon) && !(← hasPrecedingLineBreak) then
    some <$> parseExpression
  else
    pure none
  let _ ← parseSemicolon
  let nd ← makeNodeData start (← getPos)
  return .returnStatement nd expr

partial def parseIfStatement : ParserM Node := do
  let start ← getTokenStart
  let _ ← nextToken  -- consume 'if'
  let _ ← parseExpected .openParenToken
  let cond ← parseExpression
  let _ ← parseExpected .closeParenToken
  let thenStmt ← parseStatement
  let elseStmt ← if (← parseOptional .elseKeyword) then
    some <$> parseStatement
  else
    pure none
  let nd ← makeNodeData start (← getPos)
  return .ifStatement nd cond thenStmt elseStmt

partial def parseWhileStatement : ParserM Node := do
  let start ← getTokenStart
  let _ ← nextToken  -- consume 'while'
  let _ ← parseExpected .openParenToken
  let cond ← parseExpression
  let _ ← parseExpected .closeParenToken
  let body ← parseStatement
  let nd ← makeNodeData start (← getPos)
  return .whileStatement nd cond body

partial def parseDoStatement : ParserM Node := do
  let start ← getTokenStart
  let _ ← nextToken  -- consume 'do'
  let body ← parseStatement
  let _ ← parseExpected .whileKeyword
  let _ ← parseExpected .openParenToken
  let cond ← parseExpression
  let _ ← parseExpected .closeParenToken
  let _ ← parseSemicolon
  let nd ← makeNodeData start (← getPos)
  return .doStatement nd body cond

partial def parseForStatement : ParserM Node := do
  let start ← getTokenStart
  let _ ← nextToken  -- consume 'for'
  let awaitMod ← parseOptional .awaitKeyword
  let _ ← parseExpected .openParenToken
  let tok ← currentToken
  let init ← if tok == .varKeyword || tok == .letKeyword || tok == .constKeyword then do
    let _ ← nextToken  -- consume var/let/const
    some <$> parseVariableDeclarationList
  else if tok == .semicolonToken then
    pure none
  else
    some <$> parseExpression
  let tokAfterInit ← currentToken
  if tokAfterInit == .inKeyword then
    let _ ← nextToken
    let expr ← parseExpression
    let _ ← parseExpected .closeParenToken
    let body ← parseStatement
    let nd ← makeNodeData start (← getPos)
    return .forInStatement nd (init.getD (.omitted default)) expr body
  else if tokAfterInit == .ofKeyword then
    let _ ← nextToken
    let expr ← parseAssignmentExpressionOrHigher
    let _ ← parseExpected .closeParenToken
    let body ← parseStatement
    let nd ← makeNodeData start (← getPos)
    return .forOfStatement nd awaitMod (init.getD (.omitted default)) expr body
  else
    let _ ← parseExpected .semicolonToken
    let cond ← if (← currentToken) != .semicolonToken then
      some <$> parseExpression
    else
      pure none
    let _ ← parseExpected .semicolonToken
    let incr ← if (← currentToken) != .closeParenToken then
      some <$> parseExpression
    else
      pure none
    let _ ← parseExpected .closeParenToken
    let body ← parseStatement
    let nd ← makeNodeData start (← getPos)
    return .forStatement nd init cond incr body

partial def parseThrowStatement : ParserM Node := do
  let start ← getTokenStart
  let _ ← nextToken  -- consume 'throw'
  let expr ← parseExpression
  let _ ← parseSemicolon
  let nd ← makeNodeData start (← getPos)
  return .throwStatement nd expr

partial def parseTryStatement : ParserM Node := do
  let start ← getTokenStart
  let _ ← nextToken  -- consume 'try'
  let tryBlock ← parseBlock
  let catchClause ← if (← currentToken) == .catchKeyword then do
    let cStart ← getTokenStart
    let _ ← nextToken
    let decl ← if (← parseOptional .openParenToken) then do
      let d ← parseVariableDeclaration
      let _ ← parseExpected .closeParenToken
      pure (some d)
    else
      pure none
    let block ← parseBlock
    let cNd ← makeNodeData cStart (← getPos)
    pure (some (.catchClause cNd decl block))
  else
    pure none
  let finallyBlock ← if (← parseOptional .finallyKeyword) then
    some <$> parseBlock
  else
    pure none
  let nd ← makeNodeData start (← getPos)
  return .tryStatement nd tryBlock catchClause finallyBlock

partial def parseSwitchStatement : ParserM Node := do
  let start ← getTokenStart
  let _ ← nextToken  -- consume 'switch'
  let _ ← parseExpected .openParenToken
  let expr ← parseExpression
  let _ ← parseExpected .closeParenToken
  let _ ← parseExpected .openBraceToken
  let mut clauses : Array Node := #[]
  while (← currentToken) != .closeBraceToken && (← currentToken) != .endOfFileToken do
    let tok ← currentToken
    if tok == .caseKeyword then
      let cStart ← getTokenStart
      let _ ← nextToken
      let caseExpr ← parseExpression
      let _ ← parseExpected .colonToken
      let mut stmts : Array Node := #[]
      while (← currentToken) != .caseKeyword && (← currentToken) != .defaultKeyword &&
            (← currentToken) != .closeBraceToken && (← currentToken) != .endOfFileToken do
        stmts := stmts.push (← parseStatement)
      let cNd ← makeNodeData cStart (← getPos)
      clauses := clauses.push (.caseClause cNd caseExpr stmts)
    else if tok == .defaultKeyword then
      let dStart ← getTokenStart
      let _ ← nextToken
      let _ ← parseExpected .colonToken
      let mut stmts : Array Node := #[]
      while (← currentToken) != .caseKeyword && (← currentToken) != .defaultKeyword &&
            (← currentToken) != .closeBraceToken && (← currentToken) != .endOfFileToken do
        stmts := stmts.push (← parseStatement)
      let dNd ← makeNodeData dStart (← getPos)
      clauses := clauses.push (.defaultClause dNd stmts)
    else
      parseError "case or default expected"
      let _ ← nextToken
  let _ ← parseExpected .closeBraceToken
  let cbNd ← makeNodeData start (← getPos)
  let caseBlock := Node.caseBlock cbNd clauses
  let nd ← makeNodeData start (← getPos)
  return .switchStatement nd expr caseBlock

partial def parseBreakOrContinueStatement (kind : SyntaxKind) : ParserM Node := do
  let start ← getTokenStart
  let _ ← nextToken
  let label ← if !(← hasPrecedingLineBreak) && (← currentToken) == .identifier then
    some <$> parseIdentifier
  else
    pure none
  let _ ← parseSemicolon
  let nd ← makeNodeData start (← getPos)
  if kind == .breakKeyword then
    return .breakStatement nd label
  else
    return .continueStatement nd label

-- Declaration parsing

partial def parseParameterDeclaration : ParserM Node := do
  let start ← getTokenStart
  let dotDotDot ← parseOptional .dotDotDotToken
  let name ← parseIdentifier
  let questionToken ← parseOptional .questionToken
  let type_ ← if (← parseOptional .colonToken) then some <$> parseTypeNode else pure none
  let initializer ← if (← parseOptional .equalsToken) then
    some <$> parseAssignmentExpressionOrHigher
  else
    pure none
  let nd ← makeNodeData start (← getPos)
  return .parameter nd #[] dotDotDot name questionToken type_ initializer

partial def parseFunctionDeclaration : ParserM Node := do
  let start ← getTokenStart
  let _ ← nextToken  -- consume 'function'
  let asterisk ← parseOptional .asteriskToken
  let name ← if (← currentToken) == .identifier then
    some <$> parseIdentifier
  else
    pure none
  let _ ← parseExpected .openParenToken
  let params ← parseDelimitedList .closeParenToken parseParameterDeclaration
  let _ ← parseExpected .closeParenToken
  let returnType ← if (← parseOptional .colonToken) then some <$> parseTypeNode else pure none
  let body ← if (← currentToken) == .openBraceToken then
    some <$> parseBlock
  else do
    let _ ← parseSemicolon
    pure none
  let nd ← makeNodeData start (← getPos)
  return .functionDeclaration nd #[] asterisk name none params returnType body

partial def parseFunctionExpression : ParserM Node := do
  let start ← getTokenStart
  let _ ← nextToken  -- consume 'function'
  let asterisk ← parseOptional .asteriskToken
  let name ← if (← currentToken) == .identifier then
    some <$> parseIdentifier
  else
    pure none
  let _ ← parseExpected .openParenToken
  let params ← parseDelimitedList .closeParenToken parseParameterDeclaration
  let _ ← parseExpected .closeParenToken
  let returnType ← if (← parseOptional .colonToken) then some <$> parseTypeNode else pure none
  let body ← if (← currentToken) == .openBraceToken then
    some <$> parseBlock
  else
    pure none
  let nd ← makeNodeData start (← getPos)
  return .functionExpr nd #[] asterisk name none params returnType body

partial def parseClassMember : ParserM Node := do
  let start ← getTokenStart
  let name ← parseIdentifier
  let tok ← currentToken
  if tok == .openParenToken then
    let _ ← nextToken
    let params ← parseDelimitedList .closeParenToken parseParameterDeclaration
    let _ ← parseExpected .closeParenToken
    let returnType ← if (← parseOptional .colonToken) then some <$> parseTypeNode else pure none
    let body ← if (← currentToken) == .openBraceToken then
      some <$> parseBlock
    else do
      let _ ← parseSemicolon
      pure none
    let nd ← makeNodeData start (← getPos)
    return .methodDeclaration nd #[] false name false none params returnType body
  else
    let type_ ← if (← parseOptional .colonToken) then some <$> parseTypeNode else pure none
    let init ← if (← parseOptional .equalsToken) then
      some <$> parseAssignmentExpressionOrHigher
    else
      pure none
    let _ ← parseSemicolon
    let nd ← makeNodeData start (← getPos)
    return .propertyDeclaration nd #[] name false false type_ init

partial def parseClassDeclaration : ParserM Node := do
  let start ← getTokenStart
  let _ ← nextToken  -- consume 'class'
  let name ← if (← currentToken) == .identifier then
    some <$> parseIdentifier
  else
    pure none
  let _ ← parseExpected .openBraceToken
  let members ← parseList .closeBraceToken parseClassMember
  let _ ← parseExpected .closeBraceToken
  let nd ← makeNodeData start (← getPos)
  return .classDeclaration nd #[] name none #[] members

partial def parseClassExpression : ParserM Node := do
  let start ← getTokenStart
  let _ ← nextToken  -- consume 'class'
  let name ← if (← currentToken) == .identifier then
    some <$> parseIdentifier
  else
    pure none
  let _ ← parseExpected .openBraceToken
  let members ← parseList .closeBraceToken parseClassMember
  let _ ← parseExpected .closeBraceToken
  let nd ← makeNodeData start (← getPos)
  return .classExpr nd #[] name none #[] members

-- Other parsing functions

partial def parseObjectLiteralElement : ParserM Node := do
  let start ← getTokenStart
  let tok ← currentToken
  if tok == .dotDotDotToken then
    let _ ← nextToken
    let expr ← parseAssignmentExpressionOrHigher
    let nd ← makeNodeData start (← getPos)
    return .spreadAssignment nd expr
  else
    let name ← parseIdentifier
    let tok' ← currentToken
    if tok' == .colonToken then
      let _ ← nextToken
      let value ← parseAssignmentExpressionOrHigher
      let nd ← makeNodeData start (← getPos)
      return .propertyAssignment nd name false value
    else if tok' == .openParenToken then
      let _ ← nextToken
      let params ← parseDelimitedList .closeParenToken parseParameterDeclaration
      let _ ← parseExpected .closeParenToken
      let body ← if (← currentToken) == .openBraceToken then some <$> parseBlock else pure none
      let nd ← makeNodeData start (← getPos)
      return .methodDeclaration nd #[] false name false none params none body
    else
      let nd ← makeNodeData start (← getPos)
      return .shorthandPropertyAssignment nd name none

partial def parseNewExpression : ParserM Node := do
  let start ← getTokenStart
  let _ ← nextToken  -- consume 'new'
  let expr ← parsePrimaryExpression
  let expr ← parseMemberExpressionRest expr
  let args ← if (← currentToken) == .openParenToken then do
    let _ ← nextToken
    let a ← parseDelimitedList .closeParenToken parseAssignmentExpressionOrHigher
    let _ ← parseExpected .closeParenToken
    pure (some a)
  else
    pure none
  let nd ← makeNodeData start (← getPos)
  return .new_ nd expr none args

partial def parseTemplateExpression : ParserM Node := do
  let start ← getTokenStart
  let headValue ← currentTokenValue
  let _ ← nextToken
  let headNd ← makeNodeData start (← getPos)
  let head := Node.noSubstitutionTemplate headNd headValue
  let mut spans : Array Node := #[]
  while (← currentToken) != .templateTail && (← currentToken) != .endOfFileToken do
    let spanStart ← getTokenStart
    let expr ← parseExpression
    let litStart ← getTokenStart
    let litValue ← currentTokenValue
    let _ ← nextToken
    let litNd ← makeNodeData litStart (← getPos)
    let lit := Node.noSubstitutionTemplate litNd litValue
    let spanNd ← makeNodeData spanStart (← getPos)
    spans := spans.push (.templateSpan spanNd expr lit)
  if (← currentToken) == .templateTail then
    let _ ← nextToken
  let nd ← makeNodeData start (← getPos)
  return .templateExpression nd head spans

-- Main statement dispatcher

partial def parseStatement : ParserM Node := do
  let tok ← currentToken
  match tok with
  | .openBraceToken => parseBlock
  | .varKeyword | .letKeyword | .constKeyword => parseVariableStatement
  | .functionKeyword => parseFunctionDeclaration
  | .classKeyword => parseClassDeclaration
  | .ifKeyword => parseIfStatement
  | .doKeyword => parseDoStatement
  | .whileKeyword => parseWhileStatement
  | .forKeyword => parseForStatement
  | .returnKeyword => parseReturnStatement
  | .switchKeyword => parseSwitchStatement
  | .throwKeyword => parseThrowStatement
  | .tryKeyword => parseTryStatement
  | .debuggerKeyword => do
    let start ← getTokenStart
    let _ ← nextToken
    let _ ← parseSemicolon
    let nd ← makeNodeData start (← getPos)
    return .debuggerStatement nd
  | .breakKeyword => parseBreakOrContinueStatement .breakKeyword
  | .continueKeyword => parseBreakOrContinueStatement .continueKeyword
  | .semicolonToken => do
    let start ← getTokenStart
    let _ ← nextToken
    let nd ← makeNodeData start (← getPos)
    return .emptyStatement nd
  | _ => do
    let start ← getTokenStart
    let expr ← parseExpression
    let _ ← parseSemicolon
    let nd ← makeNodeData start (← getPos)
    return .expressionStatement nd expr

end -- mutual

-- ============================================================================
-- Source File Parsing
-- ============================================================================

partial def parseSourceFile (fileName : String) (text : String)
    : Except String (Node × Array Diagnostic) := do
  let scanner := Scanner.create text
  let scanner := scanner.scan
  let initialState : ParserState := {
    scanner := scanner
    nextNodeId := 0
    contextFlags := NodeFlags.none
    diagnostics := #[]
    identifiers := #[]
    identifierCount := 0
    sourceFlags := NodeFlags.none
  }
  let action : ParserM Node := do
    let start ← getTokenStart
    let mut statements : Array Node := #[]
    while (← currentToken) != .endOfFileToken do
      statements := statements.push (← parseStatement)
    let endOfFile ← getTokenStart
    let eofNd ← makeNodeData endOfFile (← getPos)
    let nd ← makeNodeData start (← getPos)
    return .sourceFile nd fileName statements eofNd false
  match StateT.run action initialState with
  | .ok (node, state) => .ok (node, state.diagnostics)
  | .error e => .error e

end TSLean.Parser
