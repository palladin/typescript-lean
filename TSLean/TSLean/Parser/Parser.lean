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

-- Re-scan > to potentially produce >>, >>>, >>=, >>>=
def reScanGreaterToken : ParserM SyntaxKind := do
  let st ← get
  let newScanner := st.scanner.reScanGreaterToken
  set { st with scanner := newScanner }
  return newScanner.token

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
  | .overrideKeyword | .ofKeyword | .yieldKeyword => true
  | _ => false

def parseIdentifier : ParserM Node := do
  let tok ← currentToken
  if tok == .identifier || isKeywordUsableAsIdentifier tok then
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
    let posBefore ← getPos
    result := result.push (← parseElement)
    -- Guard against infinite loops: if parseElement didn't advance, skip the token
    if (← getPos) == posBefore then
      let _ ← nextToken
  return result

-- ============================================================================
-- Pure helpers
-- ============================================================================

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

private def isModifierKeyword (tok : SyntaxKind) : Bool :=
  match tok with
  | .publicKeyword | .privateKeyword | .protectedKeyword
  | .staticKeyword | .abstractKeyword | .readonlyKeyword
  | .asyncKeyword | .declareKeyword | .overrideKeyword
  | .accessorKeyword | .constKeyword | .defaultKeyword
  | .exportKeyword => true
  | _ => false

-- Can a token follow a modifier? If not, the "modifier" is actually the member name.
-- e.g. `static public;` → `public` is NOT a modifier (followed by `;`)
-- e.g. `static public foo` → `public` IS a modifier (followed by identifier)
private def canFollowModifier (tok : SyntaxKind) : Bool :=
  match tok with
  | .identifier => true
  | .openBracketToken | .openBraceToken | .asteriskToken | .dotDotDotToken
  | .hashToken => true
  -- Keywords that can start a declaration after modifiers
  | .abstractKeyword | .accessorKeyword | .asyncKeyword | .constKeyword
  | .declareKeyword | .getKeyword | .setKeyword | .readonlyKeyword
  | .overrideKeyword | .staticKeyword
  | .publicKeyword | .privateKeyword | .protectedKeyword => true
  -- Keyword identifiers that can be used as property names
  | _ => isKeywordUsableAsIdentifier tok

-- Parse an identifier or contextual keyword used as an identifier name.
-- Any keyword can be used as a property name / identifier name in TypeScript
private def isKeyword (tok : SyntaxKind) : Bool :=
  isKeywordUsableAsIdentifier tok || isModifierKeyword tok ||
  match tok with
  | .breakKeyword | .caseKeyword | .catchKeyword | .classKeyword
  | .continueKeyword | .debuggerKeyword | .defaultKeyword | .deleteKeyword
  | .doKeyword | .elseKeyword | .enumKeyword
  | .extendsKeyword | .falseKeyword | .finallyKeyword | .forKeyword
  | .functionKeyword | .ifKeyword | .importKeyword | .inKeyword
  | .instanceOfKeyword | .newKeyword | .nullKeyword | .returnKeyword
  | .superKeyword | .switchKeyword | .thisKeyword | .throwKeyword
  | .trueKeyword | .tryKeyword | .typeOfKeyword | .varKeyword
  | .voidKeyword | .whileKeyword | .withKeyword
  | .implementsKeyword | .interfaceKeyword | .letKeyword | .packageKeyword
  | .yieldKeyword => true
  | _ => false

def parseIdentifierName : ParserM Node := do
  let tok ← currentToken
  if tok == .identifier || isKeyword tok then
    let start ← getTokenStart
    let value ← currentTokenValue
    let _ ← nextToken
    let nd ← makeNodeData start (← getPos)
    return .identifier nd value
  else
    parseIdentifier

-- ============================================================================
-- Mutually recursive parsing functions
-- ============================================================================

mutual

-- ====================== Binding patterns ======================

-- Parse a binding name: identifier, { destructure }, or [ destructure ]
partial def parseBindingName : ParserM Node := do
  let tok ← currentToken
  match tok with
  | .openBraceToken => parseObjectBindingPattern
  | .openBracketToken => parseArrayBindingPattern
  | _ => parseIdentifier

partial def parseObjectBindingPattern : ParserM Node := do
  let start ← getTokenStart
  let _ ← parseExpected .openBraceToken
  let elements ← parseDelimitedList .closeBraceToken parseBindingElement
  let _ ← parseExpected .closeBraceToken
  let nd ← makeNodeData start (← getPos)
  return .objectBindingPattern nd elements

partial def parseArrayBindingPattern : ParserM Node := do
  let start ← getTokenStart
  let _ ← parseExpected .openBracketToken
  let elements ← parseDelimitedList .closeBracketToken parseArrayBindingElement
  let _ ← parseExpected .closeBracketToken
  let nd ← makeNodeData start (← getPos)
  return .arrayBindingPattern nd elements

partial def parseArrayBindingElement : ParserM Node := do
  -- Allow elision (empty slots): just return omitted for commas
  if (← currentToken) == .commaToken then
    let pos ← getPos
    let nd ← makeNodeData pos pos
    return .omitted nd
  parseBindingElement

partial def parseBindingElement : ParserM Node := do
  let start ← getTokenStart
  let dotDotDot ← parseOptional .dotDotDotToken
  -- Could be `propertyName: bindingName` or just `bindingName`
  let nameOrProp ← parseBindingName
  let (propName, name) ←
    if !dotDotDot && (← currentToken) == .colonToken then do
      let _ ← nextToken
      let bindName ← parseBindingName
      pure (some nameOrProp, bindName)
    else
      pure (none, nameOrProp)
  let initializer ← if (← parseOptional .equalsToken) then
    some <$> parseAssignmentExpressionOrHigher
  else pure none
  let nd ← makeNodeData start (← getPos)
  return .bindingElement nd dotDotDot propName name initializer

-- ====================== Property name parsing ======================

-- Parse a property name: identifier, string, number, computed, or private
partial def parsePropertyName : ParserM Node := do
  let tok ← currentToken
  match tok with
  | .stringLiteral => do
    let start ← getTokenStart; let value ← currentTokenValue; let _ ← nextToken
    let nd ← makeNodeData start (← getPos)
    return .stringLiteral nd value false
  | .numericLiteral => do
    let start ← getTokenStart; let value ← currentTokenValue; let _ ← nextToken
    let nd ← makeNodeData start (← getPos)
    return .numericLiteral nd value
  | .openBracketToken => do
    let start ← getTokenStart; let _ ← nextToken
    let expr ← parseAssignmentExpressionOrHigher
    let _ ← parseExpected .closeBracketToken
    let nd ← makeNodeData start (← getPos)
    return .computedPropertyName nd expr
  | .hashToken => do
    let start ← getTokenStart; let _ ← nextToken
    let value ← currentTokenValue; let _ ← nextToken
    let nd ← makeNodeData start (← getPos)
    return .privateIdentifier nd s!"#{value}"
  | _ => parseIdentifierName

-- ====================== Expression parsing ======================

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
    return .stringLiteral nd value false
  | .noSubstitutionTemplateLiteral => do
    let start ← getTokenStart
    let value ← currentTokenValue
    let _ ← nextToken
    let nd ← makeNodeData start (← getPos)
    return .noSubstitutionTemplate nd value
  | .trueKeyword => do
    let start ← getTokenStart; let _ ← nextToken
    let nd ← makeNodeData start (← getPos); return .trueKeyword nd
  | .falseKeyword => do
    let start ← getTokenStart; let _ ← nextToken
    let nd ← makeNodeData start (← getPos); return .falseKeyword nd
  | .nullKeyword => do
    let start ← getTokenStart; let _ ← nextToken
    let nd ← makeNodeData start (← getPos); return .nullKeyword nd
  | .thisKeyword => do
    let start ← getTokenStart; let _ ← nextToken
    let nd ← makeNodeData start (← getPos); return .thisKeyword nd
  | .superKeyword => do
    let start ← getTokenStart; let _ ← nextToken
    let nd ← makeNodeData start (← getPos); return .superKeyword nd
  | .identifier => parseIdentifier
  | .openParenToken => do
    let start ← getTokenStart
    let _ ← nextToken
    let expr ← parseExpression
    let _ ← parseExpected .closeParenToken
    let nd ← makeNodeData start (← getPos)
    return .parenthesized nd expr
  | .openBracketToken => do
    let start ← getTokenStart
    let _ ← nextToken
    let elements ← parseDelimitedList .closeBracketToken parseArrayLiteralElement
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
  | .classKeyword => do
    let start ← getTokenStart; parseClassExpression start
  | .newKeyword => do
    -- Check for new.target meta property
    let isMetaProp ← lookAhead do
      let _ ← nextToken; return (← currentToken) == .dotToken
    if isMetaProp then
      let metaStart ← getTokenStart
      let _ ← nextToken  -- consume 'new'
      let _ ← nextToken  -- consume '.'
      let name ← parseIdentifierName
      let nd ← makeNodeData metaStart (← getPos)
      return .metaProperty nd .newKeyword name
    parseNewExpression
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
  | .importKeyword => do
    -- import.meta or import(expr) (dynamic import)
    let isMetaProp ← lookAhead do
      let _ ← nextToken; return (← currentToken) == .dotToken
    if isMetaProp then
      let metaStart ← getTokenStart
      let _ ← nextToken  -- consume 'import'
      let _ ← nextToken  -- consume '.'
      let name ← parseIdentifierName
      let nd ← makeNodeData metaStart (← getPos)
      return .metaProperty nd .importKeyword name
    -- Dynamic import: import(expr)
    let start ← getTokenStart
    let _ ← nextToken  -- consume 'import'
    let _ ← parseExpected .openParenToken
    let arg ← parseAssignmentExpressionOrHigher
    let _ ← parseExpected .closeParenToken
    let nd ← makeNodeData start (← getPos)
    return .call nd (.token nd .importKeyword) none #[arg]
  | _ => do
    if isKeywordUsableAsIdentifier tok then
      parseIdentifier
    else do
      let pos ← getPos
      let nd ← makeNodeData pos pos
      parseError "Expression expected"
      return .omitted nd

-- Parse `...expr` or a regular assignment expression (for array/argument lists).
partial def parseSpreadOrAssignmentExpression : ParserM Node := do
  if (← currentToken) == .dotDotDotToken then
    let start ← getTokenStart
    let _ ← nextToken
    let expr ← parseAssignmentExpressionOrHigher
    let nd ← makeNodeData start (← getPos)
    return .spread nd expr
  else
    parseAssignmentExpressionOrHigher

-- Parse array literal element with elision support (commas without expressions create holes).
partial def parseArrayLiteralElement : ParserM Node := do
  if (← currentToken) == .commaToken then
    let pos ← getPos
    let nd ← makeNodeData pos pos
    return .omitted nd
  parseSpreadOrAssignmentExpression

partial def parseMemberExpressionRest (expr : Node) : ParserM Node := do
  let tok ← currentToken
  match tok with
  | .dotToken => do
    let _ ← nextToken
    let name ← parseIdentifierName
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
    let args ← parseDelimitedList .closeParenToken parseSpreadOrAssignmentExpression
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
      let args ← parseDelimitedList .closeParenToken parseSpreadOrAssignmentExpression
      let _ ← parseExpected .closeParenToken
      let nd ← makeNodeData (expr.getData.range.pos.toNat) (← getPos)
      parseMemberExpressionRest (.call nd expr none args)
    else
      let name ← parseIdentifierName
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
    let start ← getTokenStart; let _ ← nextToken
    let operand ← parseUnaryExpression
    let nd ← makeNodeData start (← getPos); return .delete_ nd operand
  | .typeOfKeyword => do
    let start ← getTokenStart; let _ ← nextToken
    let operand ← parseUnaryExpression
    let nd ← makeNodeData start (← getPos); return .typeof_ nd operand
  | .voidKeyword => do
    let start ← getTokenStart; let _ ← nextToken
    let operand ← parseUnaryExpression
    let nd ← makeNodeData start (← getPos); return .void_ nd operand
  | .awaitKeyword => do
    let start ← getTokenStart; let _ ← nextToken
    let operand ← parseUnaryExpression
    let nd ← makeNodeData start (← getPos); return .await_ nd operand
  | .yieldKeyword => parseYieldExpression
  | .lessThanToken => do
    -- Angle bracket type assertion: <Type>expr (only in non-JSX)
    let start ← getTokenStart
    let _ ← nextToken  -- consume <
    let type_ ← parseTypeNode
    let _ ← parseExpected .greaterThanToken
    let operand ← parseUnaryExpression
    let nd ← makeNodeData start (← getPos)
    return .typeAssertion nd type_ operand
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

partial def parseYieldExpression : ParserM Node := do
  let start ← getTokenStart
  let _ ← nextToken  -- consume 'yield'
  let asterisk ← parseOptional .asteriskToken
  let expr ← if !(← hasPrecedingLineBreak) && (← currentToken) != .semicolonToken &&
      (← currentToken) != .closeBraceToken && (← currentToken) != .endOfFileToken then
    some <$> parseAssignmentExpressionOrHigher
  else
    pure none
  let nd ← makeNodeData start (← getPos)
  return .yield_ nd asterisk expr

partial def parseBinaryExpressionRest (precedence : Precedence) (left : Node) : ParserM Node := do
  let mut tok ← currentToken
  -- Re-scan > to potentially produce >>, >>>, >>=, >>>=
  if tok == .greaterThanToken then
    tok ← reScanGreaterToken
  let newPrec := getBinaryOperatorPrecedence tok
  if newPrec <= precedence then
    -- Check for as/satisfies at relational precedence
    if precedence < .relational then
      if tok == .asKeyword then
        let _ ← nextToken
        let type_ ← parseTypeNode
        let nd ← makeNodeData (left.getData.range.pos.toNat) (← getPos)
        let result := Node.asExpr nd left type_
        return ← parseBinaryExpressionRest precedence result
      else if tok == .satisfiesKeyword then
        let _ ← nextToken
        let type_ ← parseTypeNode
        let nd ← makeNodeData (left.getData.range.pos.toNat) (← getPos)
        let result := Node.satisfiesExpr nd left type_
        return ← parseBinaryExpressionRest precedence result
    return left
  else
    -- Handle as/satisfies specially: right side is a type, not an expression
    if tok == .asKeyword then
      let _ ← nextToken
      let type_ ← parseTypeNode
      let nd ← makeNodeData (left.getData.range.pos.toNat) (← getPos)
      let result := Node.asExpr nd left type_
      parseBinaryExpressionRest precedence result
    else if tok == .satisfiesKeyword then
      let _ ← nextToken
      let type_ ← parseTypeNode
      let nd ← makeNodeData (left.getData.range.pos.toNat) (← getPos)
      let result := Node.satisfiesExpr nd left type_
      parseBinaryExpressionRest precedence result
    else
      let _ ← nextToken
      let right ← parseUnaryExpression
      let right ← parseBinaryExpressionRest newPrec right
      let nd ← makeNodeData (left.getData.range.pos.toNat) (← getPos)
      let result := Node.binary nd left tok right
      parseBinaryExpressionRest precedence result

partial def parseAssignmentExpressionOrHigher : ParserM Node := do
  -- Check for simple arrow function: identifier => body
  let tok ← currentToken
  if tok == .identifier then
    let isArrow ← lookAhead do
      let _ ← nextToken
      return (← currentToken) == .equalsGreaterThanToken
    if isArrow then
      let start ← getTokenStart
      let paramName ← parseIdentifier
      let arrowStart ← getTokenStart
      let _ ← nextToken  -- consume =>
      let arrowNd ← makeNodeData arrowStart (← getPos)
      let body ← parseArrowFunctionBody
      let nd ← makeNodeData start (← getPos)
      let paramNd := paramName.getData
      return .arrowFunction nd #[] none
        #[.parameter paramNd #[] false paramName false none none]
        none arrowNd body

  -- Check for spread in argument-like contexts
  if tok == .dotDotDotToken then
    let start ← getTokenStart
    let _ ← nextToken
    let expr ← parseAssignmentExpressionOrHigher
    let nd ← makeNodeData start (← getPos)
    return .spread nd expr

  -- Normal expression parsing
  let expr ← parseUnaryExpression
  let expr ← parseBinaryExpressionRest .assignment expr
  let tok' ← currentToken

  -- Check for => after parenthesized expression (arrow function)
  if tok' == .equalsGreaterThanToken then
    let arrowStart ← getTokenStart
    let _ ← nextToken  -- consume =>
    let arrowNd ← makeNodeData arrowStart (← getPos)
    let body ← parseArrowFunctionBody
    let nd ← makeNodeData (expr.getData.range.pos.toNat) (← getPos)
    -- TODO: properly convert parenthesized expression to parameter list
    return .arrowFunction nd #[] none #[] none arrowNd body

  if tok' == .questionToken then
    let _ ← nextToken
    let whenTrue ← parseAssignmentExpressionOrHigher
    let _ ← parseExpected .colonToken
    let whenFalse ← parseAssignmentExpressionOrHigher
    let nd ← makeNodeData (expr.getData.range.pos.toNat) (← getPos)
    return .conditional nd expr whenTrue whenFalse
  else if isAssignmentOperator tok' then
    let _ ← nextToken
    let right ← parseAssignmentExpressionOrHigher
    let nd ← makeNodeData (expr.getData.range.pos.toNat) (← getPos)
    return .binary nd expr tok' right
  else
    return expr

partial def parseArrowFunctionBody : ParserM Node := do
  if (← currentToken) == .openBraceToken then
    parseBlock
  else
    parseAssignmentExpressionOrHigher

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

-- ====================== Type parsing ======================

-- Entry point: handles conditional types (lowest type precedence) and type predicates.
partial def parseTypeNode : ParserM Node := do
  -- Check for `asserts x is T` or `x is T` type predicates
  if (← currentToken) == .assertsKeyword then
    let start ← getTokenStart
    let isTypePredicate ← lookAhead do
      let _ ← nextToken
      return (← currentToken) == .identifier || (← currentToken) == .thisKeyword
    if isTypePredicate then
      let _ ← nextToken  -- consume 'asserts'
      let paramName ← if (← currentToken) == .thisKeyword then do
        let s ← getTokenStart; let _ ← nextToken
        let nd ← makeNodeData s (← getPos); pure (.thisKeyword nd)
      else parseIdentifier
      let type_ ← if (← currentToken) == .isKeyword then
        let _ ← nextToken; some <$> parseTypeNode
      else pure none
      let nd ← makeNodeData start (← getPos)
      return .typePredicate nd true paramName type_
  let type_ ← parseUnionType
  -- Check for type predicate: x is T (only when type_ is an identifier or `this`)
  if (← currentToken) == .isKeyword then
    match type_ with
    | .typeReference _ nameNode none =>
      let _ ← nextToken
      let targetType ← parseTypeNode
      let nd ← makeNodeData (type_.getData.range.pos.toNat) (← getPos)
      return .typePredicate nd false nameNode (some targetType)
    | .thisType _ =>
      let _ ← nextToken
      let targetType ← parseTypeNode
      let nd ← makeNodeData (type_.getData.range.pos.toNat) (← getPos)
      return .typePredicate nd false type_ (some targetType)
    | _ => pure ()
  -- Check for conditional type: T extends U ? X : Y
  if (← currentToken) == .extendsKeyword then
    let _ ← nextToken
    let extendsType ← parseUnionType
    let _ ← parseExpected .questionToken
    let trueType ← parseTypeNode
    let _ ← parseExpected .colonToken
    let falseType ← parseTypeNode
    let nd ← makeNodeData (type_.getData.range.pos.toNat) (← getPos)
    return .conditionalType nd type_ extendsType trueType falseType
  return type_

-- Parse union type: A | B | C
partial def parseUnionType : ParserM Node := do
  let _ ← parseOptional .barToken  -- allow leading |
  let first ← parseIntersectionType
  if (← currentToken) == .barToken then
    let mut types : Array Node := #[first]
    while (← parseOptional .barToken) do
      types := types.push (← parseIntersectionType)
    let nd ← makeNodeData (first.getData.range.pos.toNat) (← getPos)
    return .unionType nd types
  return first

-- Parse intersection type: A & B & C
partial def parseIntersectionType : ParserM Node := do
  let _ ← parseOptional .ampersandToken  -- allow leading &
  let first ← parsePostfixType
  if (← currentToken) == .ampersandToken then
    let mut types : Array Node := #[first]
    while (← parseOptional .ampersandToken) do
      types := types.push (← parsePostfixType)
    let nd ← makeNodeData (first.getData.range.pos.toNat) (← getPos)
    return .intersectionType nd types
  return first

-- Parse postfix type operators: T[], T?
partial def parsePostfixType : ParserM Node := do
  let mut type_ ← parsePrefixType
  while true do
    let tok ← currentToken
    if tok == .openBracketToken then
      let isArray ← lookAhead do
        let _ ← nextToken
        return (← currentToken) == .closeBracketToken
      if isArray then
        let _ ← nextToken  -- [
        let _ ← nextToken  -- ]
        let nd ← makeNodeData (type_.getData.range.pos.toNat) (← getPos)
        type_ := .arrayType nd type_
      else
        -- Indexed access type: T[K]
        let _ ← nextToken
        let indexType ← parseTypeNode
        let _ ← parseExpected .closeBracketToken
        let nd ← makeNodeData (type_.getData.range.pos.toNat) (← getPos)
        type_ := .indexedAccessType nd type_ indexType
    else
      break
  return type_

-- Parse prefix type operators: keyof T, typeof x, readonly T[], infer T, unique symbol
partial def parsePrefixType : ParserM Node := do
  let tok ← currentToken
  match tok with
  | .keyOfKeyword => do
    let start ← getTokenStart; let _ ← nextToken
    let type_ ← parsePostfixType
    let nd ← makeNodeData start (← getPos)
    return .typeOperator nd .keyOfKeyword type_
  | .uniqueKeyword => do
    let start ← getTokenStart; let _ ← nextToken
    let type_ ← parsePostfixType
    let nd ← makeNodeData start (← getPos)
    return .typeOperator nd .uniqueKeyword type_
  | .readonlyKeyword => do
    let start ← getTokenStart; let _ ← nextToken
    let type_ ← parsePostfixType
    let nd ← makeNodeData start (← getPos)
    return .typeOperator nd .readonlyKeyword type_
  | .inferKeyword => do
    let start ← getTokenStart; let _ ← nextToken
    let tpStart ← getTokenStart
    let name ← parseIdentifier
    let constraint ← if (← currentToken) == .extendsKeyword then
      let _ ← nextToken; some <$> parseTypeNode
    else pure none
    let tpNd ← makeNodeData tpStart (← getPos)
    let nd ← makeNodeData start (← getPos)
    return .inferType nd (.typeParameter tpNd name constraint none)
  | _ => parsePrimaryTypeNode

-- Parse primary type node (non-composite).
partial def parsePrimaryTypeNode : ParserM Node := do
  let tok ← currentToken
  match tok with
  -- Keyword types
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
  | .intrinsicKeyword => do
    let start ← getTokenStart; let _ ← nextToken
    let nd ← makeNodeData start (← getPos); return .intrinsicKeyword nd
  | .thisKeyword => do
    let start ← getTokenStart; let _ ← nextToken
    let nd ← makeNodeData start (← getPos); return .thisType nd
  -- Literal types
  | .trueKeyword | .falseKeyword => do
    let start ← getTokenStart
    let _ ← nextToken
    let litNd ← makeNodeData start (← getPos)
    let lit := if tok == .trueKeyword then Node.trueKeyword litNd else Node.falseKeyword litNd
    let nd ← makeNodeData start (← getPos)
    return .literalType nd lit
  | .numericLiteral | .stringLiteral => do
    let start ← getTokenStart
    let value ← currentTokenValue
    let _ ← nextToken
    let litNd ← makeNodeData start (← getPos)
    let lit := if tok == .numericLiteral then Node.numericLiteral litNd value
               else Node.stringLiteral litNd value false
    let nd ← makeNodeData start (← getPos)
    return .literalType nd lit
  | .minusToken => do
    -- Negative literal type: -1
    let start ← getTokenStart; let _ ← nextToken
    let value ← currentTokenValue
    let _ ← nextToken
    let litNd ← makeNodeData start (← getPos)
    let lit := Node.prefixUnary litNd .minusToken (Node.numericLiteral litNd value)
    let nd ← makeNodeData start (← getPos)
    return .literalType nd lit
  -- typeof query
  | .typeOfKeyword => do
    let start ← getTokenStart; let _ ← nextToken
    let name ← parseIdentifier
    -- Parse qualified name: typeof a.b.c
    let mut expr := name
    while (← currentToken) == .dotToken do
      let _ ← nextToken
      let right ← parseIdentifierName
      let qnd ← makeNodeData (expr.getData.range.pos.toNat) (← getPos)
      expr := .qualifiedName qnd expr right
    let typeArgs ← if (← currentToken) == .lessThanToken then
      some <$> parseTypeArguments
    else pure none
    let nd ← makeNodeData start (← getPos)
    return .typeQuery nd expr typeArgs
  -- Identifier → type reference
  | .identifier => do
    let start ← getTokenStart
    let name ← parseIdentifier
    -- Parse qualified name: A.B.C
    let mut typeName := name
    while (← currentToken) == .dotToken do
      let _ ← nextToken
      let right ← parseIdentifierName
      let qnd ← makeNodeData (typeName.getData.range.pos.toNat) (← getPos)
      typeName := .qualifiedName qnd typeName right
    let typeArgs ← if (← currentToken) == .lessThanToken then
      some <$> parseTypeArguments
    else pure none
    let nd ← makeNodeData start (← getPos)
    return .typeReference nd typeName typeArgs
  -- Tuple type: [T, U]
  | .openBracketToken => do
    let start ← getTokenStart; let _ ← nextToken
    let elements ← parseDelimitedList .closeBracketToken parseTupleElement
    let _ ← parseExpected .closeBracketToken
    let nd ← makeNodeData start (← getPos)
    return .tupleType nd elements
  -- Parenthesized type or function type: (x: T) => R or (T)
  | .openParenToken => parseFunctionOrParenthesizedType
  -- Constructor type: new (...) => T
  | .newKeyword => parseConstructorType
  -- Type literal or mapped type: { ... }
  | .openBraceToken => parseTypeLiteralOrMappedType
  -- Import type: import("module").Type
  | .importKeyword => parseImportType
  -- Template literal type
  | .noSubstitutionTemplateLiteral => do
    let start ← getTokenStart
    let value ← currentTokenValue; let _ ← nextToken
    let litNd ← makeNodeData start (← getPos)
    let nd ← makeNodeData start (← getPos)
    return .literalType nd (.stringLiteral litNd value false)
  -- Fallback: treat as type reference
  | _ => do
    if isKeywordUsableAsIdentifier tok then
      let start ← getTokenStart
      let name ← parseIdentifierName
      let typeArgs ← if (← currentToken) == .lessThanToken then
        some <$> parseTypeArguments
      else pure none
      let nd ← makeNodeData start (← getPos)
      return .typeReference nd name typeArgs
    else
      let start ← getTokenStart
      let name ← parseIdentifier  -- will produce error
      let nd ← makeNodeData start (← getPos)
      return .typeReference nd name none

-- Parse function type or parenthesized type.
-- Disambiguates `(x: T) => R` (function type) from `(T)` (parenthesized type).
-- Uses lookahead: if first token after `(` is `)`, `...`, or `identifier :/?` → function type.
partial def parseFunctionOrParenthesizedType : ParserM Node := do
  let start ← getTokenStart
  -- Lookahead to disambiguate
  let isFunctionType ← lookAhead do
    let _ ← nextToken  -- consume (
    let tok ← currentToken
    if tok == .closeParenToken then return true   -- () => R
    if tok == .dotDotDotToken then return true     -- (...args) => R
    -- Check for `identifier :` or `identifier ?` or `identifier ,` patterns
    if tok == .identifier || isKeywordUsableAsIdentifier tok then
      let _ ← nextToken
      let next ← currentToken
      return next == .colonToken || next == .questionToken || next == .commaToken
        || next == .closeParenToken || next == .equalsToken
    return false
  if isFunctionType then
    let _ ← nextToken  -- consume (
    -- Parse as function type
    let typeParams : Option (Array Node) := none  -- type params come before (
    let params ← if (← currentToken) == .closeParenToken then pure #[]
      else parseDelimitedList .closeParenToken parseParameterDeclaration
    let _ ← parseExpected .closeParenToken
    let _ ← parseExpected .equalsGreaterThanToken
    let returnType ← parseTypeNode
    let nd ← makeNodeData start (← getPos)
    return .functionType nd typeParams params returnType
  else
    -- Parenthesized type: (T)
    let _ ← nextToken  -- consume (
    let inner ← parseTypeNode
    let _ ← parseExpected .closeParenToken
    -- Check if `=>` follows (degenerate function type case)
    if (← currentToken) == .equalsGreaterThanToken then
      let _ ← nextToken
      let returnType ← parseTypeNode
      let nd ← makeNodeData start (← getPos)
      return .functionType nd none #[] returnType
    let nd ← makeNodeData start (← getPos)
    return .parenthesizedType nd inner

-- Parse a tuple element: can be named (`label: Type`), rest (`...Type`), or plain type
partial def parseTupleElement : ParserM Node := do
  let start ← getTokenStart
  -- Rest element: ...Type
  if (← currentToken) == .dotDotDotToken then
    let _ ← nextToken
    let type_ ← parseTypeNode
    let nd ← makeNodeData start (← getPos)
    return .restType nd type_
  -- Could be named tuple member: `label: Type` or `label?: Type`
  let type_ ← parseTypeNode
  -- Check for named tuple: identifier followed by `:` or `?:`
  match type_ with
  | .typeReference _ nameNode none =>
    if (← currentToken) == .colonToken then
      let _ ← nextToken
      let elemType ← parseTypeNode
      let nd ← makeNodeData start (← getPos)
      return .namedTupleMember nd false nameNode false elemType
    else if (← currentToken) == .questionToken then
      let _ ← nextToken
      let _ ← parseExpected .colonToken
      let elemType ← parseTypeNode
      let nd ← makeNodeData start (← getPos)
      return .namedTupleMember nd false nameNode true elemType
    else return type_
  | _ => return type_

-- Parse constructor type: `new <T>(params) => ReturnType`
partial def parseConstructorType : ParserM Node := do
  let start ← getTokenStart
  let _ ← nextToken  -- consume 'new'
  let typeParams ← parseTypeParameters
  let _ ← parseExpected .openParenToken
  let params ← parseDelimitedList .closeParenToken parseParameterDeclaration
  let _ ← parseExpected .closeParenToken
  let _ ← parseExpected .equalsGreaterThanToken
  let returnType ← parseTypeNode
  let nd ← makeNodeData start (← getPos)
  return .constructorType nd #[] typeParams params returnType

-- Parse type literal `{ members }` or mapped type `{ [K in T]: V }`
partial def parseTypeLiteralOrMappedType : ParserM Node := do
  let start ← getTokenStart
  let _ ← nextToken  -- consume {
  -- Check for mapped type: { [K in ...]: ... } or { readonly [K in ...]: ... }
  -- Also { +readonly [K in ...] } or { -readonly [K in ...] }
  let isMapped ← lookAhead do
    -- Skip optional readonly/+readonly/-readonly
    let tok ← currentToken
    if tok == .readonlyKeyword || tok == .plusToken || tok == .minusToken then
      let _ ← nextToken
      if (← currentToken) == .readonlyKeyword then let _ ← nextToken
    if (← currentToken) != .openBracketToken then return false
    let _ ← nextToken  -- [
    if (← currentToken) != .identifier then return false
    let _ ← nextToken  -- identifier
    return (← currentToken) == .inKeyword
  if isMapped then
    parseMappedTypeBody start
  else
    let members ← parseList .closeBraceToken parseTypeMember
    let _ ← parseExpected .closeBraceToken
    let nd ← makeNodeData start (← getPos)
    return .typeLiteral nd members

-- Parse mapped type body after `{` has been consumed
partial def parseMappedTypeBody (start : Nat) : ParserM Node := do
  -- Parse optional readonly modifier: readonly, +readonly, -readonly
  let readonlyToken ← do
    let tok ← currentToken
    if tok == .readonlyKeyword then
      let _ ← nextToken; pure (some SyntaxKind.readonlyKeyword)
    else if tok == .plusToken then
      let _ ← nextToken
      if (← currentToken) == .readonlyKeyword then
        let _ ← nextToken; pure (some SyntaxKind.plusToken)
      else pure none
    else if tok == .minusToken then
      let _ ← nextToken
      if (← currentToken) == .readonlyKeyword then
        let _ ← nextToken; pure (some SyntaxKind.minusToken)
      else pure none
    else pure none
  let _ ← parseExpected .openBracketToken
  let tpStart ← getTokenStart
  let name ← parseIdentifier
  let _ ← parseExpected .inKeyword
  let constraint ← parseTypeNode
  let nameType ← if (← parseOptional .asKeyword) then some <$> parseTypeNode else pure none
  let tpNd ← makeNodeData tpStart (← getPos)
  let typeParam := Node.typeParameter tpNd name (some constraint) none
  let _ ← parseExpected .closeBracketToken
  -- Parse optional question token: ?, +?, -?
  let questionToken ← do
    let tok ← currentToken
    if tok == .questionToken then
      let _ ← nextToken; pure (some SyntaxKind.questionToken)
    else if tok == .plusToken then
      let _ ← nextToken
      if (← currentToken) == .questionToken then
        let _ ← nextToken; pure (some SyntaxKind.plusToken)
      else pure none
    else if tok == .minusToken then
      let _ ← nextToken
      if (← currentToken) == .questionToken then
        let _ ← nextToken; pure (some SyntaxKind.minusToken)
      else pure none
    else pure none
  let type_ ← if (← parseOptional .colonToken) then some <$> parseTypeNode else pure none
  let _ ← parseOptional .semicolonToken
  let _ ← parseExpected .closeBraceToken
  let nd ← makeNodeData start (← getPos)
  return .mappedType nd readonlyToken typeParam nameType questionToken type_

-- Parse import type: `import("module").Type<Args>`
partial def parseImportType : ParserM Node := do
  let start ← getTokenStart
  let isTypeOf := false  -- typeof import(...) is handled separately
  let _ ← nextToken  -- consume 'import'
  let _ ← parseExpected .openParenToken
  let argument ← parseTypeNode
  let _ ← parseExpected .closeParenToken
  -- Optional qualifier: .Foo.Bar
  let qualifier ← if (← currentToken) == .dotToken then do
    let _ ← nextToken
    let name ← parseIdentifier
    let mut q := name
    while (← currentToken) == .dotToken do
      let _ ← nextToken
      let right ← parseIdentifierName
      let qnd ← makeNodeData (q.getData.range.pos.toNat) (← getPos)
      q := .qualifiedName qnd q right
    pure (some q)
  else pure none
  let typeArgs ← if (← currentToken) == .lessThanToken then
    some <$> parseTypeArguments
  else pure none
  let nd ← makeNodeData start (← getPos)
  return .importType nd isTypeOf argument none qualifier typeArgs

partial def parseTypeArguments : ParserM (Array Node) := do
  let _ ← parseExpected .lessThanToken
  let args ← parseDelimitedList .greaterThanToken parseTypeNode
  let _ ← parseExpected .greaterThanToken
  return args

-- Parse type parameter list: <T, U extends V = W>
partial def parseTypeParameters : ParserM (Option (Array Node)) := do
  if (← currentToken) != .lessThanToken then return none
  let _ ← nextToken
  let params ← parseDelimitedList .greaterThanToken parseTypeParameter
  let _ ← parseExpected .greaterThanToken
  return some params

partial def parseTypeParameter : ParserM Node := do
  let start ← getTokenStart
  let name ← parseIdentifier
  let constraint ← if (← parseOptional .extendsKeyword) then
    some <$> parseTypeNode
  else pure none
  let default_ ← if (← parseOptional .equalsToken) then
    some <$> parseTypeNode
  else pure none
  let nd ← makeNodeData start (← getPos)
  return .typeParameter nd name constraint default_

-- Parse a type member in a type literal or interface body.
partial def parseTypeMember : ParserM Node := do
  let start ← getTokenStart
  let tok ← currentToken
  -- Call signature: (params): Type
  if tok == .openParenToken || tok == .lessThanToken then
    let typeParams ← parseTypeParameters
    let _ ← parseExpected .openParenToken
    let params ← parseDelimitedList .closeParenToken parseParameterDeclaration
    let _ ← parseExpected .closeParenToken
    let type_ ← if (← parseOptional .colonToken) then some <$> parseTypeNode else pure none
    let _ ← parseOptional .semicolonToken
    let _ ← parseOptional .commaToken
    let nd ← makeNodeData start (← getPos)
    return .callSignature nd typeParams params type_
  -- Construct signature: new (params): Type
  if tok == .newKeyword then
    let _ ← nextToken
    let typeParams ← parseTypeParameters
    let _ ← parseExpected .openParenToken
    let params ← parseDelimitedList .closeParenToken parseParameterDeclaration
    let _ ← parseExpected .closeParenToken
    let type_ ← if (← parseOptional .colonToken) then some <$> parseTypeNode else pure none
    let _ ← parseOptional .semicolonToken
    let _ ← parseOptional .commaToken
    let nd ← makeNodeData start (← getPos)
    return .constructSignature nd typeParams params type_
  -- Index signature: [key: string]: Type  vs  computed property: [expr]: Type
  if tok == .openBracketToken then
    -- Look ahead to distinguish index signature from computed property name.
    -- Index signature: [identifier :  or  [identifier ,  or  [modifier identifier
    let isIndexSig ← lookAhead do
      let _ ← nextToken  -- skip [
      -- Skip modifiers (readonly, etc.)
      while isModifierKeyword (← currentToken) do
        let _ ← nextToken
      let t ← currentToken
      if t == .identifier || isKeywordUsableAsIdentifier t then
        let _ ← nextToken
        let t2 ← currentToken
        return t2 == .colonToken || t2 == .commaToken || t2 == .closeBracketToken
      else
        return false
    if isIndexSig then
      let _ ← nextToken
      let params ← parseDelimitedList .closeBracketToken parseParameterDeclaration
      let _ ← parseExpected .closeBracketToken
      let type_ ← if (← parseOptional .colonToken) then some <$> parseTypeNode else pure none
      let _ ← parseOptional .semicolonToken
      let _ ← parseOptional .commaToken
      let nd ← makeNodeData start (← getPos)
      return .indexSignature nd #[] params type_
    -- else fall through: treat as computed property name
  -- Parse modifiers (readonly, etc.)
  let memberMods ← parseModifiers
  let name ← parsePropertyName
  let questionToken ← parseOptional .questionToken
  -- Method signature: name(params): Type
  if (← currentToken) == .openParenToken || (← currentToken) == .lessThanToken then
    let typeParams ← parseTypeParameters
    let _ ← parseExpected .openParenToken
    let params ← parseDelimitedList .closeParenToken parseParameterDeclaration
    let _ ← parseExpected .closeParenToken
    let type_ ← if (← parseOptional .colonToken) then some <$> parseTypeNode else pure none
    let _ ← parseOptional .semicolonToken
    let _ ← parseOptional .commaToken
    let nd ← makeNodeData start (← getPos)
    return .methodSignature nd name questionToken typeParams params type_
  -- Property signature: name?: Type
  let type_ ← if (← parseOptional .colonToken) then some <$> parseTypeNode else pure none
  let _ ← parseOptional .semicolonToken
  let _ ← parseOptional .commaToken
  let nd ← makeNodeData start (← getPos)
  return .propertySignature nd memberMods name questionToken type_

-- ====================== Statement parsing ======================

partial def parseBlock : ParserM Node := do
  let start ← getTokenStart
  let _ ← parseExpected .openBraceToken
  let stmts ← parseList .closeBraceToken parseStatement
  let _ ← parseExpected .closeBraceToken
  let nd ← makeNodeData start (← getPos)
  return .block nd stmts

partial def parseVariableDeclaration : ParserM Node := do
  let start ← getTokenStart
  let name ← parseBindingName
  let excl ← parseOptional .exclamationToken
  let type_ ← if (← parseOptional .colonToken) then some <$> parseTypeNode else pure none
  let init ← if (← parseOptional .equalsToken) then
    some <$> parseAssignmentExpressionOrHigher
  else pure none
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

partial def parseVariableStatement (start : Nat) (mods : Array Modifier) : ParserM Node := do
  let tok ← currentToken
  -- Store var/let/const kind in context flags for the declaration list
  let savedFlags := (← get).contextFlags
  if tok == .letKeyword then
    modify fun st => { st with contextFlags := ⟨st.contextFlags.val ||| NodeFlags.let_.val⟩ }
  else if tok == .constKeyword then
    modify fun st => { st with contextFlags := ⟨st.contextFlags.val ||| NodeFlags.const_.val⟩ }
  else
    pure ()
  let _ ← nextToken  -- consume var/let/const
  let declList ← parseVariableDeclarationList
  modify fun st => { st with contextFlags := savedFlags }
  let _ ← parseSemicolon
  let nd ← makeNodeData start (← getPos)
  return .variableStatement nd mods declList

partial def parseReturnStatement : ParserM Node := do
  let start ← getTokenStart
  let _ ← nextToken
  let expr ← if !(← canFollowSemicolon) && !(← hasPrecedingLineBreak) then
    some <$> parseExpression
  else pure none
  let _ ← parseSemicolon
  let nd ← makeNodeData start (← getPos)
  return .returnStatement nd expr

partial def parseIfStatement : ParserM Node := do
  let start ← getTokenStart
  let _ ← nextToken
  let _ ← parseExpected .openParenToken
  let cond ← parseExpression
  let _ ← parseExpected .closeParenToken
  let thenStmt ← parseStatement
  let elseStmt ← if (← parseOptional .elseKeyword) then some <$> parseStatement else pure none
  let nd ← makeNodeData start (← getPos)
  return .ifStatement nd cond thenStmt elseStmt

partial def parseWhileStatement : ParserM Node := do
  let start ← getTokenStart; let _ ← nextToken
  let _ ← parseExpected .openParenToken
  let cond ← parseExpression
  let _ ← parseExpected .closeParenToken
  let body ← parseStatement
  let nd ← makeNodeData start (← getPos)
  return .whileStatement nd cond body

partial def parseDoStatement : ParserM Node := do
  let start ← getTokenStart; let _ ← nextToken
  let body ← parseStatement
  let _ ← parseExpected .whileKeyword
  let _ ← parseExpected .openParenToken
  let cond ← parseExpression
  let _ ← parseExpected .closeParenToken
  let _ ← parseSemicolon
  let nd ← makeNodeData start (← getPos)
  return .doStatement nd body cond

partial def parseForStatement : ParserM Node := do
  let start ← getTokenStart; let _ ← nextToken
  let awaitMod ← parseOptional .awaitKeyword
  let _ ← parseExpected .openParenToken
  let tok ← currentToken
  let init ← if tok == .varKeyword || tok == .letKeyword || tok == .constKeyword then do
    let _ ← nextToken
    some <$> parseVariableDeclarationList
  else if tok == .semicolonToken then pure none
  else some <$> parseExpression
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
    let cond ← if (← currentToken) != .semicolonToken then some <$> parseExpression else pure none
    let _ ← parseExpected .semicolonToken
    let incr ← if (← currentToken) != .closeParenToken then some <$> parseExpression else pure none
    let _ ← parseExpected .closeParenToken
    let body ← parseStatement
    let nd ← makeNodeData start (← getPos)
    return .forStatement nd init cond incr body

partial def parseThrowStatement : ParserM Node := do
  let start ← getTokenStart; let _ ← nextToken
  let expr ← parseExpression
  let _ ← parseSemicolon
  let nd ← makeNodeData start (← getPos)
  return .throwStatement nd expr

partial def parseTryStatement : ParserM Node := do
  let start ← getTokenStart; let _ ← nextToken
  let tryBlock ← parseBlock
  let catchClause ← if (← currentToken) == .catchKeyword then do
    let cStart ← getTokenStart; let _ ← nextToken
    let decl ← if (← parseOptional .openParenToken) then do
      let d ← parseVariableDeclaration
      let _ ← parseExpected .closeParenToken; pure (some d)
    else pure none
    let block ← parseBlock
    let cNd ← makeNodeData cStart (← getPos)
    pure (some (.catchClause cNd decl block))
  else pure none
  let finallyBlock ← if (← parseOptional .finallyKeyword) then some <$> parseBlock else pure none
  let nd ← makeNodeData start (← getPos)
  return .tryStatement nd tryBlock catchClause finallyBlock

partial def parseSwitchStatement : ParserM Node := do
  let start ← getTokenStart; let _ ← nextToken
  let _ ← parseExpected .openParenToken
  let expr ← parseExpression
  let _ ← parseExpected .closeParenToken
  let _ ← parseExpected .openBraceToken
  let mut clauses : Array Node := #[]
  while (← currentToken) != .closeBraceToken && (← currentToken) != .endOfFileToken do
    let tok ← currentToken
    if tok == .caseKeyword then
      let cStart ← getTokenStart; let _ ← nextToken
      let caseExpr ← parseExpression
      let _ ← parseExpected .colonToken
      let mut stmts : Array Node := #[]
      while (← currentToken) != .caseKeyword && (← currentToken) != .defaultKeyword &&
            (← currentToken) != .closeBraceToken && (← currentToken) != .endOfFileToken do
        let posBefore ← getPos
        stmts := stmts.push (← parseStatement)
        if (← getPos) == posBefore then let _ ← nextToken
      let cNd ← makeNodeData cStart (← getPos)
      clauses := clauses.push (.caseClause cNd caseExpr stmts)
    else if tok == .defaultKeyword then
      let dStart ← getTokenStart; let _ ← nextToken
      let _ ← parseExpected .colonToken
      let mut stmts : Array Node := #[]
      while (← currentToken) != .caseKeyword && (← currentToken) != .defaultKeyword &&
            (← currentToken) != .closeBraceToken && (← currentToken) != .endOfFileToken do
        let posBefore ← getPos
        stmts := stmts.push (← parseStatement)
        if (← getPos) == posBefore then let _ ← nextToken
      let dNd ← makeNodeData dStart (← getPos)
      clauses := clauses.push (.defaultClause dNd stmts)
    else
      parseError "case or default expected"; let _ ← nextToken
  let _ ← parseExpected .closeBraceToken
  let cbNd ← makeNodeData start (← getPos)
  let nd ← makeNodeData start (← getPos)
  return .switchStatement nd expr (.caseBlock cbNd clauses)

partial def parseBreakOrContinueStatement (kind : SyntaxKind) : ParserM Node := do
  let start ← getTokenStart; let _ ← nextToken
  let label ← if !(← hasPrecedingLineBreak) && (← currentToken) == .identifier then
    some <$> parseIdentifier
  else pure none
  let _ ← parseSemicolon
  let nd ← makeNodeData start (← getPos)
  if kind == .breakKeyword then return .breakStatement nd label
  else return .continueStatement nd label

partial def parseWithStatement : ParserM Node := do
  let start ← getTokenStart; let _ ← nextToken
  let _ ← parseExpected .openParenToken
  let expr ← parseExpression
  let _ ← parseExpected .closeParenToken
  let body ← parseStatement
  let nd ← makeNodeData start (← getPos)
  return .withStatement nd expr body

-- ====================== Declaration parsing ======================

-- Parse modifier keywords (public, private, static, abstract, etc.)
partial def parseModifiers : ParserM (Array Modifier) := do
  let mut mods : Array Modifier := #[]
  while isModifierKeyword (← currentToken) do
    -- Check if what follows this keyword can follow a modifier;
    -- if not, this keyword is actually the member name, not a modifier.
    let nextCanFollow ← lookAhead do
      let _ ← nextToken
      return canFollowModifier (← currentToken)
    if !nextCanFollow then break
    let start ← getTokenStart
    let kind ← currentToken
    let _ ← nextToken
    let nd ← makeNodeData start (← getPos)
    mods := mods.push { data := nd, kind := kind }
  return mods

partial def parseParameterDeclaration : ParserM Node := do
  let start ← getTokenStart
  let mods ← parseModifiers
  let dotDotDot ← parseOptional .dotDotDotToken
  let name ← parseBindingName
  let questionToken ← parseOptional .questionToken
  let type_ ← if (← parseOptional .colonToken) then some <$> parseTypeNode else pure none
  let initializer ← if (← parseOptional .equalsToken) then
    some <$> parseAssignmentExpressionOrHigher
  else pure none
  let nd ← makeNodeData start (← getPos)
  return .parameter nd mods dotDotDot name questionToken type_ initializer

-- Parse heritage clauses: extends Foo, Bar implements Baz
partial def parseHeritageClauses : ParserM (Array Node) := do
  let mut clauses : Array Node := #[]
  while (← currentToken) == .extendsKeyword || (← currentToken) == .implementsKeyword do
    let hStart ← getTokenStart
    let token ← currentToken
    let _ ← nextToken
    let mut types : Array Node := #[]
    types := types.push (← parseExpressionWithTypeArguments)
    while (← parseOptional .commaToken) do
      types := types.push (← parseExpressionWithTypeArguments)
    let hNd ← makeNodeData hStart (← getPos)
    clauses := clauses.push (.heritageClause hNd token types)
  return clauses

partial def parseExpressionWithTypeArguments : ParserM Node := do
  let start ← getTokenStart
  let expr ← parseIdentifier
  -- Parse qualified: A.B
  let mut name := expr
  while (← currentToken) == .dotToken do
    let _ ← nextToken
    let right ← parseIdentifierName
    let qnd ← makeNodeData (name.getData.range.pos.toNat) (← getPos)
    name := .qualifiedName qnd name right
  let typeArgs ← if (← currentToken) == .lessThanToken then
    some <$> parseTypeArguments
  else pure none
  let nd ← makeNodeData start (← getPos)
  return .expressionWithTypeArguments nd name typeArgs

partial def parseFunctionDeclaration (start : Nat) (mods : Array Modifier) : ParserM Node := do
  let _ ← nextToken  -- consume 'function'
  let asterisk ← parseOptional .asteriskToken
  let tok ← currentToken
  let name ← if tok == .identifier || isKeywordUsableAsIdentifier tok then
    some <$> parseIdentifier
  else pure none
  let typeParams ← parseTypeParameters
  let _ ← parseExpected .openParenToken
  let params ← parseDelimitedList .closeParenToken parseParameterDeclaration
  let _ ← parseExpected .closeParenToken
  let returnType ← if (← parseOptional .colonToken) then some <$> parseTypeNode else pure none
  let body ← if (← currentToken) == .openBraceToken then some <$> parseBlock
  else do let _ ← parseSemicolon; pure none
  let nd ← makeNodeData start (← getPos)
  return .functionDeclaration nd mods asterisk name typeParams params returnType body

partial def parseFunctionExpression : ParserM Node := do
  let start ← getTokenStart
  let _ ← nextToken
  let asterisk ← parseOptional .asteriskToken
  let tok ← currentToken
  let name ← if tok == .identifier || isKeywordUsableAsIdentifier tok then
    some <$> parseIdentifier
  else pure none
  let typeParams ← parseTypeParameters
  let _ ← parseExpected .openParenToken
  let params ← parseDelimitedList .closeParenToken parseParameterDeclaration
  let _ ← parseExpected .closeParenToken
  let returnType ← if (← parseOptional .colonToken) then some <$> parseTypeNode else pure none
  let body ← if (← currentToken) == .openBraceToken then some <$> parseBlock else pure none
  let nd ← makeNodeData start (← getPos)
  return .functionExpr nd #[] asterisk name typeParams params returnType body

partial def parseClassMember : ParserM Node := do
  let start ← getTokenStart
  -- Handle semicolons
  if (← currentToken) == .semicolonToken then
    let _ ← nextToken
    let nd ← makeNodeData start (← getPos)
    return .semicolonClassElement nd
  let mods ← parseModifiers
  let tok ← currentToken
  -- Constructor
  if tok == .constructorKeyword then
    let _ ← nextToken
    let _ ← parseExpected .openParenToken
    let params ← parseDelimitedList .closeParenToken parseParameterDeclaration
    let _ ← parseExpected .closeParenToken
    let body ← if (← currentToken) == .openBraceToken then some <$> parseBlock else do
      let _ ← parseSemicolon; pure none
    let nd ← makeNodeData start (← getPos)
    return .constructor_ nd mods params body
  -- Static block: static { ... }
  if tok == .staticKeyword then
    let isStaticBlock ← lookAhead do
      let _ ← nextToken; return (← currentToken) == .openBraceToken
    if isStaticBlock then
      let _ ← nextToken  -- consume 'static'
      let body ← parseBlock
      let nd ← makeNodeData start (← getPos)
      return .classStaticBlockDeclaration nd body
  -- Get/set accessors
  if tok == .getKeyword || tok == .setKeyword then
    let isAccessor ← lookAhead do
      let _ ← nextToken
      let t ← currentToken
      return t == .identifier || t == .stringLiteral || t == .numericLiteral
        || t == .openBracketToken || t == .hashToken || isKeywordUsableAsIdentifier t
    if isAccessor then
      let _ ← nextToken
      let name ← parsePropertyName
      let _typeParams ← parseTypeParameters
      let _ ← parseExpected .openParenToken
      let params ← parseDelimitedList .closeParenToken parseParameterDeclaration
      let _ ← parseExpected .closeParenToken
      if tok == .getKeyword then
        let returnType ← if (← parseOptional .colonToken) then some <$> parseTypeNode else pure none
        let body ← if (← currentToken) == .openBraceToken then some <$> parseBlock else do
          let _ ← parseSemicolon; pure none
        let nd ← makeNodeData start (← getPos)
        return .getAccessor nd mods name params returnType body
      else
        let body ← if (← currentToken) == .openBraceToken then some <$> parseBlock else do
          let _ ← parseSemicolon; pure none
        let nd ← makeNodeData start (← getPos)
        return .setAccessor nd mods name params body
  -- Index signature: [key: type]: Type
  if tok == .openBracketToken then
    let isIndexSig ← lookAhead do
      let _ ← nextToken  -- skip [
      while isModifierKeyword (← currentToken) do
        let _ ← nextToken
      let t ← currentToken
      if t == .identifier || isKeywordUsableAsIdentifier t then
        let _ ← nextToken
        let t2 ← currentToken
        return t2 == .colonToken || t2 == .commaToken || t2 == .closeBracketToken
      else
        return false
    if isIndexSig then
      let _ ← nextToken  -- consume [
      let params ← parseDelimitedList .closeBracketToken parseParameterDeclaration
      let _ ← parseExpected .closeBracketToken
      let type_ ← if (← parseOptional .colonToken) then some <$> parseTypeNode else pure none
      let _ ← parseSemicolon
      let nd ← makeNodeData start (← getPos)
      return .indexSignature nd mods params type_
  -- Regular member: name, method or property
  let name ← parsePropertyName
  let questionToken ← parseOptional .questionToken
  if (← currentToken) == .openParenToken || (← currentToken) == .lessThanToken then
    let typeParams ← parseTypeParameters
    let _ ← parseExpected .openParenToken
    let params ← parseDelimitedList .closeParenToken parseParameterDeclaration
    let _ ← parseExpected .closeParenToken
    let returnType ← if (← parseOptional .colonToken) then some <$> parseTypeNode else pure none
    let body ← if (← currentToken) == .openBraceToken then some <$> parseBlock
    else do let _ ← parseSemicolon; pure none
    let nd ← makeNodeData start (← getPos)
    return .methodDeclaration nd mods false name questionToken typeParams params returnType body
  else
    let excl ← parseOptional .exclamationToken
    let type_ ← if (← parseOptional .colonToken) then some <$> parseTypeNode else pure none
    let init ← if (← parseOptional .equalsToken) then
      some <$> parseAssignmentExpressionOrHigher
    else pure none
    let _ ← parseSemicolon
    let nd ← makeNodeData start (← getPos)
    return .propertyDeclaration nd mods name questionToken excl type_ init

partial def parseClassDeclaration (start : Nat) (mods : Array Modifier) : ParserM Node := do
  let _ ← nextToken  -- consume 'class'
  let ctok ← currentToken
  let name ← if ctok == .identifier || isKeywordUsableAsIdentifier ctok then
    some <$> parseIdentifier
  else pure none
  let typeParams ← parseTypeParameters
  let heritageClauses ← parseHeritageClauses
  let _ ← parseExpected .openBraceToken
  let members ← parseList .closeBraceToken parseClassMember
  let _ ← parseExpected .closeBraceToken
  let nd ← makeNodeData start (← getPos)
  return .classDeclaration nd mods name typeParams heritageClauses members

partial def parseClassExpression (start : Nat) : ParserM Node := do
  let _ ← nextToken  -- consume 'class'
  let ctok ← currentToken
  let name ← if ctok == .identifier || isKeywordUsableAsIdentifier ctok then
    some <$> parseIdentifier
  else pure none
  let typeParams ← parseTypeParameters
  let heritageClauses ← parseHeritageClauses
  let _ ← parseExpected .openBraceToken
  let members ← parseList .closeBraceToken parseClassMember
  let _ ← parseExpected .closeBraceToken
  let nd ← makeNodeData start (← getPos)
  return .classExpr nd #[] name typeParams heritageClauses members

partial def parseInterfaceDeclaration (start : Nat) (mods : Array Modifier) : ParserM Node := do
  let _ ← nextToken  -- consume 'interface'
  let name ← parseIdentifier
  let typeParams ← parseTypeParameters
  let heritageClauses ← parseHeritageClauses
  let _ ← parseExpected .openBraceToken
  let members ← parseList .closeBraceToken parseTypeMember
  let _ ← parseExpected .closeBraceToken
  let nd ← makeNodeData start (← getPos)
  return .interfaceDeclaration nd mods name typeParams heritageClauses members

partial def parseEnumDeclaration (start : Nat) (mods : Array Modifier) : ParserM Node := do
  let _ ← nextToken  -- consume 'enum'
  let name ← parseIdentifier
  let _ ← parseExpected .openBraceToken
  let members ← parseDelimitedList .closeBraceToken parseEnumMember
  let _ ← parseExpected .closeBraceToken
  let nd ← makeNodeData start (← getPos)
  return .enumDeclaration nd mods name members

partial def parseEnumMember : ParserM Node := do
  let start ← getTokenStart
  let name ← parsePropertyName
  let init ← if (← parseOptional .equalsToken) then
    some <$> parseAssignmentExpressionOrHigher
  else pure none
  let nd ← makeNodeData start (← getPos)
  return .enumMember nd name init

partial def parseTypeAliasDeclaration (start : Nat) (mods : Array Modifier) : ParserM Node := do
  let _ ← nextToken  -- consume 'type'
  let name ← parseIdentifier
  let typeParams ← parseTypeParameters
  let _ ← parseExpected .equalsToken
  let type_ ← parseTypeNode
  let _ ← parseSemicolon
  let nd ← makeNodeData start (← getPos)
  return .typeAliasDeclaration nd mods name typeParams type_

-- Parse the body of a module: either { stmts } or .Name { stmts } (dotted)
partial def parseModuleBody : ParserM (Option Node) := do
  if (← currentToken) == .openBraceToken then do
    let bStart ← getTokenStart
    let _ ← nextToken
    let stmts ← parseList .closeBraceToken parseStatement
    let _ ← parseExpected .closeBraceToken
    let bNd ← makeNodeData bStart (← getPos)
    pure (some (.moduleBlock bNd stmts))
  else if (← currentToken) == .dotToken then
    -- Nested: module A.B.C { } → moduleDeclaration(A, moduleDeclaration(B, moduleDeclaration(C, block)))
    let _ ← nextToken
    let nestedStart ← getTokenStart
    let nestedName ← parseIdentifier
    let nestedBody ← parseModuleBody
    let nestedNd ← makeNodeData nestedStart (← getPos)
    pure (some (.moduleDeclaration nestedNd #[] nestedName nestedBody))
  else pure none

partial def parseModuleDeclaration (start : Nat) (mods : Array Modifier) : ParserM Node := do
  let _ ← nextToken  -- consume 'module' or 'namespace'
  let name ← if (← currentToken) == .stringLiteral then do
    let s ← getTokenStart; let v ← currentTokenValue; let _ ← nextToken
    let sNd ← makeNodeData s (← getPos)
    pure (.stringLiteral sNd v false)
  else parseIdentifier
  let body ← parseModuleBody
  let nd ← makeNodeData start (← getPos)
  return .moduleDeclaration nd mods name body

-- ====================== Import/Export ======================

partial def parseImportDeclaration : ParserM Node := do
  let start ← getTokenStart; let _ ← nextToken  -- consume 'import'
  -- import "module" (side-effect only)
  if (← currentToken) == .stringLiteral then
    let modSpec ← parseModuleSpecifier
    let _ ← parseSemicolon
    let nd ← makeNodeData start (← getPos)
    return .importDeclaration nd #[] none modSpec none
  -- import type { ... } from "module"
  let isTypeOnly ← if (← currentToken) == .typeKeyword then
    lookAhead do
      let _ ← nextToken
      let tok ← currentToken
      -- If followed by identifier, *, {, it's `import type ...`
      return tok == .identifier || tok == .asteriskToken || tok == .openBraceToken
  else pure false
  if isTypeOnly then let _ ← nextToken  -- consume 'type'
  -- import defaultBinding from "module"
  -- import * as ns from "module"
  -- import { a, b } from "module"
  -- import defaultBinding, { a, b } from "module"
  let clauseStart ← getTokenStart
  let name ← if (← currentToken) == .identifier then
    let isDefault ← lookAhead do
      let _ ← nextToken
      let tok ← currentToken
      return tok == .commaToken || tok == .fromKeyword
    if isDefault then some <$> parseIdentifier
    else pure none
  else pure none
  let namedBindings ← if name.isSome && (← parseOptional .commaToken) || name.isNone then
    some <$> parseNamedImportBindings
  else pure none
  let clauseNd ← makeNodeData clauseStart (← getPos)
  let clause := Node.importClause clauseNd isTypeOnly name namedBindings
  let _ ← parseExpected .fromKeyword
  let modSpec ← parseModuleSpecifier
  let _ ← parseSemicolon
  let nd ← makeNodeData start (← getPos)
  return .importDeclaration nd #[] (some clause) modSpec none

partial def parseNamedImportBindings : ParserM Node := do
  if (← currentToken) == .asteriskToken then
    let start ← getTokenStart; let _ ← nextToken
    let _ ← parseExpected .asKeyword
    let name ← parseIdentifier
    let nd ← makeNodeData start (← getPos)
    return .namespaceImport nd name
  else
    let start ← getTokenStart
    let _ ← parseExpected .openBraceToken
    let elements ← parseDelimitedList .closeBraceToken parseImportSpecifier
    let _ ← parseExpected .closeBraceToken
    let nd ← makeNodeData start (← getPos)
    return .namedImports nd elements

partial def parseImportSpecifier : ParserM Node := do
  let start ← getTokenStart
  let isTypeOnly ← if (← currentToken) == .typeKeyword then
    lookAhead do
      let _ ← nextToken
      return (← currentToken) == .identifier
  else pure false
  if isTypeOnly then let _ ← nextToken
  let nameOrProp ← parseIdentifierName
  let (propName, name) ← if (← parseOptional .asKeyword) then do
    let localName ← parseIdentifier
    pure (some nameOrProp, localName)
  else
    pure (none, nameOrProp)
  let nd ← makeNodeData start (← getPos)
  return .importSpecifier nd isTypeOnly propName name

partial def parseModuleSpecifier : ParserM Node := do
  let start ← getTokenStart
  let value ← currentTokenValue
  let _ ← parseExpected .stringLiteral
  let nd ← makeNodeData start (← getPos)
  return .stringLiteral nd value false

partial def parseExportDeclaration : ParserM Node := do
  let start ← getTokenStart; let _ ← nextToken  -- consume 'export'
  let tok ← currentToken
  -- export default expression
  if tok == .defaultKeyword then
    let _ ← nextToken
    if (← currentToken) == .functionKeyword then
      let funcStart ← getTokenStart
      let decl ← parseFunctionDeclaration funcStart #[]
      let nd ← makeNodeData start (← getPos)
      return .exportAssignment nd #[] false decl
    else if (← currentToken) == .classKeyword then
      let classStart ← getTokenStart
      let decl ← parseClassDeclaration classStart #[]
      let nd ← makeNodeData start (← getPos)
      return .exportAssignment nd #[] false decl
    else
      let expr ← parseAssignmentExpressionOrHigher
      let _ ← parseSemicolon
      let nd ← makeNodeData start (← getPos)
      return .exportAssignment nd #[] false expr
  -- export = expression (CommonJS)
  if tok == .equalsToken then
    let _ ← nextToken
    let expr ← parseAssignmentExpressionOrHigher
    let _ ← parseSemicolon
    let nd ← makeNodeData start (← getPos)
    return .exportAssignment nd #[] true expr
  -- export type { ... }
  let isTypeOnly ← if tok == .typeKeyword then
    lookAhead do
      let _ ← nextToken
      let t ← currentToken
      return t == .openBraceToken || t == .asteriskToken
  else pure false
  if isTypeOnly then let _ ← nextToken
  -- export * from "module"
  if (← currentToken) == .asteriskToken then
    let _ ← nextToken
    -- export * as ns from "module"
    let nsExport ← if (← parseOptional .asKeyword) then do
      let nsStart ← getTokenStart
      let nsName ← parseIdentifier
      let nsNd ← makeNodeData nsStart (← getPos)
      pure (some (.namespaceExport nsNd nsName))
    else pure none
    let _ ← parseExpected .fromKeyword
    let modSpec ← parseModuleSpecifier
    let _ ← parseSemicolon
    let nd ← makeNodeData start (← getPos)
    return .exportDeclaration nd #[] isTypeOnly nsExport (some modSpec) none
  -- export { a, b } from "module"  or  export { a, b }
  if (← currentToken) == .openBraceToken then
    let exStart ← getTokenStart
    let _ ← nextToken
    let elements ← parseDelimitedList .closeBraceToken parseExportSpecifier
    let _ ← parseExpected .closeBraceToken
    let exNd ← makeNodeData exStart (← getPos)
    let exportClause := Node.namedExports exNd elements
    let modSpec ← if (← parseOptional .fromKeyword) then some <$> parseModuleSpecifier else pure none
    let _ ← parseSemicolon
    let nd ← makeNodeData start (← getPos)
    return .exportDeclaration nd #[] isTypeOnly (some exportClause) modSpec none
  -- export declaration (function, class, var, let, const, interface, type, enum)
  -- Collect export as a modifier and parse the inner declaration
  let modNd ← makeNodeData start (← getPos)
  let exportMod : Modifier := { data := modNd, kind := .exportKeyword }
  parseDeclarationAfterModifiers start #[exportMod]

partial def parseExportSpecifier : ParserM Node := do
  let start ← getTokenStart
  let isTypeOnly ← if (← currentToken) == .typeKeyword then
    lookAhead do
      let _ ← nextToken
      return (← currentToken) == .identifier
  else pure false
  if isTypeOnly then let _ ← nextToken
  let nameOrProp ← parseIdentifierName
  let (propName, name) ← if (← parseOptional .asKeyword) then do
    let localName ← parseIdentifierName
    pure (some nameOrProp, localName)
  else
    pure (none, nameOrProp)
  let nd ← makeNodeData start (← getPos)
  return .exportSpecifier nd isTypeOnly propName name

-- ====================== Other parsing functions ======================

partial def parseObjectLiteralElement : ParserM Node := do
  let start ← getTokenStart
  let tok ← currentToken
  if tok == .dotDotDotToken then
    let _ ← nextToken
    let expr ← parseAssignmentExpressionOrHigher
    let nd ← makeNodeData start (← getPos)
    return .spreadAssignment nd expr
  -- get/set accessors
  else if tok == .getKeyword || tok == .setKeyword then
    let isAccessor ← lookAhead do
      let _ ← nextToken
      let t ← currentToken
      -- If followed by a property name token, it's an accessor
      return t == .identifier || t == .stringLiteral || t == .numericLiteral
        || t == .openBracketToken || t == .hashToken || isKeywordUsableAsIdentifier t
    if isAccessor then
      let _ ← nextToken  -- consume get/set
      let name ← parsePropertyName
      let _ ← parseExpected .openParenToken
      let params ← parseDelimitedList .closeParenToken parseParameterDeclaration
      let _ ← parseExpected .closeParenToken
      if tok == .getKeyword then
        let returnType ← if (← parseOptional .colonToken) then some <$> parseTypeNode else pure none
        let body ← if (← currentToken) == .openBraceToken then some <$> parseBlock else pure none
        let nd ← makeNodeData start (← getPos)
        return .getAccessor nd #[] name params returnType body
      else
        let body ← if (← currentToken) == .openBraceToken then some <$> parseBlock else pure none
        let nd ← makeNodeData start (← getPos)
        return .setAccessor nd #[] name params body
    else
      -- It's `get` or `set` used as a property name
      let name ← parsePropertyName
      let tok' ← currentToken
      if tok' == .colonToken then
        let _ ← nextToken
        let value ← parseAssignmentExpressionOrHigher
        let nd ← makeNodeData start (← getPos)
        return .propertyAssignment nd name false value
      else
        let nd ← makeNodeData start (← getPos)
        return .shorthandPropertyAssignment nd name none
  else if tok == .asteriskToken then
    -- Generator method: *name() { }
    let _ ← nextToken
    let name ← parsePropertyName
    let typeParams ← parseTypeParameters
    let _ ← parseExpected .openParenToken
    let params ← parseDelimitedList .closeParenToken parseParameterDeclaration
    let _ ← parseExpected .closeParenToken
    let returnType ← if (← parseOptional .colonToken) then some <$> parseTypeNode else pure none
    let body ← if (← currentToken) == .openBraceToken then some <$> parseBlock else pure none
    let nd ← makeNodeData start (← getPos)
    return .methodDeclaration nd #[] true name false typeParams params returnType body
  else
    let name ← parsePropertyName
    let tok' ← currentToken
    if tok' == .colonToken then
      let _ ← nextToken
      let value ← parseAssignmentExpressionOrHigher
      let nd ← makeNodeData start (← getPos)
      return .propertyAssignment nd name false value
    else if tok' == .openParenToken || tok' == .lessThanToken then
      let typeParams ← parseTypeParameters
      let _ ← parseExpected .openParenToken
      let params ← parseDelimitedList .closeParenToken parseParameterDeclaration
      let _ ← parseExpected .closeParenToken
      let returnType ← if (← parseOptional .colonToken) then some <$> parseTypeNode else pure none
      let body ← if (← currentToken) == .openBraceToken then some <$> parseBlock else pure none
      let nd ← makeNodeData start (← getPos)
      return .methodDeclaration nd #[] false name false typeParams params returnType body
    else
      let nd ← makeNodeData start (← getPos)
      return .shorthandPropertyAssignment nd name none

partial def parseNewExpression : ParserM Node := do
  let start ← getTokenStart; let _ ← nextToken
  let expr ← parsePrimaryExpression
  let expr ← parseMemberExpressionRest expr
  let args ← if (← currentToken) == .openParenToken then do
    let _ ← nextToken
    let a ← parseDelimitedList .closeParenToken parseSpreadOrAssignmentExpression
    let _ ← parseExpected .closeParenToken
    pure (some a)
  else pure none
  let nd ← makeNodeData start (← getPos)
  return .new_ nd expr none args

partial def parseTemplateExpression : ParserM Node := do
  let start ← getTokenStart
  let headValue ← currentTokenValue; let _ ← nextToken
  let headNd ← makeNodeData start (← getPos)
  let head := Node.noSubstitutionTemplate headNd headValue
  let mut spans : Array Node := #[]
  while (← currentToken) != .templateTail && (← currentToken) != .endOfFileToken do
    let spanStart ← getTokenStart
    let expr ← parseExpression
    let litStart ← getTokenStart
    let litValue ← currentTokenValue; let _ ← nextToken
    let litNd ← makeNodeData litStart (← getPos)
    let spanNd ← makeNodeData spanStart (← getPos)
    spans := spans.push (.templateSpan spanNd expr (.noSubstitutionTemplate litNd litValue))
  if (← currentToken) == .templateTail then let _ ← nextToken
  let nd ← makeNodeData start (← getPos)
  return .templateExpression nd head spans

-- ====================== Statement dispatcher ======================

-- Parse a declaration that follows modifier keywords.
-- `start` is the position of the first modifier (or the declaration keyword).
-- `mods` is the collected modifiers so far.
partial def parseDeclarationAfterModifiers (start : Nat) (mods : Array Modifier) : ParserM Node := do
  let tok ← currentToken
  match tok with
  | .varKeyword | .letKeyword => parseVariableStatement start mods
  | .constKeyword => do
    -- `const enum` case
    let isConstEnum ← lookAhead do
      let _ ← nextToken; return (← currentToken) == .enumKeyword
    if isConstEnum then
      let modStart ← getTokenStart
      let _ ← nextToken
      let modNd ← makeNodeData modStart (← getPos)
      let mods := mods.push { data := modNd, kind := .constKeyword }
      parseEnumDeclaration start mods
    else
      parseVariableStatement start mods
  | .functionKeyword => parseFunctionDeclaration start mods
  | .classKeyword => parseClassDeclaration start mods
  | .interfaceKeyword => parseInterfaceDeclaration start mods
  | .enumKeyword => parseEnumDeclaration start mods
  | .typeKeyword => do
    let isDecl ← lookAhead do
      let _ ← nextToken; return (← currentToken) == .identifier
    if isDecl then parseTypeAliasDeclaration start mods
    else parseExpressionOrLabeledStatement
  | .moduleKeyword | .namespaceKeyword => do
    let isDecl ← lookAhead do
      let _ ← nextToken
      let t ← currentToken
      return t == .identifier || t == .stringLiteral
    if isDecl then parseModuleDeclaration start mods
    else parseExpressionOrLabeledStatement
  | .abstractKeyword => do
    let modStart ← getTokenStart
    let _ ← nextToken
    let modNd ← makeNodeData modStart (← getPos)
    let mods := mods.push { data := modNd, kind := .abstractKeyword }
    parseDeclarationAfterModifiers start mods
  | .asyncKeyword => do
    let modStart ← getTokenStart
    let _ ← nextToken
    let modNd ← makeNodeData modStart (← getPos)
    let mods := mods.push { data := modNd, kind := .asyncKeyword }
    parseDeclarationAfterModifiers start mods
  | .declareKeyword => do
    let modStart ← getTokenStart
    let _ ← nextToken
    let modNd ← makeNodeData modStart (← getPos)
    let mods := mods.push { data := modNd, kind := .declareKeyword }
    parseDeclarationAfterModifiers start mods
  | .defaultKeyword => do
    -- `export default` case handled in parseExportDeclaration
    parseExpressionOrLabeledStatement
  | _ =>
    -- No declaration keyword found after modifiers; treat as expression statement
    parseExpressionOrLabeledStatement

partial def parseStatement : ParserM Node := do
  let tok ← currentToken
  match tok with
  | .openBraceToken => parseBlock
  | .varKeyword | .letKeyword | .constKeyword => do
    let start ← getTokenStart; parseVariableStatement start #[]
  | .functionKeyword => do
    let start ← getTokenStart; parseFunctionDeclaration start #[]
  | .classKeyword => do
    let start ← getTokenStart; parseClassDeclaration start #[]
  | .ifKeyword => parseIfStatement
  | .doKeyword => parseDoStatement
  | .whileKeyword => parseWhileStatement
  | .forKeyword => parseForStatement
  | .returnKeyword => parseReturnStatement
  | .switchKeyword => parseSwitchStatement
  | .throwKeyword => parseThrowStatement
  | .tryKeyword => parseTryStatement
  | .withKeyword => parseWithStatement
  | .debuggerKeyword => do
    let start ← getTokenStart; let _ ← nextToken; let _ ← parseSemicolon
    let nd ← makeNodeData start (← getPos); return .debuggerStatement nd
  | .breakKeyword => parseBreakOrContinueStatement .breakKeyword
  | .continueKeyword => parseBreakOrContinueStatement .continueKeyword
  | .semicolonToken => do
    let start ← getTokenStart; let _ ← nextToken
    let nd ← makeNodeData start (← getPos); return .emptyStatement nd
  | .atToken => do
    -- Decorator: @expression
    let start ← getTokenStart
    let decorators ← parseDecorators
    let mods := decorators.map fun d => Modifier.mk d.getData .atToken
    parseDeclarationAfterModifiers start mods
  -- Declaration keywords
  | .interfaceKeyword => do
    let start ← getTokenStart; parseInterfaceDeclaration start #[]
  | .enumKeyword => do
    let start ← getTokenStart; parseEnumDeclaration start #[]
  | .importKeyword => parseImportDeclaration
  | .exportKeyword => parseExportDeclaration
  -- Contextual keyword declarations
  | .typeKeyword => do
    let isDecl ← lookAhead do
      let _ ← nextToken
      let t ← currentToken
      return t == .identifier || isKeywordUsableAsIdentifier t
    if isDecl then do
      let start ← getTokenStart; parseTypeAliasDeclaration start #[]
    else parseExpressionOrLabeledStatement
  | .moduleKeyword | .namespaceKeyword => do
    let isDecl ← lookAhead do
      let _ ← nextToken
      let t ← currentToken
      return t == .identifier || t == .stringLiteral || isKeywordUsableAsIdentifier t
    if isDecl then do
      let start ← getTokenStart; parseModuleDeclaration start #[]
    else parseExpressionOrLabeledStatement
  | .abstractKeyword | .declareKeyword | .asyncKeyword => do
    let start ← getTokenStart
    parseDeclarationAfterModifiers start #[]
  | _ => parseExpressionOrLabeledStatement

-- Parse decorator list: @expr @expr ...
partial def parseDecorators : ParserM (Array Node) := do
  let mut decorators : Array Node := #[]
  while (← currentToken) == .atToken do
    let start ← getTokenStart
    let _ ← nextToken  -- consume @
    let expr ← parsePrimaryExpression
    let expr ← parseMemberExpressionRest expr
    -- Handle decorator call: @foo(args)
    let expr ← if (← currentToken) == .openParenToken then do
      let _ ← nextToken
      let args ← parseDelimitedList .closeParenToken parseSpreadOrAssignmentExpression
      let _ ← parseExpected .closeParenToken
      let callNd ← makeNodeData (expr.getData.range.pos.toNat) (← getPos)
      pure (.call callNd expr none args)
    else pure expr
    let nd ← makeNodeData start (← getPos)
    decorators := decorators.push (.decorator nd expr)
  return decorators

-- Parse an expression statement or a labeled statement (label: statement).
partial def parseExpressionOrLabeledStatement : ParserM Node := do
  let start ← getTokenStart
  let expr ← parseExpression
  -- Check for labeled statement: identifier ':'
  if (← currentToken) == .colonToken then
    match expr with
    | .identifier nd text =>
      let _ ← nextToken  -- consume ':'
      let stmt ← parseStatement
      let labelNd ← makeNodeData start (← getPos)
      return .labeledStatement labelNd (.identifier nd text) stmt
    | _ => pure ()
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
      let posBefore ← getPos
      statements := statements.push (← parseStatement)
      -- Guard against infinite loops: if parseStatement didn't advance, skip the token
      let posAfter ← getPos
      if posAfter == posBefore then
        let _ ← nextToken
    let endOfFile ← getTokenStart
    let eofNd ← makeNodeData endOfFile (← getPos)
    let nd ← makeNodeData start (← getPos)
    return .sourceFile nd fileName statements eofNd false
  match StateT.run action initialState with
  | .ok (node, state) => .ok (node, state.diagnostics)
  | .error e => .error e

end TSLean.Parser
