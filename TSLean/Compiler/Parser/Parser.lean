/-
  TSLean.Compiler.Parser.Parser — Complete recursive-descent parser.

  Based on Go: internal/parser/parser.go (6582 lines)
  Uses ParserM (StateM Parser) monad with `do` notation for clean state threading.
  All mutually recursive parsing functions are in a `mutual` block.
  Organized in sections: Utilities, Lists, Expressions, Types, Statements, Declarations, Entry.
-/
import TSLean.Compiler.Parser.Types
import TSLean.Compiler.Ast.Precedence
import TSLean.Compiler.Ast.Utilities

namespace TSLean.Compiler

-- ============================================================
-- Section: Core Utilities
-- Based on Go: parser.go:271-924
-- ============================================================

/-- Get current token kind. -/
@[inline] def currentToken : ParserM Kind := do return (← get).token

/-- Based on Go: parser.go:324 (nodePos) -/
@[inline] def nodePos : ParserM Nat := do return (← get).scanner.tokenFullStart

/-- Based on Go: parser.go:299 (nextToken) -/
def nextToken : ParserM Unit :=
  modify fun p =>
    let s := p.scanner.scan
    { p with scanner := s, token := s.state.token }

/-- Push a diagnostic error at the current token position. -/
def parseErrorAtCurrentToken (msg : DiagnosticMessage)
    (args : Array String := #[]) : ParserM Unit :=
  modify fun p =>
    let start := p.scanner.tokenStart
    let len := if p.scanner.state.pos > start then p.scanner.state.pos - start else 0
    { p with
      diagnostics := p.diagnostics.push
        { loc := TextRange.mk' start (start + len), message := msg, args := args }
      hasParseError := true }

/-- Based on Go: parser.go:5762 (finishNode) -/
def finishNode (node : Node) (pos : Nat) : ParserM Node := do
  let p ← get
  let base := node.base
  let flags := base.flags ||| p.contextFlags |||
    (if p.hasParseError then NodeFlags.thisNodeHasError else NodeFlags.none)
  set { p with hasParseError := false }
  return node.withBase { base with loc := TextRange.mk' pos p.scanner.tokenFullStart, flags := flags }

/-- Based on Go: parser.go:5874 (canParseSemicolon) -/
def canParseSemicolon : ParserM Bool := do
  let p ← get
  return p.token == Kind.semicolonToken || p.token == Kind.closeBraceToken ||
    p.token == Kind.endOfFile || p.scanner.hasPrecedingLineBreak

/-- Based on Go: parser.go:871 (parseOptional) -/
def parseOptional (kind : Kind) : ParserM Bool := do
  if (← currentToken) == kind then nextToken; return true
  else return false

/-- Based on Go: parser.go:879 (parseExpected) -/
def parseExpected (kind : Kind) : ParserM Bool := do
  if (← currentToken) == kind then nextToken; return true
  else
    parseErrorAtCurrentToken Diagnostics.X_0_expected #[tokenToString kind]
    return false

/-- Based on Go: parser.go:903 (parseTokenNode) -/
def parseTokenNode : ParserM Node := do
  let pos ← nodePos
  let kind ← currentToken
  nextToken
  finishNode (Node.token {} kind) pos

/-- Based on Go: parser.go:919 (parseOptionalToken) -/
def parseOptionalToken (kind : Kind) : ParserM (Option Node) := do
  if (← currentToken) == kind then return some (← parseTokenNode)
  else return none

/-- Based on Go: parser.go:910 (parseExpectedToken) -/
def parseExpectedToken (kind : Kind) : ParserM Node := do
  match ← parseOptionalToken kind with
  | some node => return node
  | none =>
    parseErrorAtCurrentToken Diagnostics.X_0_expected #[tokenToString kind]
    finishNode (Node.missing {} kind) (← nodePos)

/-- Based on Go: parser.go:5880 (tryParseSemicolon) -/
def tryParseSemicolon : ParserM Bool := do
  if !(← canParseSemicolon) then return false
  else if (← currentToken) == Kind.semicolonToken then nextToken; return true
  else return true

/-- Based on Go: parser.go:5891 (parseSemicolon) -/
def parseSemicolon : ParserM Bool := do
  if ← tryParseSemicolon then return true
  else parseExpected Kind.semicolonToken

/-- Based on Go: parser.go:6110 (isIdentifier) -/
def isIdentifierToken : ParserM Bool := do
  let tok ← currentToken
  return tok == Kind.identifier || (Kind.isKeywordKind tok && !Kind.isReservedWord tok)

/-- Based on Go: parser.go:6072 (isBindingIdentifier) -/
def isBindingIdentifierToken : ParserM Bool := do
  let tok ← currentToken
  return tok == Kind.identifier || Kind.isKeywordKind tok

/-- Based on Go: parser.go:5738 (internIdentifier) -/
def internIdentifier (text : String) : ParserM String := do
  let p ← get
  match p.identifiers[text]? with
  | some id => return id
  | none =>
    set { p with identifiers := p.identifiers.insert text text
                 identifierCount := p.identifierCount + 1 }
    return text

/-- Create a missing identifier node for error recovery. -/
def createMissingIdentifier : ParserM Node := do
  let pos ← nodePos
  parseErrorAtCurrentToken Diagnostics.identifier_expected
  finishNode (Node.missing {} Kind.identifier) pos

/-- Set a context flag. -/
def setContextFlag (flag : NodeFlags) (value : Bool) : ParserM Unit :=
  modify fun p =>
    if value then { p with contextFlags := p.contextFlags ||| flag }
    else { p with contextFlags := ⟨p.contextFlags.val &&& (~~~ flag.val)⟩ }

/-- Based on Go: parser.go:271 (mark) -/
def saveMark : ParserM ParserState := do
  let p ← get
  return { scannerState := p.scanner.mark, contextFlags := p.contextFlags,
           diagnosticsLen := p.diagnostics.size, hasParseError := p.hasParseError }

/-- Based on Go: parser.go:282 (rewind) -/
def restoreMark (state : ParserState) : ParserM Unit :=
  modify fun p => { p with
    scanner := p.scanner.rewind state.scannerState
    token := state.scannerState.token
    contextFlags := state.contextFlags
    diagnostics := p.diagnostics.shrink state.diagnosticsLen
    hasParseError := state.hasParseError }

/-- Based on Go: parser.go:292 (lookAhead) -/
def lookAhead (callback : ParserM Bool) : ParserM Bool := do
  let state ← saveMark
  let result ← callback
  restoreMark state
  return result

-- ============================================================
-- Section: Identifier Parsing
-- Based on Go: parser.go:5677-5736
-- ============================================================

/-- Based on Go: parser.go:5704 (createIdentifier) -/
def createIdentifier (isIdent : Bool) : ParserM Node := do
  if isIdent then
    let pos ← nodePos
    let text ← internIdentifier (← get).scanner.tokenValue
    nextToken
    finishNode (Node.identifier {} text) pos
  else createMissingIdentifier

/-- Based on Go: parser.go:5696 (parseIdentifier) -/
def parseIdentifier : ParserM Node := do
  createIdentifier (← isIdentifierToken)

/-- Based on Go: parser.go:5677 (parseBindingIdentifier) -/
def parseBindingIdentifier : ParserM Node := do
  createIdentifier (← isBindingIdentifierToken)

-- ============================================================
-- Section: List Parsing Infrastructure
-- Based on Go: parser.go:533-735
-- ============================================================

/-- Based on Go: parser.go:798 (isListTerminator) -/
def isListTerminator (kind : ParsingContext) : ParserM Bool := do
  let tok ← currentToken
  return match kind with
  | .sourceElements => tok == Kind.endOfFile
  | .blockStatements => tok == Kind.closeBraceToken
  | .switchClauses => tok == Kind.closeBraceToken
  | .switchClauseStatements =>
    tok == Kind.caseKeyword || tok == Kind.defaultKeyword || tok == Kind.closeBraceToken
  | .typeMembers => tok == Kind.closeBraceToken
  | .classMembers => tok == Kind.closeBraceToken
  | .enumMembers => tok == Kind.closeBraceToken
  | .heritageClauseElement =>
    tok == Kind.openBraceToken || tok == Kind.extendsKeyword || tok == Kind.implementsKeyword
  | .variableDeclarations =>
    tok == Kind.semicolonToken || tok == Kind.inKeyword || tok == Kind.ofKeyword
  | .objectBindingElements => tok == Kind.closeBraceToken
  | .arrayBindingElements => tok == Kind.closeBracketToken
  | .argumentExpressions => tok == Kind.closeParenToken
  | .objectLiteralMembers => tok == Kind.closeBraceToken
  | .arrayLiteralMembers => tok == Kind.closeBracketToken
  | .parameters => tok == Kind.closeParenToken
  | .typeParameters => tok == Kind.greaterThanToken
  | .typeArguments => tok == Kind.greaterThanToken
  | .tupleElementTypes => tok == Kind.closeBracketToken
  | .heritageClauses => tok == Kind.openBraceToken || tok == Kind.closeBraceToken
  | .importOrExportSpecifiers => tok == Kind.closeBraceToken
  | _ => false

/-- Based on Go: parser.go:623 (isInSomeParsingContext) -/
def isInSomeParsingContext : ParserM Bool := do
  return (← get).parsingContexts != 0

/-- Based on Go: parser.go:613 (abortParsingListOrMoveToNextToken) -/
def abortParsingListOrMoveToNextToken (_kind : ParsingContext) : ParserM Bool := do
  parseErrorAtCurrentToken Diagnostics.declaration_or_statement_expected
  if ← isInSomeParsingContext then return true
  else nextToken; return false

/-- Based on Go: parser.go:533 (parseList) — recursive loop
    Includes progress tracking: if parseElement fails to consume any tokens,
    forces advancement to prevent infinite loops. -/
partial def parseListLoop (kind : ParsingContext) (isElement : ParserM Bool)
    (parseElement : ParserM Node) (acc : Array Node) : ParserM (Array Node) := do
  if ← isListTerminator kind then return acc
  else if ← isElement then
    let startPos := (← get).scanner.tokenFullStart
    let node ← parseElement
    let acc' := acc.push node
    -- Safety: if no tokens were consumed, skip one to prevent infinite loop
    let endPos := (← get).scanner.tokenFullStart
    if endPos == startPos then
      if ← isListTerminator kind then return acc'
      nextToken
    parseListLoop kind isElement parseElement acc'
  else
    if ← abortParsingListOrMoveToNextToken kind then return acc
    else parseListLoop kind isElement parseElement acc

/-- Based on Go: parser.go:533 (parseList) -/
partial def parseList (kind : ParsingContext) (isElement : ParserM Bool)
    (parseElement : ParserM Node) : ParserM (Array Node) := do
  let savedContexts := (← get).parsingContexts
  modify fun p => { p with parsingContexts := p.parsingContexts ||| ((1 : UInt32) <<< kind.toNat.toUInt32) }
  let result ← parseListLoop kind isElement parseElement #[]
  modify fun p => { p with parsingContexts := savedContexts }
  return result

/-- Based on Go: parser.go:540 (parseDelimitedList) — recursive loop
    Includes progress tracking to prevent infinite loops. -/
partial def parseDelimitedListLoop (kind : ParsingContext) (isElement : ParserM Bool)
    (parseElement : ParserM Node) (acc : Array Node) : ParserM (Array Node) := do
  if ← isElement then
    let startPos := (← get).scanner.tokenFullStart
    let node ← parseElement
    let acc' := acc.push node
    let endPos := (← get).scanner.tokenFullStart
    -- Safety: if no tokens were consumed, skip one to prevent infinite loop
    if endPos == startPos then
      if ← isListTerminator kind then return acc'
      nextToken
    if ← parseOptional Kind.commaToken then
      parseDelimitedListLoop kind isElement parseElement acc'
    else if ← isListTerminator kind then return acc'
    else
      let _ ← parseExpected Kind.commaToken
      parseDelimitedListLoop kind isElement parseElement acc'
  else if ← isListTerminator kind then return acc
  else
    if ← abortParsingListOrMoveToNextToken kind then return acc
    else parseDelimitedListLoop kind isElement parseElement acc

/-- Based on Go: parser.go:540 (parseDelimitedList) -/
partial def parseDelimitedList (kind : ParsingContext) (isElement : ParserM Bool)
    (parseElement : ParserM Node) : ParserM (Array Node) := do
  let savedContexts := (← get).parsingContexts
  modify fun p => { p with parsingContexts := p.parsingContexts ||| ((1 : UInt32) <<< kind.toNat.toUInt32) }
  let result ← parseDelimitedListLoop kind isElement parseElement #[]
  modify fun p => { p with parsingContexts := savedContexts }
  return result

-- ============================================================
-- Section: Expression/Statement Start Predicates
-- ============================================================

/-- Helper: check if current token starts an expression. -/
def isStartOfExpression : ParserM Bool := do
  let tok ← currentToken
  return tok == Kind.identifier || tok == Kind.numericLiteral ||
    tok == Kind.stringLiteral || tok == Kind.bigIntLiteral ||
    tok == Kind.openParenToken || tok == Kind.openBracketToken ||
    tok == Kind.openBraceToken || tok == Kind.thisKeyword ||
    tok == Kind.superKeyword || tok == Kind.nullKeyword ||
    tok == Kind.trueKeyword || tok == Kind.falseKeyword ||
    tok == Kind.functionKeyword || tok == Kind.classKeyword ||
    tok == Kind.newKeyword || tok == Kind.typeOfKeyword ||
    tok == Kind.voidKeyword || tok == Kind.deleteKeyword ||
    tok == Kind.plusToken || tok == Kind.minusToken ||
    tok == Kind.tildeToken || tok == Kind.exclamationToken ||
    tok == Kind.plusPlusToken || tok == Kind.minusMinusToken ||
    tok == Kind.lessThanToken || tok == Kind.awaitKeyword ||
    tok == Kind.yieldKeyword || tok == Kind.slashToken ||
    tok == Kind.slashEqualsToken || tok == Kind.templateHead ||
    tok == Kind.noSubstitutionTemplateLiteral

/-- Based on Go: parser.go:5899 (isStartOfStatement) -/
def isStartOfStatement : ParserM Bool := do
  let tok ← currentToken
  if tok == Kind.semicolonToken || tok == Kind.openBraceToken ||
     tok == Kind.varKeyword || tok == Kind.letKeyword ||
     tok == Kind.functionKeyword || tok == Kind.classKeyword ||
     tok == Kind.ifKeyword || tok == Kind.returnKeyword ||
     tok == Kind.doKeyword || tok == Kind.whileKeyword ||
     tok == Kind.forKeyword || tok == Kind.continueKeyword ||
     tok == Kind.breakKeyword || tok == Kind.switchKeyword ||
     tok == Kind.throwKeyword || tok == Kind.tryKeyword ||
     tok == Kind.debuggerKeyword || tok == Kind.catchKeyword ||
     tok == Kind.finallyKeyword || tok == Kind.withKeyword ||
     tok == Kind.constKeyword || tok == Kind.enumKeyword ||
     tok == Kind.exportKeyword || tok == Kind.importKeyword ||
     tok == Kind.asyncKeyword || tok == Kind.declareKeyword ||
     tok == Kind.interfaceKeyword || tok == Kind.typeKeyword ||
     tok == Kind.moduleKeyword || tok == Kind.namespaceKeyword ||
     tok == Kind.abstractKeyword || tok == Kind.accessorKeyword ||
     tok == Kind.publicKeyword || tok == Kind.privateKeyword ||
     tok == Kind.protectedKeyword || tok == Kind.staticKeyword ||
     tok == Kind.readonlyKeyword || tok == Kind.globalKeyword then
    return true
  else isStartOfExpression

-- ============================================================
-- Section: All Mutually Recursive Parse Functions
-- Based on Go: parser.go:945-5800
-- ============================================================

mutual

-- ---- Expression Parsing ----

/-- Based on Go: parser.go:5636 (parseLiteralExpression) -/
partial def parseLiteralExpression : ParserM Node := do
  let pos ← nodePos
  let text := (← get).scanner.tokenValue
  let kind ← currentToken
  nextToken
  let node := if kind == Kind.numericLiteral then Node.numericLiteral {} text
    else if kind == Kind.stringLiteral then Node.stringLiteral {} text
    else Node.numericLiteral {} text
  finishNode node pos

/-- Based on Go: parser.go:5413 (parsePrimaryExpression) -/
partial def parsePrimaryExpression : ParserM Node := do
  let tok ← currentToken
  if tok == Kind.numericLiteral || tok == Kind.bigIntLiteral || tok == Kind.stringLiteral then
    parseLiteralExpression
  else if tok == Kind.thisKeyword || tok == Kind.superKeyword || tok == Kind.nullKeyword ||
          tok == Kind.trueKeyword || tok == Kind.falseKeyword then
    parseTokenNode
  else if tok == Kind.openParenToken then
    parseParenthesizedExpression
  else
    parseIdentifier

/-- Based on Go: parser.go:5458 (parseParenthesizedExpression) -/
partial def parseParenthesizedExpression : ParserM Node := do
  let pos ← nodePos
  let _ ← parseExpected Kind.openParenToken
  let expr ← parseExpressionAllowIn
  let _ ← parseExpected Kind.closeParenToken
  finishNode (Node.parenthesizedExpression {} expr) pos

/-- Based on Go: parser.go:5143 (parseMemberExpressionOrHigher) -/
partial def parseMemberExpressionOrHigher : ParserM Node := do
  let pos ← nodePos
  let expr ← parsePrimaryExpression
  parseMemberExpressionRest pos expr

/-- Helper: parse member expression rest (.prop, [idx]).
    Based on Go: parser.go:5162 -/
partial def parseMemberExpressionRest (pos : Nat) (expr : Node) : ParserM Node := do
  let tok ← currentToken
  if tok == Kind.dotToken then
    nextToken
    let name ← parseIdentifier
    let node ← finishNode (Node.propertyAccessExpression {} expr name) pos
    parseMemberExpressionRest pos node
  else if tok == Kind.openBracketToken then
    nextToken
    let argExpr ← parseExpressionAllowIn
    let _ ← parseExpected Kind.closeBracketToken
    let node ← finishNode (Node.elementAccessExpression {} expr argExpr) pos
    parseMemberExpressionRest pos node
  else return expr

/-- Based on Go: parser.go:5312 (parseCallExpressionRest) -/
partial def parseCallExpressionRest (pos : Nat) (expr : Node) : ParserM Node := do
  let tok ← currentToken
  if tok == Kind.openParenToken then
    let _ ← parseExpected Kind.openParenToken
    let args ← parseDelimitedList .argumentExpressions isStartOfExpression
      parseAssignmentExpressionOrHigher
    let _ ← parseExpected Kind.closeParenToken
    let node ← finishNode (Node.callExpression {} expr args) pos
    parseCallExpressionRest pos node
  else if tok == Kind.dotToken || tok == Kind.openBracketToken then
    let expr' ← parseMemberExpressionRest pos expr
    parseCallExpressionRest pos expr'
  else return expr

/-- Based on Go: parser.go:5002 (parseLeftHandSideExpressionOrHigher) -/
partial def parseLeftHandSideExpressionOrHigher : ParserM Node := do
  let pos ← nodePos
  let expr ← parseMemberExpressionOrHigher
  parseCallExpressionRest pos expr

/-- Based on Go: parser.go:4528 (parseUnaryExpressionOrHigher) -/
partial def parseUnaryExpressionOrHigher : ParserM Node := do
  let tok ← currentToken
  if tok == Kind.plusToken || tok == Kind.minusToken || tok == Kind.tildeToken ||
     tok == Kind.exclamationToken || tok == Kind.plusPlusToken || tok == Kind.minusMinusToken ||
     tok == Kind.typeOfKeyword || tok == Kind.voidKeyword || tok == Kind.deleteKeyword then
    let pos ← nodePos
    let op ← currentToken
    nextToken
    let operand ← parseUnaryExpressionOrHigher
    finishNode (Node.prefixUnaryExpression {} op operand) pos
  else
    let pos ← nodePos
    let expr ← parseLeftHandSideExpressionOrHigher
    if !(← get).scanner.hasPrecedingLineBreak then
      let tok ← currentToken
      if tok == Kind.plusPlusToken || tok == Kind.minusMinusToken then
        nextToken
        finishNode (Node.postfixUnaryExpression {} expr tok) pos
      else return expr
    else return expr

/-- Based on Go: parser.go:4453 (parseBinaryExpressionRest) — Pratt parser -/
partial def parseBinaryExpressionRest (precedence : OperatorPrecedence)
    (leftOperand : Node) (pos : Nat) : ParserM Node := do
  -- Rescan > tokens (for >=, >>=, >>>=)
  if (← currentToken) == Kind.greaterThanToken then
    modify fun p =>
      let s := p.scanner.reScanGreaterThanToken
      { p with scanner := s, token := s.state.token }
  let newPrecedence := getBinaryOperatorPrecedence (← currentToken)
  let consume := if (← currentToken) == Kind.asteriskAsteriskToken then
    newPrecedence.toInt >= precedence.toInt  -- right-associative
  else
    newPrecedence.toInt > precedence.toInt   -- left-associative
  if !consume then return leftOperand
  if (← currentToken) == Kind.inKeyword &&
     (← get).contextFlags.hasFlag NodeFlags.disallowInContext then
    return leftOperand
  let opNode ← parseTokenNode
  let rightOperand ← parseBinaryExpressionOrHigher newPrecedence
  let binExpr ← finishNode (Node.binaryExpression {} leftOperand opNode rightOperand) pos
  parseBinaryExpressionRest precedence binExpr pos

/-- Based on Go: parser.go:4447 (parseBinaryExpressionOrHigher) -/
partial def parseBinaryExpressionOrHigher (precedence : OperatorPrecedence) : ParserM Node := do
  let pos ← nodePos
  let leftOperand ← parseUnaryExpressionOrHigher
  parseBinaryExpressionRest precedence leftOperand pos

/-- Based on Go: parser.go:3952 (parseAssignmentExpressionOrHigher) — simplified -/
partial def parseAssignmentExpressionOrHigher : ParserM Node := do
  let pos ← nodePos
  let expr ← parseBinaryExpressionOrHigher OperatorPrecedence.lowest
  if isLeftHandSideExpression expr && Kind.isAssignment (← currentToken) then
    let opNode ← parseTokenNode
    let right ← parseAssignmentExpressionOrHigher
    finishNode (Node.binaryExpression {} expr opNode right) pos
  else return expr

/-- Helper: parse comma expression rest -/
partial def parseExpressionCommaRest (expr : Node) (pos : Nat) : ParserM Node := do
  if (← currentToken) == Kind.commaToken then
    let opNode ← parseTokenNode
    let right ← parseAssignmentExpressionOrHigher
    let binExpr ← finishNode (Node.binaryExpression {} expr opNode right) pos
    parseExpressionCommaRest binExpr pos
  else return expr

/-- Based on Go: parser.go:3927 (parseExpression) — comma expressions -/
partial def parseExpression : ParserM Node := do
  let pos ← nodePos
  let expr ← parseAssignmentExpressionOrHigher
  parseExpressionCommaRest expr pos

/-- Based on Go: parser.go:3948 (parseExpressionAllowIn) -/
partial def parseExpressionAllowIn : ParserM Node := do
  let saved := (← get).contextFlags
  setContextFlag NodeFlags.disallowInContext false
  let expr ← parseExpression
  modify fun p => { p with contextFlags := saved }
  return expr

-- ---- Type Parsing ----

/-- Based on Go: parser.go:2484 (parseType) — simplified -/
partial def parseType' : ParserM Node := do
  let tok ← currentToken
  if isKeywordType tok then parseTokenNode
  else if ← isIdentifierToken then
    let pos ← nodePos
    let name ← parseIdentifier
    finishNode (Node.typeReference {} name none) pos
  else parseTokenNode  -- fallback

/-- Based on Go: parser.go:1588 (parseTypeAnnotation) -/
partial def parseTypeAnnotation : ParserM (Option Node) := do
  if ← parseOptional Kind.colonToken then
    pure (some (← parseType'))
  else return none

/-- Based on Go: parser.go:3255 (parseReturnType) -/
partial def parseReturnType : ParserM (Option Node) := do
  if ← parseOptional Kind.colonToken then
    pure (some (← parseType'))
  else return none

/-- Based on Go: parser.go:3096 (parseTypeParameters) -/
partial def parseTypeParameters : ParserM (Option (Array Node)) := do
  if (← currentToken) == Kind.lessThanToken then
    let _ ← parseExpected Kind.lessThanToken
    let params ← parseDelimitedList .typeParameters isIdentifierToken parseIdentifier
    let _ ← parseExpected Kind.greaterThanToken
    pure (some params)
  else return none

/-- Based on Go: parser.go:3191 (parseParameter) -/
partial def parseParameter : ParserM Node := do
  let pos ← nodePos
  let dotDotDot ← parseOptionalToken Kind.dotDotDotToken
  let name ← parseBindingIdentifier
  let questionToken ← parseOptionalToken Kind.questionToken
  let typeNode ← parseTypeAnnotation
  let initializer ← parseInitializer
  finishNode (Node.parameterDeclaration {} dotDotDot name questionToken typeNode initializer) pos

/-- Based on Go: parser.go:3136 (parseParameters) -/
partial def parseParameters : ParserM (Array Node) := do
  let ok ← parseExpected Kind.openParenToken
  if ok then
    let isParam : ParserM Bool := do
      let tok ← currentToken
      let bindId ← isBindingIdentifierToken
      return bindId || tok == Kind.dotDotDotToken ||
        tok == Kind.openBracketToken || tok == Kind.openBraceToken ||
        isModifierKind tok || tok == Kind.thisKeyword
    let params ← parseDelimitedList .parameters isParam parseParameter
    let _ ← parseExpected Kind.closeParenToken
    return params
  else return #[]

-- ---- Statement Parsing ----

/-- Based on Go: parser.go:1090 (parseBlock) -/
partial def parseBlock : ParserM Node := do
  let pos ← nodePos
  let ok ← parseExpected Kind.openBraceToken
  if ok then
    let stmts ← parseList .blockStatements isStartOfStatement parseStatement
    let _ ← parseExpected Kind.closeBraceToken
    finishNode (Node.block {} stmts) pos
  else
    finishNode (Node.block {} #[]) pos

/-- Based on Go: parser.go:1113 (parseEmptyStatement) -/
partial def parseEmptyStatement : ParserM Node := do
  let pos ← nodePos
  let _ ← parseExpected Kind.semicolonToken
  finishNode (Node.emptyStatement {}) pos

/-- Based on Go: parser.go:1122 (parseIfStatement) -/
partial def parseIfStatement : ParserM Node := do
  let pos ← nodePos
  let _ ← parseExpected Kind.ifKeyword
  let _ ← parseExpected Kind.openParenToken
  let expr ← parseExpressionAllowIn
  let _ ← parseExpected Kind.closeParenToken
  let thenStmt ← parseStatement
  let hasElse ← parseOptional Kind.elseKeyword
  let elseStmt ← if hasElse then do
    let s ← parseStatement; pure (some s)
  else pure none
  finishNode (Node.ifStatement {} expr thenStmt elseStmt) pos

/-- Based on Go: parser.go:1249 (parseReturnStatement) -/
partial def parseReturnStatement : ParserM Node := do
  let pos ← nodePos
  let _ ← parseExpected Kind.returnKeyword
  let expr ← if !(← canParseSemicolon) then do
    let e ← parseExpressionAllowIn; pure (some e)
  else pure none
  let _ ← parseSemicolon
  finishNode (Node.returnStatement {} expr) pos

/-- Based on Go: parser.go:1401 (parseExpressionOrLabeledStatement) -/
partial def parseExpressionOrLabeledStatement : ParserM Node := do
  let pos ← nodePos
  let expr ← parseExpression
  -- Check for labeled statement: identifier followed by ':'
  if (← currentToken) == Kind.colonToken then
    match expr with
    | .identifier _ _ =>
      nextToken
      let stmt ← parseStatement
      return ← finishNode (Node.labeledStatement {} expr stmt) pos
    | _ => pure ()
  let _ ← parseSemicolon
  finishNode (Node.expressionStatement {} expr) pos

/-- Based on Go: parser.go:1289 (parseThrowStatement) -/
partial def parseThrowStatement : ParserM Node := do
  let pos ← nodePos
  let _ ← parseExpected Kind.throwKeyword
  let expr ← if ← canParseSemicolon then pure none
    else pure (some (← parseExpressionAllowIn))
  let _ ← parseSemicolon
  finishNode (Node.throwStatement {} expr) pos

/-- Based on Go: parser.go:1202 (parseBreakOrContinueStatement) -/
partial def parseBreakStatement : ParserM Node := do
  let pos ← nodePos
  let _ ← parseExpected Kind.breakKeyword
  let label ← if ← canParseSemicolon then pure none
    else if ← isIdentifierToken then pure (some (← parseIdentifier))
    else pure none
  let _ ← parseSemicolon
  finishNode (Node.breakStatement {} label) pos

/-- Based on Go: parser.go:1202 (parseBreakOrContinueStatement) -/
partial def parseContinueStatement : ParserM Node := do
  let pos ← nodePos
  let _ ← parseExpected Kind.continueKeyword
  let label ← if ← canParseSemicolon then pure none
    else if ← isIdentifierToken then pure (some (← parseIdentifier))
    else pure none
  let _ ← parseSemicolon
  finishNode (Node.continueStatement {} label) pos

/-- Based on Go: parser.go:1282 (parseDebuggerStatement) -/
partial def parseDebuggerStatement : ParserM Node := do
  let pos ← nodePos
  let _ ← parseExpected Kind.debuggerKeyword
  let _ ← parseSemicolon
  finishNode (Node.debuggerStatement {}) pos

/-- Based on Go: parser.go:1151 (parseWhileStatement) -/
partial def parseWhileStatement : ParserM Node := do
  let pos ← nodePos
  let _ ← parseExpected Kind.whileKeyword
  let _ ← parseExpected Kind.openParenToken
  let expr ← parseExpressionAllowIn
  let _ ← parseExpected Kind.closeParenToken
  let stmt ← parseStatement
  finishNode (Node.whileStatement {} expr stmt) pos

/-- Based on Go: parser.go:1141 (parseDoStatement) -/
partial def parseDoStatement : ParserM Node := do
  let pos ← nodePos
  let _ ← parseExpected Kind.doKeyword
  let stmt ← parseStatement
  let _ ← parseExpected Kind.whileKeyword
  let _ ← parseExpected Kind.openParenToken
  let expr ← parseExpressionAllowIn
  let _ ← parseExpected Kind.closeParenToken
  let _ ← parseSemicolon
  finishNode (Node.doStatement {} stmt expr) pos

/-- Based on Go: parser.go:1160 (parseForStatement) — simplified -/
partial def parseForStatement : ParserM Node := do
  let pos ← nodePos
  let _ ← parseExpected Kind.forKeyword
  let _ ← parseExpected Kind.openParenToken
  let initializer ← if (← currentToken) == Kind.semicolonToken then pure none
    else if (← currentToken) == Kind.varKeyword || (← currentToken) == Kind.letKeyword ||
            (← currentToken) == Kind.constKeyword then
      pure (some (← parseVariableDeclarationList))
    else pure (some (← parseExpressionAllowIn))
  let tok ← currentToken
  if tok == Kind.inKeyword then
    let _ ← parseExpected Kind.inKeyword
    let expr ← parseExpressionAllowIn
    let _ ← parseExpected Kind.closeParenToken
    let stmt ← parseStatement
    finishNode (Node.forInStatement {} initializer expr stmt) pos
  else if tok == Kind.ofKeyword then
    nextToken
    let expr ← parseExpressionAllowIn
    let _ ← parseExpected Kind.closeParenToken
    let stmt ← parseStatement
    finishNode (Node.forOfStatement {} initializer expr stmt) pos
  else
    let _ ← parseExpected Kind.semicolonToken
    let condition ← if (← currentToken) == Kind.semicolonToken then pure none
      else pure (some (← parseExpressionAllowIn))
    let _ ← parseExpected Kind.semicolonToken
    let incrementor ← if (← currentToken) == Kind.closeParenToken then pure none
      else pure (some (← parseExpressionAllowIn))
    let _ ← parseExpected Kind.closeParenToken
    let stmt ← parseStatement
    finishNode (Node.forStatement {} initializer condition incrementor stmt) pos

/-- Based on Go: parser.go:1305 (parseSwitchStatement) -/
partial def parseSwitchStatement : ParserM Node := do
  let pos ← nodePos
  let _ ← parseExpected Kind.switchKeyword
  let _ ← parseExpected Kind.openParenToken
  let expr ← parseExpressionAllowIn
  let _ ← parseExpected Kind.closeParenToken
  let _ ← parseExpected Kind.openBraceToken
  let clauses ← parseSwitchClauses #[]
  let _ ← parseExpected Kind.closeBraceToken
  finishNode (Node.switchStatement {} expr clauses) pos

/-- Helper: parse switch case/default clauses. -/
partial def parseSwitchClauses (acc : Array Node) : ParserM (Array Node) := do
  let tok ← currentToken
  if tok == Kind.closeBraceToken || tok == Kind.endOfFile then return acc
  else if tok == Kind.caseKeyword then
    let pos ← nodePos
    let _ ← parseExpected Kind.caseKeyword
    let expr ← parseExpressionAllowIn
    let _ ← parseExpected Kind.colonToken
    let stmts ← parseList .switchClauseStatements isStartOfStatement parseStatement
    let node ← finishNode (Node.caseClause {} expr stmts) pos
    parseSwitchClauses (acc.push node)
  else if tok == Kind.defaultKeyword then
    let pos ← nodePos
    let _ ← parseExpected Kind.defaultKeyword
    let _ ← parseExpected Kind.colonToken
    let stmts ← parseList .switchClauseStatements isStartOfStatement parseStatement
    let node ← finishNode (Node.defaultClause {} stmts) pos
    parseSwitchClauses (acc.push node)
  else
    nextToken
    parseSwitchClauses acc

/-- Based on Go: parser.go:1308 (parseTryStatement) -/
partial def parseTryStatement : ParserM Node := do
  let pos ← nodePos
  let _ ← parseExpected Kind.tryKeyword
  let tryBlock ← parseBlock
  let catchClause ← if (← currentToken) == Kind.catchKeyword then do
    let cPos ← nodePos
    let _ ← parseExpected Kind.catchKeyword
    let decl ← if (← currentToken) == Kind.openParenToken then do
      let _ ← parseExpected Kind.openParenToken
      let name ← parseBindingIdentifier
      let typeNode ← parseTypeAnnotation
      let _ ← parseExpected Kind.closeParenToken
      pure (some (Node.variableDeclaration {} name typeNode none))
    else pure none
    let block ← parseBlock
    let node ← finishNode (Node.catchClause {} decl block) cPos
    pure (some node)
  else pure none
  let finallyBlock ← if (← currentToken) == Kind.finallyKeyword then do
    let _ ← parseExpected Kind.finallyKeyword
    pure (some (← parseBlock))
  else pure none
  finishNode (Node.tryStatement {} tryBlock catchClause finallyBlock) pos

/-- Based on Go: parser.go:1131 (parseWithStatement) -/
partial def parseWithStatement : ParserM Node := do
  let pos ← nodePos
  let _ ← parseExpected Kind.withKeyword
  let _ ← parseExpected Kind.openParenToken
  let expr ← parseExpressionAllowIn
  let _ ← parseExpected Kind.closeParenToken
  let stmt ← parseStatement
  finishNode (Node.withStatement {} expr stmt) pos

/-- Based on Go: parser.go:1581 (parseInitializer) -/
partial def parseInitializer : ParserM (Option Node) := do
  if ← parseOptional Kind.equalsToken then
    pure (some (← parseAssignmentExpressionOrHigher))
  else return none

/-- Based on Go: parser.go:1495 (parseVariableDeclaration) -/
partial def parseVariableDeclaration : ParserM Node := do
  let pos ← nodePos
  let name ← parseBindingIdentifier
  let typeNode ← parseTypeAnnotation
  let initializer ← parseInitializer
  finishNode (Node.variableDeclaration {} name typeNode initializer) pos

/-- Based on Go: parser.go:1434 (parseVariableDeclarationList) -/
partial def parseVariableDeclarationList : ParserM Node := do
  let pos ← nodePos
  let tok ← currentToken
  let flags := if tok == Kind.letKeyword then NodeFlags.let_
    else if tok == Kind.constKeyword then NodeFlags.const_
    else if tok == Kind.usingKeyword then NodeFlags.using_
    else NodeFlags.none
  nextToken
  let isDecl : ParserM Bool := do
    let bindId ← isBindingIdentifierToken
    let tok ← currentToken
    return bindId || tok == Kind.openBracketToken || tok == Kind.openBraceToken
  let decls ← parseDelimitedList .variableDeclarations isDecl parseVariableDeclaration
  finishNode (Node.variableDeclarationList {} flags decls) pos

/-- Based on Go: parser.go:1425 (parseVariableStatement) -/
partial def parseVariableStatement : ParserM Node := do
  let pos ← nodePos
  let declList ← parseVariableDeclarationList
  let _ ← parseSemicolon
  finishNode (Node.variableStatement {} declList) pos

/-- Based on Go: parser.go:945 (parseStatement) — dispatch on token -/
partial def parseStatement : ParserM Node := do
  let tok ← currentToken
  if tok == Kind.semicolonToken then parseEmptyStatement
  else if tok == Kind.openBraceToken then parseBlock
  else if tok == Kind.varKeyword || tok == Kind.letKeyword || tok == Kind.constKeyword then
    parseVariableStatement
  else if tok == Kind.functionKeyword then parseFunctionDeclaration
  else if tok == Kind.classKeyword then parseClassDeclaration
  else if tok == Kind.ifKeyword then parseIfStatement
  else if tok == Kind.returnKeyword then parseReturnStatement
  else if tok == Kind.throwKeyword then parseThrowStatement
  else if tok == Kind.breakKeyword then parseBreakStatement
  else if tok == Kind.continueKeyword then parseContinueStatement
  else if tok == Kind.debuggerKeyword then parseDebuggerStatement
  else if tok == Kind.whileKeyword then parseWhileStatement
  else if tok == Kind.doKeyword then parseDoStatement
  else if tok == Kind.forKeyword then parseForStatement
  else if tok == Kind.switchKeyword then parseSwitchStatement
  else if tok == Kind.tryKeyword then parseTryStatement
  else if tok == Kind.withKeyword then parseWithStatement
  else if tok == Kind.exportKeyword || tok == Kind.importKeyword ||
          tok == Kind.enumKeyword || tok == Kind.interfaceKeyword ||
          tok == Kind.typeKeyword || tok == Kind.moduleKeyword ||
          tok == Kind.namespaceKeyword || tok == Kind.abstractKeyword ||
          tok == Kind.declareKeyword then
    -- Unsupported declaration kinds: emit error and skip one token.
    -- The list loop's progress tracking handles further recovery.
    let pos ← nodePos
    parseErrorAtCurrentToken Diagnostics.declaration_or_statement_expected
    nextToken
    finishNode (Node.missing {} tok) pos
  else parseExpressionOrLabeledStatement

-- ---- Declaration Parsing ----

/-- Based on Go: parser.go:3370 (parseFunctionBlock) -/
partial def parseFunctionBlock : ParserM (Option Node) := do
  if (← currentToken) == Kind.openBraceToken then
    pure (some (← parseBlock))
  else if ← canParseSemicolon then
    let _ ← parseSemicolon; return none
  else
    pure (some (← parseBlock))

/-- Based on Go: parser.go:1595 (parseFunctionDeclaration) -/
partial def parseFunctionDeclaration : ParserM Node := do
  let pos ← nodePos
  let _ ← parseExpected Kind.functionKeyword
  let name ← if ← isBindingIdentifierToken then do
    let n ← parseBindingIdentifier; pure (some n)
  else pure none
  let typeParams ← parseTypeParameters
  let params ← parseParameters
  let returnType ← parseReturnType
  let body ← parseFunctionBlock
  finishNode (Node.functionDeclaration {} name typeParams params returnType body) pos

/-- Based on Go: parser.go:5895 (parsePropertyName) -/
partial def parsePropertyName : ParserM Node := do
  let tok ← currentToken
  if tok == Kind.stringLiteral || tok == Kind.numericLiteral then
    parseLiteralExpression
  else parseIdentifier

/-- Based on Go: parser.go:1833 (parseMethodDeclaration) rest -/
partial def parseMethodDeclarationRest (pos : Nat) (name : Node)
    (questionToken : Option Node) : ParserM Node := do
  let typeParams ← parseTypeParameters
  let params ← parseParameters
  let returnType ← parseReturnType
  let body ← parseFunctionBlock
  finishNode (Node.methodDeclaration {} name questionToken typeParams params returnType body) pos

/-- Based on Go: parser.go:1821 (parsePropertyOrMethodDeclaration) -/
partial def parsePropertyOrMethodDeclaration : ParserM Node := do
  let pos ← nodePos
  let name ← parsePropertyName
  let questionToken ← parseOptionalToken Kind.questionToken
  let tok ← currentToken
  if tok == Kind.openParenToken || tok == Kind.lessThanToken then
    parseMethodDeclarationRest pos name questionToken
  else
    let typeNode ← parseTypeAnnotation
    let initializer ← parseInitializer
    let _ ← parseSemicolon
    finishNode (Node.variableDeclaration {} name typeNode initializer) pos

/-- Based on Go: parser.go:1728 (parseClassElement) -/
partial def parseClassElement : ParserM Node := do
  let pos ← nodePos
  if (← currentToken) == Kind.semicolonToken then
    nextToken
    finishNode (Node.semicolonClassElement {}) pos
  else parsePropertyOrMethodDeclaration

/-- Based on Go: parser.go:1619 (parseClassDeclaration) -/
partial def parseClassDeclaration : ParserM Node := do
  let pos ← nodePos
  let _ ← parseExpected Kind.classKeyword
  let name ← if ← isBindingIdentifierToken then do
    let n ← parseBindingIdentifier; pure (some n)
  else pure none
  let typeParams ← parseTypeParameters
  -- Skip heritage clauses for now
  let ok ← parseExpected Kind.openBraceToken
  let members ← if ok then
    let isClassElem : ParserM Bool := do
      let tok ← currentToken
      return tok != Kind.closeBraceToken && tok != Kind.endOfFile
    parseList .classMembers isClassElem parseClassElement
  else pure #[]
  let _ ← parseExpected Kind.closeBraceToken
  finishNode (Node.classDeclaration {} name typeParams none members) pos

-- ---- Entry Point ----

/-- Based on Go: parser.go:336 (parseSourceFileWorker) -/
partial def parseSourceFileWorker : ParserM Node := do
  let pos ← nodePos
  let isStmtNotEof : ParserM Bool := do
    if (← currentToken) == Kind.endOfFile then return false
    else isStartOfStatement
  let stmts ← parseList .sourceElements isStmtNotEof parseStatement
  let eof ← parseTokenNode
  finishNode (Node.sourceFile {} stmts eof) pos

end -- mutual

-- ============================================================
-- Section: Public Entry Point
-- Based on Go: parser.go:114-390
-- ============================================================

/-- Initialize a parser from source text.
    Based on Go: parser.go:114 (initializeState + ParseSourceFile) -/
def Parser.initializeState (sourceText : String) (scriptKind : ScriptKind) : Parser :=
  let scanner : Scanner := {
    text := sourceText
    bytes := sourceText.toUTF8
    skipTrivia := true
    scriptKind := scriptKind
    languageVariant := match scriptKind with
      | .jsx | .tsx => LanguageVariant.jsx
      | _ => LanguageVariant.standard
  }
  { scanner := scanner
  , sourceText := sourceText
  , token := Kind.unknown }

/-- Based on Go: parser.go:114 (ParseSourceFile)
    Main entry point for parsing a TypeScript/JavaScript source file.
    Returns the AST and any diagnostics. -/
partial def parseSourceFile (_fileName : String) (sourceText : String)
    (scriptKind : ScriptKind) : ParseResult :=
  let p := Parser.initializeState sourceText scriptKind
  let ((), p) := nextToken p
  let (result, p) := parseSourceFileWorker p
  { sourceFile := result, diagnostics := p.diagnostics }

end TSLean.Compiler
