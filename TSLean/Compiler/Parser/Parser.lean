/-
  TSLean.Compiler.Parser.Parser — Complete recursive-descent parser.

  Based on Go: internal/parser/parser.go (6582 lines)
  Uses ParserM (StateM Parser) monad with `do` notation for clean state threading.
  All mutually recursive parsing functions are in a `partial mutual` block.
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
partial def nextToken : ParserM Unit :=
  modify fun p =>
    let s := p.scanner.scan
    { p with scanner := s, token := s.state.token }

/-- Push a diagnostic error at the current token position. -/
partial def parseErrorAtCurrentToken (msg : DiagnosticMessage)
    (args : Array String := #[]) : ParserM Unit :=
  modify fun p =>
    let start := p.scanner.tokenStart
    let len := if p.scanner.state.pos > start then p.scanner.state.pos - start else 0
    { p with
      diagnostics := p.diagnostics.push
        { loc := TextRange.mk' start (start + len), message := msg, args := args }
      hasParseError := true }

/-- Based on Go: parser.go:5762 (finishNode) -/
partial def finishNode (node : Node) (pos : Nat) : ParserM Node := do
  let p ← get
  let base := node.base
  let flags := base.flags ||| p.contextFlags |||
    (if p.hasParseError then NodeFlags.thisNodeHasError else NodeFlags.none)
  set { p with hasParseError := false }
  return node.withBase { base with loc := TextRange.mk' pos p.scanner.tokenFullStart, flags := flags }

/-- Based on Go: parser.go:5874 (canParseSemicolon) -/
partial def canParseSemicolon : ParserM Bool := do
  let p ← get
  return p.token == Kind.semicolonToken || p.token == Kind.closeBraceToken ||
    p.token == Kind.endOfFile || p.scanner.hasPrecedingLineBreak

/-- Based on Go: parser.go:871 (parseOptional) -/
partial def parseOptional (kind : Kind) : ParserM Bool := do
  if (← currentToken) == kind then nextToken; return true
  else return false

/-- Based on Go: parser.go:879 (parseExpected) -/
partial def parseExpected (kind : Kind) : ParserM Bool := do
  if (← currentToken) == kind then nextToken; return true
  else
    parseErrorAtCurrentToken Diagnostics.X_0_expected #[tokenToString kind]
    return false

/-- Based on Go: parser.go:903 (parseTokenNode) -/
partial def parseTokenNode : ParserM Node := do
  let pos ← nodePos
  let kind ← currentToken
  nextToken
  finishNode (Node.token {} kind) pos

/-- Based on Go: parser.go:919 (parseOptionalToken) -/
partial def parseOptionalToken (kind : Kind) : ParserM (Option Node) := do
  if (← currentToken) == kind then return some (← parseTokenNode)
  else return none

/-- Based on Go: parser.go:910 (parseExpectedToken) -/
partial def parseExpectedToken (kind : Kind) : ParserM Node := do
  match ← parseOptionalToken kind with
  | some node => return node
  | none =>
    parseErrorAtCurrentToken Diagnostics.X_0_expected #[tokenToString kind]
    finishNode (Node.missing {} kind) (← nodePos)

/-- Based on Go: parser.go:5880 (tryParseSemicolon) -/
partial def tryParseSemicolon : ParserM Bool := do
  if !(← canParseSemicolon) then return false
  else match (← currentToken) with
    | .semicolonToken => nextToken; return true
    | _ => return true

/-- Based on Go: parser.go:5912 (parseTypeMemberSemicolon)
    Type members allow both `;` and `,` as separators. -/
partial def parseTypeMemberSemicolon : ParserM Unit := do
  match (← currentToken) with
  | .commaToken => nextToken
  | _ => let _ ← tryParseSemicolon

/-- Based on Go: parser.go:5891 (parseSemicolon) -/
partial def parseSemicolon : ParserM Bool := do
  if ← tryParseSemicolon then return true
  else parseExpected Kind.semicolonToken

/-- Based on Go: parser.go:6110 (isIdentifier) -/
partial def isIdentifierToken : ParserM Bool := do
  let tok ← currentToken
  return tok == Kind.identifier || (Kind.isKeywordKind tok && !Kind.isReservedWord tok)

/-- Based on Go: parser.go:6072 (isBindingIdentifier) -/
partial def isBindingIdentifierToken : ParserM Bool := do
  let tok ← currentToken
  return tok == Kind.identifier || Kind.isKeywordKind tok

/-- Based on Go: parser.go:5738 (internIdentifier) -/
partial def internIdentifier (text : String) : ParserM String := do
  let p ← get
  match p.identifiers[text]? with
  | some id => return id
  | none =>
    set { p with identifiers := p.identifiers.insert text text
                 identifierCount := p.identifierCount + 1 }
    return text

/-- Create a missing identifier node for error recovery. -/
partial def createMissingIdentifier : ParserM Node := do
  let pos ← nodePos
  parseErrorAtCurrentToken Diagnostics.identifier_expected
  finishNode (Node.missing {} Kind.identifier) pos

/-- Set a context flag. -/
partial def setContextFlag (flag : NodeFlags) (value : Bool) : ParserM Unit :=
  modify fun p =>
    if value then { p with contextFlags := p.contextFlags ||| flag }
    else { p with contextFlags := ⟨p.contextFlags.val &&& (~~~ flag.val)⟩ }

/-- Based on Go: parser.go:292 (lookAhead) -/
partial def lookAhead (callback : ParserM Bool) : ParserM Bool := do
  let saved ← get
  let result ← callback
  set saved
  return result

/-- Based on Go: parser.go:2865 (reScanLessThanToken) -/
partial def reScanLessThanToken : ParserM Kind := do
  modify fun p =>
    let s := p.scanner.reScanLessThanToken
    { p with scanner := s, token := s.state.token }
  currentToken

/-- Based on Go: parser.go:2875 (reScanGreaterThanToken) -/
partial def reScanGreaterThanToken : ParserM Kind := do
  modify fun p =>
    let s := p.scanner.reScanGreaterThanToken
    { p with scanner := s, token := s.state.token }
  currentToken

/-- Based on Go: parser.go:2880 (reScanTemplateToken) -/
partial def reScanTemplateToken (isTaggedTemplate : Bool) : ParserM Kind := do
  modify fun p =>
    let s := p.scanner.reScanTemplateToken isTaggedTemplate
    { p with scanner := s, token := s.state.token }
  currentToken

-- ============================================================
-- Section: Identifier Parsing
-- Based on Go: parser.go:5677-5736
-- ============================================================

/-- Based on Go: parser.go:5704 (createIdentifier) -/
partial def createIdentifier (isIdent : Bool) : ParserM Node := do
  if isIdent then
    let pos ← nodePos
    let text ← internIdentifier (← get).scanner.tokenValue
    nextToken
    finishNode (Node.identifier {} text) pos
  else createMissingIdentifier

/-- Based on Go: parser.go:5696 (parseIdentifier) -/
partial def parseIdentifier : ParserM Node := do
  createIdentifier (← isIdentifierToken)

/-- Based on Go: parser.go:5677 (parseBindingIdentifier) -/
partial def parseBindingIdentifier : ParserM Node := do
  createIdentifier (← isBindingIdentifierToken)

/-- Parse an identifier or keyword (for import/export specifiers). -/
partial def parseIdentifierName : ParserM Node := do
  let tok ← currentToken
  if tok == Kind.identifier || Kind.isKeywordKind tok then
    let pos ← nodePos
    let text ← internIdentifier (← get).scanner.tokenValue
    nextToken
    finishNode (Node.identifier {} text) pos
  else createMissingIdentifier

-- ============================================================
-- Section: Loop Combinator
-- ============================================================

/-- Append a trace message (only when debug is enabled). -/
@[inline] def traceMsg (msg : String) : ParserM Unit :=
  modify fun p =>
    if p.debug then { p with traceLog := p.traceLog.push msg } else p

-- ============================================================
-- Section: List Parsing Infrastructure
-- Based on Go: parser.go:533-735
-- ============================================================

/-- Based on Go: parser.go:798 (isListTerminator) -/
partial def isListTerminator (kind : ParsingContext) : ParserM Bool := do
  let p ← get
  let tok := p.token
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
  -- Go parser.go:810-819: canParseSemicolon() || in || of || =>
  | .variableDeclarations =>
    tok == Kind.semicolonToken || tok == Kind.closeBraceToken || tok == Kind.endOfFile ||
    p.scanner.hasPrecedingLineBreak ||
    tok == Kind.inKeyword || tok == Kind.ofKeyword || tok == Kind.equalsGreaterThanToken
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
  | .importAttributes => tok == Kind.closeBraceToken
  | _ => false

/-- Based on Go: parser.go:623 (isInSomeParsingContext) -/
partial def isInSomeParsingContext : ParserM Bool := do
  return (← get).parsingContexts != 0

/-- Based on Go: parser.go:613 (abortParsingListOrMoveToNextToken) -/
partial def abortParsingListOrMoveToNextToken (_kind : ParsingContext) : ParserM Bool := do
  parseErrorAtCurrentToken Diagnostics.declaration_or_statement_expected
  if ← isInSomeParsingContext then return true
  else nextToken; return false

-- ============================================================
-- Section: Expression/Statement Start Predicates
-- ============================================================

/-- Helper: check if current token starts an expression. -/
partial def isStartOfExpression : ParserM Bool := do
  let tok ← currentToken
  let identStart ← isIdentifierToken
  return identStart || tok == Kind.numericLiteral ||
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
partial def isStartOfStatement : ParserM Bool := do
  match (← currentToken) with
  | .semicolonToken | .openBraceToken
  | .varKeyword | .letKeyword
  | .functionKeyword | .classKeyword
  | .ifKeyword | .returnKeyword
  | .doKeyword | .whileKeyword
  | .forKeyword | .continueKeyword
  | .breakKeyword | .switchKeyword
  | .throwKeyword | .tryKeyword
  | .debuggerKeyword | .catchKeyword
  | .finallyKeyword | .withKeyword
  | .constKeyword | .enumKeyword
  | .exportKeyword | .importKeyword
  | .asyncKeyword | .declareKeyword
  | .interfaceKeyword | .typeKeyword
  | .moduleKeyword | .namespaceKeyword
  | .abstractKeyword | .accessorKeyword
  | .publicKeyword | .privateKeyword
  | .protectedKeyword | .staticKeyword
  | .readonlyKeyword | .globalKeyword
  | .atToken => return true
  | _ => isStartOfExpression

/-- Check if current token starts a type. -/
partial def isStartOfType : ParserM Bool := do
  let tok ← currentToken
  return isKeywordType tok || tok == Kind.identifier || tok == Kind.openParenToken ||
    tok == Kind.openBracketToken || tok == Kind.openBraceToken ||
    tok == Kind.typeOfKeyword || tok == Kind.newKeyword ||
    tok == Kind.barToken || tok == Kind.ampersandToken ||
    tok == Kind.lessThanToken || tok == Kind.stringLiteral ||
    tok == Kind.numericLiteral || tok == Kind.trueKeyword ||
    tok == Kind.falseKeyword || tok == Kind.voidKeyword ||
    tok == Kind.undefinedKeyword || tok == Kind.nullKeyword ||
    tok == Kind.thisKeyword || tok == Kind.keyOfKeyword ||
    tok == Kind.uniqueKeyword || tok == Kind.readonlyKeyword ||
    tok == Kind.inferKeyword || tok == Kind.dotDotDotToken ||
    tok == Kind.templateHead || tok == Kind.noSubstitutionTemplateLiteral ||
    tok == Kind.minusToken || tok == Kind.abstractKeyword

-- ============================================================
-- Section: All Mutually Recursive Parse Functions
-- Based on Go: parser.go:945-5800
-- ============================================================

mutual

/-- Skip decorator annotations: @expr @expr ... -/
partial def skipDecorators : ParserM Unit := do
  match (← currentToken) with
  | .atToken =>
    nextToken
    let _ ← parseLeftHandSideExpressionOrHigher
    skipDecorators
  | _ => pure ()

/-- Based on Go: parser.go:3077 (isIndexSignature)
    Lookahead: is `[` followed by `identifier :` (index sig) or something else (computed prop)? -/
partial def isIndexSignature : ParserM Bool :=
  lookAhead do
    let _ ← parseExpected Kind.openBracketToken
    match (← currentToken) with
    | .dotDotDotToken => return true
    | _ => pure ()
    if ← isBindingIdentifierToken then
      nextToken
      return (← currentToken) == Kind.colonToken
    return false

/-- Parse dotted qualified name tail: A.B.C -/
partial def parseQualifiedNameRest (acc : Node) (pos : Nat) : ParserM Node := do
  match (← currentToken) with
  | .dotToken =>
    nextToken
    let right ← parseIdentifier
    let node ← finishNode (Node.qualifiedName {} acc right) pos
    parseQualifiedNameRest node pos
  | _ => return acc

/-- Based on Go: parser.go:533 (parseList) — loop body -/
partial def parseListLoop (kind : ParsingContext) (isElement : ParserM Bool)
    (parseElement : ParserM Node) (acc : Array Node) : ParserM (Array Node) := do
    if ← isListTerminator kind then return acc
    else if ← isElement then
      let startPos := (← get).scanner.tokenFullStart
      let node ← parseElement
      let acc' := acc.push node
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

/-- Based on Go: parser.go:540 (parseDelimitedList) — loop body -/
partial def parseDelimitedListLoop (kind : ParsingContext) (isElement : ParserM Bool)
    (parseElement : ParserM Node) (acc : Array Node) : ParserM (Array Node) := do
    if ← isElement then
      let startPos := (← get).scanner.tokenFullStart
      let node ← parseElement
      let acc' := acc.push node
      let endPos := (← get).scanner.tokenFullStart
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

-- ---- Expression Parsing ----

/-- Based on Go: parser.go:5636 (parseLiteralExpression) -/
partial def parseLiteralExpression : ParserM Node := do
  let pos ← nodePos
  let text := (← get).scanner.tokenValue
  let kind ← currentToken
  nextToken
  let node := match kind with
    | .numericLiteral => Node.numericLiteral {} text
    | .stringLiteral => Node.stringLiteral {} text
    | .noSubstitutionTemplateLiteral => Node.noSubstitutionTemplateLiteral {} text
    | _ => Node.numericLiteral {} text
  finishNode node pos

/-- Based on Go: parser.go:5469 (parseArrayLiteralExpression) -/
partial def parseArrayLiteralExpression : ParserM Node :=
  do
    let pos ← nodePos
    let _ ← parseExpected Kind.openBracketToken
    let isElem : ParserM Bool := do
      let tok ← currentToken
      match tok with
      | .commaToken | .dotDotDotToken => return true
      | _ => isStartOfExpression
    let elements ← parseDelimitedList .arrayLiteralMembers isElem
      (parseSpreadOrAssignmentExpression)
    let _ ← parseExpected Kind.closeBracketToken
    finishNode (Node.arrayLiteralExpression {} elements) pos

/-- Parse spread element or assignment expression (for array/argument lists). -/
partial def parseSpreadOrAssignmentExpression : ParserM Node :=
  do
    match (← currentToken) with
    | .dotDotDotToken =>
      let pos ← nodePos
      nextToken
      let expr ← parseAssignmentExpressionOrHigher
      finishNode (Node.spreadElement {} expr) pos
    | _ => parseAssignmentExpressionOrHigher

/-- Based on Go: parser.go:5479 (parseObjectLiteralExpression) -/
partial def parseObjectLiteralExpression : ParserM Node :=
  do
    let pos ← nodePos
    let _ ← parseExpected Kind.openBraceToken
    let isElem : ParserM Bool := do
      let tok ← currentToken
      if tok == Kind.dotDotDotToken then return true
      else if tok == Kind.identifier || tok == Kind.stringLiteral ||
              tok == Kind.numericLiteral || tok == Kind.openBracketToken then
        return true
      else if Kind.isKeywordKind tok then return true
      else return false
    let properties ← parseDelimitedList .objectLiteralMembers isElem
      (parseObjectLiteralElement)
    let _ ← parseExpected Kind.closeBraceToken
    finishNode (Node.objectLiteralExpression {} properties) pos

/-- Helper: after parsing a property name, dispatch on the next token to decide
    whether this is a method shorthand, property assignment, or shorthand property. -/
partial def parsePropertyBody (name : Node) (pos : Nat) : ParserM Node := do
  match (← currentToken) with
  | .openParenToken | .lessThanToken =>
    -- Method shorthand: name(params) { body }
    let typeParams ← parseTypeParameters
    let params ← parseParameters
    let returnType ← parseReturnType
    let body ← parseFunctionBlock
    finishNode (Node.methodDeclaration {} name none typeParams params returnType body) pos
  | .colonToken =>
    -- Property assignment: name: value
    nextToken
    let value ← parseAssignmentExpressionOrHigher
    finishNode (Node.propertyAssignment {} name (some value)) pos
  | _ =>
    -- Shorthand property: name  (or name = default)
    finishNode (Node.shorthandPropertyAssignment {} name) pos

/-- Parse a single object literal element (property, shorthand, spread, method). -/
partial def parseObjectLiteralElement : ParserM Node :=
  do
    let pos ← nodePos
    match (← currentToken) with
    | .dotDotDotToken =>
      nextToken
      let expr ← parseAssignmentExpressionOrHigher
      finishNode (Node.spreadAssignment {} expr) pos
    | .getKeyword | .setKeyword =>
      let isAccessor ← lookAhead do
        nextToken
        let t ← currentToken
        -- `get`/`set` can still be plain property names.
        match t with
        | .openParenToken | .colonToken | .commaToken | .closeBraceToken =>
          return false
        | _ =>
          let _ ← parsePropertyName
          return (← currentToken) == Kind.openParenToken
      if isAccessor then
        nextToken
        let name ← parsePropertyName
        let questionToken ← parseOptionalToken Kind.questionToken
        let typeParams ← parseTypeParameters
        let params ← parseParameters
        let returnType ← parseReturnType
        let body ← parseFunctionBlock
        finishNode (Node.methodDeclaration {} name questionToken typeParams params returnType body) pos
      else
        let name ← parsePropertyName
        parsePropertyBody name pos
    | _ =>
      let name ← parsePropertyName
      parsePropertyBody name pos

/-- Based on Go: parser.go:5610 (parseNewExpressionOrNewDotTarget) -/
partial def parseNewExpression : ParserM Node :=
  do
    let pos ← nodePos
    let _ ← parseExpected Kind.newKeyword
    let expr ← parseMemberExpressionOrHigher
    let args ← match (← currentToken) with
      | .openParenToken => do
        let _ ← parseExpected Kind.openParenToken
        let a ← parseDelimitedList .argumentExpressions isStartOfExpression
          (parseAssignmentExpressionOrHigher)
        let _ ← parseExpected Kind.closeParenToken
        pure (some a)
      | _ => pure none
    finishNode (Node.newExpression {} expr args) pos

/-- Based on Go: parser.go:4335 (parseFunctionExpression) -/
partial def parseFunctionExpression : ParserM Node :=
  do
    let pos ← nodePos
    let _ ← parseExpected Kind.functionKeyword
    let name ← if ← isBindingIdentifierToken then
      pure (some (← parseBindingIdentifier))
    else pure none
    let typeParams ← parseTypeParameters
    let params ← parseParameters
    let returnType ← parseReturnType
    let body ← parseFunctionBlock
    finishNode (Node.functionExpression {} name typeParams params returnType body) pos

/-- Based on Go: parser.go:5413 (parsePrimaryExpression) -/
partial def parsePrimaryExpression : ParserM Node :=
  do
    let tok ← currentToken
    match tok with
    | .numericLiteral
    | .bigIntLiteral
    | .stringLiteral
    | .noSubstitutionTemplateLiteral =>
      parseLiteralExpression
    | .templateHead =>
      parseTemplateExpression
    | .thisKeyword
    | .superKeyword
    | .nullKeyword
    | .trueKeyword
    | .falseKeyword =>
      parseTokenNode
    | .openParenToken =>
      parseParenthesizedExpression
    | .openBracketToken =>
      parseArrayLiteralExpression
    | .openBraceToken =>
      parseObjectLiteralExpression
    | .functionKeyword =>
      parseFunctionExpression
    | .newKeyword =>
      parseNewExpression
    | .classKeyword =>
      -- Class expression
      parseClassDeclaration
    | .lessThanToken
    | .lessThanSlashToken =>
      if (← get).scanner.languageVariant == LanguageVariant.jsx then
        parseJsxLikeExpression
      else
        parseIdentifier
    | _ =>
      parseIdentifier

/-- Based on Go: parser.go:5458 (parseParenthesizedExpression) -/
partial def parseParenthesizedExpression : ParserM Node :=
  do
    let pos ← nodePos
    let _ ← parseExpected Kind.openParenToken
    let expr ← parseExpressionAllowIn
    let _ ← parseExpected Kind.closeParenToken
    finishNode (Node.parenthesizedExpression {} expr) pos

/-- Based on Go: parser.go:229 (parseTemplateExpression)
    Simplified: skip to end of template, creating a single literal node. -/
partial def parseTemplateExpression : ParserM Node :=
  do
    -- For now, parse template head as literal and skip remaining tokens
    -- until we find the template tail or EOF.
    -- Full template parsing requires reScanTemplateToken on the scanner.
    parseLiteralExpression

/-- Lightweight JSX fallback parser.
    Consumes a JSX-like region in primary-expression position and returns
    a placeholder identifier expression. This avoids cascading parse errors
    until full JSX parsing is implemented. -/
partial def parseJsxLikeExpression : ParserM Node := do
  let pos ← nodePos
  let rec skipBraceExpression (depth : Nat) : ParserM Unit := do
    if depth == 0 then
      pure ()
    else
      match (← currentToken) with
      | .endOfFile => pure ()
      | .openBraceToken => nextToken; skipBraceExpression (depth + 1)
      | .closeBraceToken => nextToken; skipBraceExpression (depth - 1)
      | _ => nextToken; skipBraceExpression depth

  let rec consume (depth : Nat) (inTag : Bool) (pendingOpen : Bool) (pendingClose : Bool)
      (seenTag : Bool) (steps : Nat) : ParserM Unit := do
    if steps > 20000 then
      pure ()
    else
    let tok ← currentToken
    if tok == Kind.endOfFile then
      pure ()
    else if seenTag && depth == 0 && !inTag && tok != Kind.lessThanToken && tok != Kind.lessThanSlashToken then
      pure ()
    else if tok == Kind.openBraceToken && !inTag then
      nextToken
      skipBraceExpression 1
      consume depth inTag pendingOpen pendingClose seenTag (steps + 1)
    else
      let (depth', inTag', pendingOpen', pendingClose', seenTag', advanceNow) :=
        match tok with
        | .lessThanToken =>
          (depth, true, true, false, true, true)
        | .lessThanSlashToken =>
          (depth, true, false, true, true, true)
        | .greaterThanToken =>
          if inTag then
            if pendingClose then
              let depth' := if depth > 0 then depth - 1 else 0
              (depth', false, false, false, seenTag, true)
            else if pendingOpen then
              (depth + 1, false, false, false, seenTag, true)
            else
              (depth, false, false, false, seenTag, true)
          else
            (depth, inTag, pendingOpen, pendingClose, seenTag, true)
        | .slashToken =>
          if inTag && pendingOpen then
            -- Handle self-closing tags: <Tag />
            (depth, inTag, false, false, seenTag, true)
          else
            (depth, inTag, pendingOpen, pendingClose, seenTag, true)
        | _ =>
          (depth, inTag, pendingOpen, pendingClose, seenTag, true)
      if advanceNow then
        nextToken
      if seenTag' && depth' == 0 && !inTag' then
        pure ()
      else
        consume depth' inTag' pendingOpen' pendingClose' seenTag' (steps + 1)
  consume 0 false false false false 0
  finishNode (Node.identifier {} "__jsx") pos

/-- Based on Go: parser.go:5143 (parseMemberExpressionOrHigher) -/
partial def parseMemberExpressionOrHigher : ParserM Node :=
  do
    let pos ← nodePos
    let expr ← parsePrimaryExpression
    parseMemberExpressionRest pos expr

/-- Helper: parse member expression rest (.prop, [idx], !).
    Based on Go: parser.go:5162 -/
partial def parseMemberExpressionRest (pos : Nat) (current : Node) : ParserM Node := do
      let tok ← currentToken
      match tok with
      | .dotToken =>
        nextToken
        let name ← parseIdentifierName
        let node ← finishNode (Node.propertyAccessExpression {} current name) pos
        parseMemberExpressionRest pos node
      -- Optional chaining: ?.prop or ?.[idx]
      -- Based on Go: parser.go:5198 (parsePropertyOrElementAccessChain)
      | .questionDotToken =>
        nextToken
        match (← currentToken) with
        | .openBracketToken =>
          nextToken
          let argExpr ← parseExpressionAllowIn
          let _ ← parseExpected Kind.closeBracketToken
          let node ← finishNode (Node.elementAccessExpression {} current argExpr) pos
          parseMemberExpressionRest pos node
        | _ =>
          let name ← parseIdentifierName
          let node ← finishNode (Node.propertyAccessExpression {} current name) pos
          parseMemberExpressionRest pos node
      | .exclamationToken =>
        if !(← get).scanner.hasPrecedingLineBreak then
          nextToken
          let node ← finishNode (Node.nonNullExpression {} current) pos
          parseMemberExpressionRest pos node
        else return current
      | .openBracketToken =>
        nextToken
        let argExpr ← parseExpressionAllowIn
        let _ ← parseExpected Kind.closeBracketToken
        let node ← finishNode (Node.elementAccessExpression {} current argExpr) pos
        parseMemberExpressionRest pos node
      | _ => return current

/-- Based on Go: parser.go:5312 (parseCallExpressionRest) -/
partial def parseCallExpressionRest (pos : Nat) (current : Node) : ParserM Node := do

      let tok ← currentToken
      match tok with
      | .openParenToken =>
        let _ ← parseExpected Kind.openParenToken
        let args ← parseDelimitedList .argumentExpressions isStartOfExpression
          (parseSpreadOrAssignmentExpression)
        let _ ← parseExpected Kind.closeParenToken
        let node ← finishNode (Node.callExpression {} current args) pos
        parseCallExpressionRest pos node
      | .lessThanToken | .lessThanLessThanToken =>
        -- Generic call: expr<T>(args)
        let isTypeArgCall ← lookAhead do
          match (← currentToken) with
          | .lessThanLessThanToken => let _ ← reScanLessThanToken
          | _ => pure ()
          match (← currentToken) with
          | .lessThanToken => pure ()
          | _ => return false
          let _ ← parseExpected Kind.lessThanToken
          let _ ← parseDelimitedList .typeArguments isStartOfType (parseType')
          let _ ← parseExpected Kind.greaterThanToken
          return (← currentToken) == Kind.openParenToken
        if isTypeArgCall then
          match (← currentToken) with
          | .lessThanLessThanToken => let _ ← reScanLessThanToken
          | _ => pure ()
          let _ ← parseExpected Kind.lessThanToken
          let _ ← parseDelimitedList .typeArguments isStartOfType (parseType')
          let _ ← parseExpected Kind.greaterThanToken
          let _ ← parseExpected Kind.openParenToken
          let args ← parseDelimitedList .argumentExpressions isStartOfExpression
            (parseSpreadOrAssignmentExpression)
          let _ ← parseExpected Kind.closeParenToken
          let node ← finishNode (Node.callExpression {} current args) pos
          parseCallExpressionRest pos node
        else
          return current
      | .questionDotToken =>
        -- Optional chaining: foo?.(), foo?.prop, foo?.[idx]
        let isCall ← lookAhead do nextToken; return (← currentToken) == Kind.openParenToken
        if isCall then
          nextToken  -- skip ?.
          let _ ← parseExpected Kind.openParenToken
          let args ← parseDelimitedList .argumentExpressions isStartOfExpression
            (parseSpreadOrAssignmentExpression)
          let _ ← parseExpected Kind.closeParenToken
          let node ← finishNode (Node.callExpression {} current args) pos
          parseCallExpressionRest pos node
        else
          let expr' ← parseMemberExpressionRest pos current
          parseCallExpressionRest pos expr'
      | .dotToken | .openBracketToken =>
        let expr' ← parseMemberExpressionRest pos current
        parseCallExpressionRest pos expr'
      | .exclamationToken =>
        if !(← get).scanner.hasPrecedingLineBreak then
          let expr' ← parseMemberExpressionRest pos current
          parseCallExpressionRest pos expr'
        else return current
      | .noSubstitutionTemplateLiteral | .templateHead =>
        let tmpl ← match tok with
          | .noSubstitutionTemplateLiteral =>
            let _ ← reScanTemplateToken true
            parseLiteralExpression
          | _ => parseTemplateExpression
        let node ← finishNode (Node.taggedTemplateExpression {} current tmpl) pos
        parseCallExpressionRest pos node
      | _ => return current

/-- Based on Go: parser.go:5002 (parseLeftHandSideExpressionOrHigher) -/
partial def parseLeftHandSideExpressionOrHigher : ParserM Node :=
  do
    let pos ← nodePos
    let expr ← parseMemberExpressionOrHigher
    parseCallExpressionRest pos expr

/-- Based on Go: parser.go:4528 (parseUnaryExpressionOrHigher) -/
partial def parseUnaryExpressionOrHigher : ParserM Node :=
  do
    let tok ← currentToken
    match tok with
    | .plusToken
    | .minusToken
    | .tildeToken
    | .exclamationToken
    | .plusPlusToken
    | .minusMinusToken =>
      let pos ← nodePos
      let op ← currentToken
      nextToken
      let operand ← parseUnaryExpressionOrHigher
      finishNode (Node.prefixUnaryExpression {} op operand) pos
    | .deleteKeyword =>
      let pos ← nodePos
      nextToken
      let operand ← parseUnaryExpressionOrHigher
      finishNode (Node.deleteExpression {} operand) pos
    | .typeOfKeyword =>
      let pos ← nodePos
      nextToken
      let operand ← parseUnaryExpressionOrHigher
      finishNode (Node.typeOfExpression {} operand) pos
    | .voidKeyword =>
      let pos ← nodePos
      nextToken
      let operand ← parseUnaryExpressionOrHigher
      finishNode (Node.voidExpression {} operand) pos
    | .awaitKeyword =>
      let pos ← nodePos
      nextToken
      let operand ← parseUnaryExpressionOrHigher
      finishNode (Node.awaitExpression {} operand) pos
    | _ =>
      let pos ← nodePos
      let expr ← parseLeftHandSideExpressionOrHigher
      if !(← get).scanner.hasPrecedingLineBreak then
        let tok ← currentToken
        match tok with
        | .plusPlusToken
        | .minusMinusToken =>
          nextToken
          finishNode (Node.postfixUnaryExpression {} expr tok) pos
        | _ =>
          return expr
      else
        return expr

/-- Based on Go: parser.go:4453 (parseBinaryExpressionRest) — Pratt parser -/
partial def parseBinaryExpressionRest (precedence : OperatorPrecedence)
    (left : Node) (pos : Nat) : ParserM Node := do
      -- Rescan > tokens (for >=, >>=, >>>=)
      match (← currentToken) with
      | .greaterThanToken => let _ ← reScanGreaterThanToken
      | _ => pure ()
      let tok ← currentToken
      -- Handle 'as' type assertion and 'satisfies' expression
      -- Based on Go: parser.go:4492
      match tok with
      | .asKeyword | .satisfiesKeyword =>
        if precedence.toInt >= OperatorPrecedence.relational.toInt then return left
        if (← get).scanner.hasPrecedingLineBreak then return left
        nextToken
        let typeNode ← parseType'
        let expr ← match tok with
          | .satisfiesKeyword =>
            finishNode (Node.satisfiesExpression {} left typeNode) pos
          | _ =>
            finishNode (Node.asExpression {} left typeNode) pos
        parseBinaryExpressionRest precedence expr pos
      | _ =>
      let newPrecedence := getBinaryOperatorPrecedence tok
      let consume := match tok with
        | .asteriskAsteriskToken =>
          newPrecedence.toInt >= precedence.toInt  -- right-associative
        | _ =>
          newPrecedence.toInt > precedence.toInt   -- left-associative
      if !consume then return left
      match tok with
      | .inKeyword =>
        if (← get).contextFlags.hasFlag NodeFlags.disallowInContext then
          return left
      | _ => pure ()
      let opNode ← parseTokenNode
      let rightOperand ← parseBinaryExpressionOrHigher newPrecedence
      let binExpr ← finishNode (Node.binaryExpression {} left opNode rightOperand) pos
      parseBinaryExpressionRest precedence binExpr pos

/-- Based on Go: parser.go:4447 (parseBinaryExpressionOrHigher) -/
partial def parseBinaryExpressionOrHigher (precedence : OperatorPrecedence) : ParserM Node :=
  do
    let pos ← nodePos
    let leftOperand ← parseUnaryExpressionOrHigher
    parseBinaryExpressionRest precedence leftOperand pos

/-- Based on Go: parser.go:4424 (parseConditionalExpressionRest) -/
partial def parseConditionalExpressionRest (expr : Node) (pos : Nat) : ParserM Node :=
  do
    match (← currentToken) with
    | .questionToken =>
      nextToken
      let saved := (← get).contextFlags
      setContextFlag NodeFlags.disallowInContext false
      let whenTrue ← parseAssignmentExpressionOrHigher
      modify fun p => { p with contextFlags := saved }
      let _ ← parseExpected Kind.colonToken
      let whenFalse ← parseAssignmentExpressionOrHigher
      finishNode (Node.conditionalExpression {} expr whenTrue whenFalse) pos
    | _ => return expr

/-- Try to detect if current position is an arrow function.
    Simple heuristic: look for `() =>`, `(id) =>`, `id =>`. -/
partial def isArrowFunctionStart : ParserM Bool := do
  match (← currentToken) with
  | .openParenToken =>
    lookAhead do
      let rec scanToArrow (parenDepth bracketDepth braceDepth : Nat) : ParserM Bool := do
        match (← currentToken) with
        | .endOfFile => return false
        | .openParenToken =>
          nextToken
          scanToArrow (parenDepth + 1) bracketDepth braceDepth
        | .closeParenToken =>
          if parenDepth == 1 && bracketDepth == 0 && braceDepth == 0 then
            nextToken
            match (← currentToken) with
            | .equalsGreaterThanToken => return true
            | .colonToken =>
              let _ ← parseReturnType
              return (← currentToken) == Kind.equalsGreaterThanToken
            | _ => return false
          else
            nextToken
            scanToArrow (parenDepth - 1) bracketDepth braceDepth
        | .openBracketToken =>
          nextToken
          scanToArrow parenDepth (bracketDepth + 1) braceDepth
        | .closeBracketToken =>
          if bracketDepth == 0 then return false
          nextToken
          scanToArrow parenDepth (bracketDepth - 1) braceDepth
        | .openBraceToken =>
          nextToken
          scanToArrow parenDepth bracketDepth (braceDepth + 1)
        | .closeBraceToken =>
          if braceDepth == 0 then return false
          nextToken
          scanToArrow parenDepth bracketDepth (braceDepth - 1)
        | _ =>
          nextToken
          scanToArrow parenDepth bracketDepth braceDepth
      scanToArrow 0 0 0
  | _ =>
    if ← isBindingIdentifierToken then
      lookAhead do
        nextToken
        return (← currentToken) == Kind.equalsGreaterThanToken
    else return false

/-- Parse arrow function expression. -/
partial def parseArrowFunction : ParserM Node :=
  do
    let pos ← nodePos
    match (← currentToken) with
    | .openParenToken =>
      let typeParams ← parseTypeParameters
      let params ← parseParameters
      let returnType ← parseReturnType
      let _ ← parseExpected Kind.equalsGreaterThanToken
      let body ← match (← currentToken) with
        | .openBraceToken => parseBlock
        | _ => parseAssignmentExpressionOrHigher
      finishNode (Node.arrowFunction {} typeParams params returnType body) pos
    | _ =>
      -- Single parameter arrow: x => expr
      let param ← parseBindingIdentifier
      let paramNode ← finishNode (Node.parameterDeclaration {} none param none none none) pos
      let _ ← parseExpected Kind.equalsGreaterThanToken
      let body ← match (← currentToken) with
        | .openBraceToken => parseBlock
        | _ => parseAssignmentExpressionOrHigher
      finishNode (Node.arrowFunction {} none #[paramNode] none body) pos

/-- Based on Go: parser.go:3952 (parseAssignmentExpressionOrHigher) -/
partial def parseAssignmentExpressionOrHigher : ParserM Node :=
  do
    let tok0 ← currentToken
    if ((tok0 == Kind.lessThanToken) || (tok0 == Kind.lessThanSlashToken)) &&
       (← get).scanner.languageVariant == LanguageVariant.jsx then
      return ← parseJsxLikeExpression
    -- Check for arrow function
    if ← isArrowFunctionStart then
      return ← parseArrowFunction
    -- Check for yield
    match (← currentToken) with
    | .yieldKeyword =>
      let pos ← nodePos
      nextToken
      let expr ← if !(← canParseSemicolon) then
        pure (some (← parseAssignmentExpressionOrHigher))
      else pure none
      return ← finishNode (Node.yieldExpression {} expr) pos
    | _ => pure ()
    let pos ← nodePos
    let expr ← parseBinaryExpressionOrHigher OperatorPrecedence.lowest
    -- Check for conditional
    match (← currentToken) with
    | .questionToken => return ← parseConditionalExpressionRest expr pos
    | _ => pure ()
    if isLeftHandSideExpression expr && Kind.isAssignment (← currentToken) then
      let opNode ← parseTokenNode
      let right ← parseAssignmentExpressionOrHigher
      finishNode (Node.binaryExpression {} expr opNode right) pos
    else return expr

/-- Helper: parse comma expression rest. -/
partial def parseExpressionCommaRest (current : Node) (pos : Nat) : ParserM Node := do
      match (← currentToken) with
      | .commaToken =>
        let opNode ← parseTokenNode
        let right ← parseAssignmentExpressionOrHigher
        let binExpr ← finishNode (Node.binaryExpression {} current opNode right) pos
        parseExpressionCommaRest binExpr pos
      | _ => return current

/-- Based on Go: parser.go:3927 (parseExpression) — comma expressions -/
partial def parseExpression : ParserM Node :=
  do
    let pos ← nodePos
    let expr ← parseAssignmentExpressionOrHigher
    parseExpressionCommaRest expr pos

/-- Based on Go: parser.go:3948 (parseExpressionAllowIn) -/
partial def parseExpressionAllowIn : ParserM Node :=
  do
    let saved := (← get).contextFlags
    setContextFlag NodeFlags.disallowInContext false
    let expr ← parseExpression
    modify fun p => { p with contextFlags := saved }
    return expr

-- ---- Type Parsing ----

/-- Based on Go: parser.go:2484 (parseType) — full type parsing -/
partial def parseType' : ParserM Node :=
  do
    let tok ← currentToken
    match tok with
    -- Generic function type: <T>(params) => ReturnType
    | .lessThanToken =>
      let pos ← nodePos
      let typeParams ← parseTypeParameters
      let params ← parseParameters
      let _ ← parseExpected Kind.equalsGreaterThanToken
      let retType ← parseType'
      return ← finishNode (Node.functionType {} typeParams params (some retType)) pos
    -- Function type: (params) => ReturnType
    | .openParenToken =>
      -- Try to detect function type vs parenthesized type
      let isFuncType ← lookAhead do
        let rec scanToArrow (parenDepth bracketDepth braceDepth : Nat) : ParserM Bool := do
          match (← currentToken) with
          | .endOfFile => return false
          | .openParenToken =>
            nextToken
            scanToArrow (parenDepth + 1) bracketDepth braceDepth
          | .closeParenToken =>
            if parenDepth == 1 && bracketDepth == 0 && braceDepth == 0 then
              nextToken
              return (← currentToken) == Kind.equalsGreaterThanToken
            else
              nextToken
              scanToArrow (parenDepth - 1) bracketDepth braceDepth
          | .openBracketToken =>
            nextToken
            scanToArrow parenDepth (bracketDepth + 1) braceDepth
          | .closeBracketToken =>
            if bracketDepth == 0 then return false
            nextToken
            scanToArrow parenDepth (bracketDepth - 1) braceDepth
          | .openBraceToken =>
            nextToken
            scanToArrow parenDepth bracketDepth (braceDepth + 1)
          | .closeBraceToken =>
            if braceDepth == 0 then return false
            nextToken
            scanToArrow parenDepth bracketDepth (braceDepth - 1)
          | _ =>
            nextToken
            scanToArrow parenDepth bracketDepth braceDepth
        scanToArrow 0 0 0
      if isFuncType then
        let pos ← nodePos
        let params ← parseParameters
        let _ ← parseExpected Kind.equalsGreaterThanToken
        let retType ← parseType'
        return ← finishNode (Node.functionType {} none params (some retType)) pos
      else
        -- Parenthesized type
        let pos ← nodePos
        let _ ← parseExpected Kind.openParenToken
        let inner ← parseType'
        let _ ← parseExpected Kind.closeParenToken
        let pType ← finishNode (Node.parenthesizedType {} inner) pos
        let pType ← parseArrayTypePostfix pType
        parseUnionOrIntersectionPostfix pType
    -- Constructor type: new (params) => ReturnType
    | .newKeyword =>
      let pos ← nodePos
      nextToken
      let params ← parseParameters
      let _ ← parseExpected Kind.equalsGreaterThanToken
      let retType ← parseType'
      finishNode (Node.constructorType {} none params (some retType)) pos
    -- keyof, unique, readonly type operators
    | .keyOfKeyword | .uniqueKeyword | .readonlyKeyword =>
      let pos ← nodePos
      let op ← currentToken
      nextToken
      let inner ← parseType'
      finishNode (Node.typeOperator {} op inner) pos
    -- infer T — Based on Go: parser.go:2445
    | .inferKeyword =>
      let pos ← nodePos
      nextToken
      let tpPos ← nodePos
      let name ← parseIdentifier
      -- infer T creates a typeParameter node for the name
      let tp ← finishNode (Node.typeReference {} name none) tpPos
      finishNode (Node.inferType {} tp) pos
    | _ =>
      -- Union prefix: | Type
      let hasLeadingBar := tok == Kind.barToken
      if hasLeadingBar then nextToken
      -- Primary type then union/intersection postfix
      let primaryType ← parsePrimaryType
      let typeNode ← parseUnionOrIntersectionPostfix primaryType
      -- Conditional type postfix: T extends U ? X : Y
      -- Based on Go: parser.go:2493-2507
      match (← currentToken) with
      | .extendsKeyword =>
        if !(← get).scanner.hasPrecedingLineBreak then
          let cPos := typeNode.base.loc.pos.toInt.toNat
          nextToken  -- skip 'extends'
          let extendsType ← parseType'
          let _ ← parseExpected Kind.questionToken
          let trueType ← parseType'
          let _ ← parseExpected Kind.colonToken
          let falseType ← parseType'
          finishNode (Node.conditionalType {} typeNode extendsType trueType falseType) cPos
        else return typeNode
      | _ => return typeNode

/-- Parse a primary (non-union, non-intersection) type. -/
partial def parsePrimaryType : ParserM Node :=
  do
    let tok ← currentToken
    let baseType ←
      match tok with
      -- Type literal: { members }
      | .openBraceToken =>
        let pos ← nodePos
        let _ ← parseExpected Kind.openBraceToken
        let members ← parseList .typeMembers (isTypeMemberStart) (parseTypeMember)
        let _ ← parseExpected Kind.closeBraceToken
        finishNode (Node.typeLiteral {} members) pos
      -- Tuple type: [Type, Type]
      | .openBracketToken =>
        let pos ← nodePos
        let _ ← parseExpected Kind.openBracketToken
        let elements ← parseDelimitedList .tupleElementTypes isStartOfType (parseType')
        let _ ← parseExpected Kind.closeBracketToken
        finishNode (Node.tupleType {} elements) pos
      -- typeof type: typeof expr
      | .typeOfKeyword =>
        let pos ← nodePos
        nextToken
        let name ← parseIdentifier
        let qname ← parseQualifiedNameRest name pos
        finishNode (Node.typeQuery {} qname) pos
      | .voidKeyword | .undefinedKeyword | .nullKeyword => parseTokenNode
      | .stringLiteral | .numericLiteral | .trueKeyword | .falseKeyword =>
        let pos ← nodePos
        let lit ← parseLiteralExpression
        finishNode (Node.literalType {} lit) pos
      | .minusToken =>
        let pos ← nodePos
        nextToken
        let lit ← parseLiteralExpression
        let neg ← finishNode (Node.prefixUnaryExpression {} Kind.minusToken lit) pos
        finishNode (Node.literalType {} neg) pos
      | .thisKeyword => parseTokenNode
      | _ =>
        if isKeywordType tok then parseTokenNode
        else if ← isIdentifierToken then
          let pos ← nodePos
          let name ← parseIdentifier
          -- Check for qualified name: A.B.C
          let qname ← parseQualifiedNameRest name pos
          -- Check for type arguments: Name<T, U>
          let typeArgs ← match (← currentToken) with
            | .lessThanToken => do
              let _ ← parseExpected Kind.lessThanToken
              let args ← parseDelimitedList .typeArguments isStartOfType (parseType')
              let _ ← parseExpected Kind.greaterThanToken
              pure (some args)
            | _ => pure none
          finishNode (Node.typeReference {} qname typeArgs) pos
        else
          parseTokenNode  -- fallback
    -- Array type postfix: Type[], Type[][]
    parseArrayTypePostfix baseType

/-- Parse array type postfix: Type[], Type[][], Type[Key]
    Based on Go: parser.go:2427 (parseArrayTypeOrHigher) -/
partial def parseArrayTypePostfix (current : Node) : ParserM Node := do
      match (← currentToken) with
      | .openBracketToken =>
        let isArrayType ← lookAhead do nextToken; return (← currentToken) == Kind.closeBracketToken
        if isArrayType then
          let pos := current.base.loc.pos.toInt.toNat
          nextToken  -- [
          nextToken  -- ]
          let node ← finishNode (Node.arrayType {} current) pos
          parseArrayTypePostfix node
        else
          -- Indexed access type: Type[Key]
          let pos := current.base.loc.pos.toInt.toNat
          nextToken  -- [
          let indexType ← parseType'
          let _ ← parseExpected Kind.closeBracketToken
          let node ← finishNode (Node.indexedAccessType {} current indexType) pos
          parseArrayTypePostfix node
      | _ => return current

/-- Parse intersection type: Type & Type & Type
    Based on Go: parser.go:2379 (parseIntersectionTypeOrHigher)
    Each intersection member is a primary type with array/indexed-access postfix. -/
partial def collectIntersectionTypes (acc : Array Node) : ParserM (Array Node) := do
    match (← currentToken) with
    | .ampersandToken =>
      nextToken
      let nextType ← parsePrimaryType
      collectIntersectionTypes (acc.push nextType)
    | _ => return acc

partial def parseIntersectionPostfix (firstType : Node) : ParserM Node := do
    match (← currentToken) with
    | .ampersandToken =>
      let pos := firstType.base.loc.pos.toInt.toNat
      let types ← collectIntersectionTypes #[firstType]
      finishNode (Node.intersectionType {} types) pos
    | _ => return firstType

partial def collectUnionTypes (acc : Array Node) : ParserM (Array Node) := do
    match (← currentToken) with
    | .barToken =>
      nextToken
      let primary ← parsePrimaryType
      let member ← parseIntersectionPostfix primary
      collectUnionTypes (acc.push member)
    | _ => return acc

/-- Parse union/intersection postfix: Type | Type, Type & Type
    Based on Go: parser.go:2358 (parseUnionTypeOrHigher)
    Each union member is parsed as intersection-or-higher. -/
partial def parseUnionOrIntersectionPostfix (firstType : Node) : ParserM Node := do
    let firstOrIntersection ← parseIntersectionPostfix firstType
    match (← currentToken) with
    | .barToken =>
      let pos := firstOrIntersection.base.loc.pos.toInt.toNat
      let types ← collectUnionTypes #[firstOrIntersection]
      finishNode (Node.unionType {} types) pos
    | _ => return firstOrIntersection

/-- Check if current token can start a type member. -/
partial def isTypeMemberStart : ParserM Bool := do
  let tok ← currentToken
  match tok with
  | .openParenToken | .lessThanToken => return true  -- call sig
  | .openBracketToken => return true  -- index sig
  | .newKeyword => return true  -- construct sig
  | .identifier | .stringLiteral | .numericLiteral => return true
  | _ => return Kind.isKeywordKind tok

/-- Helper: after parsing a type member's name and question token, dispatch
    on whether this is a method signature or property signature. -/
partial def parseTypeMemberPropertyOrMethod (name : Node) (questionToken : Option Node)
    (pos : Nat) : ParserM Node := do
  match (← currentToken) with
  | .openParenToken | .lessThanToken =>
    let typeParams ← parseTypeParameters
    let params ← parseParameters
    let returnType ← parseReturnType
    parseTypeMemberSemicolon
    finishNode (Node.methodSignature {} name questionToken typeParams params returnType) pos
  | _ =>
    let typeNode ← parseTypeAnnotation
    parseTypeMemberSemicolon
    finishNode (Node.propertySignature {} name questionToken typeNode) pos

/-- Parse a single type member (property signature, method signature, index signature, etc.) -/
partial def parseTypeMember : ParserM Node :=
  do
    let pos ← nodePos
    let tok ← currentToken
    match tok with
    -- Call signature: (params): Type
    | .openParenToken | .lessThanToken =>
      let typeParams ← parseTypeParameters
      let params ← parseParameters
      let returnType ← parseReturnType
      parseTypeMemberSemicolon
      finishNode (Node.callSignature {} typeParams params returnType) pos
    -- Construct signature: new (params): Type
    | .newKeyword =>
      nextToken
      let typeParams ← parseTypeParameters
      let params ← parseParameters
      let returnType ← parseReturnType
      parseTypeMemberSemicolon
      finishNode (Node.constructSignature {} typeParams params returnType) pos
    -- Index signature or computed property name
    | .openBracketToken =>
      if ← isIndexSignature then
        -- Index signature: [key: Type]: Type
        let _ ← parseExpected Kind.openBracketToken
        let isIdx : ParserM Bool := do
          let tok ← currentToken
          let bindId ← isBindingIdentifierToken
          return bindId || tok == Kind.dotDotDotToken
        let params ← parseDelimitedList .parameters isIdx (parseParameter)
        let _ ← parseExpected Kind.closeBracketToken
        let typeNode ← parseTypeAnnotation
        parseTypeMemberSemicolon
        finishNode (Node.indexSignature {} params typeNode) pos
      else
        -- Computed property name: [expr]?: Type or [expr](params): Type
        let name ← parsePropertyName
        let questionToken ← parseOptionalToken Kind.questionToken
        parseTypeMemberPropertyOrMethod name questionToken pos
    | _ =>
      -- Property or method signature
      let name ← parsePropertyName
      let questionToken ← parseOptionalToken Kind.questionToken
      parseTypeMemberPropertyOrMethod name questionToken pos

/-- Based on Go: parser.go:1588 (parseTypeAnnotation) -/
partial def parseTypeAnnotation : ParserM (Option Node) :=
  do
    if ← parseOptional Kind.colonToken then
      pure (some (← parseType'))
    else return none

/-- Based on Go: parser.go:3255 (parseReturnType) -/
partial def parseReturnType : ParserM (Option Node) :=
  do
    if ← parseOptional Kind.colonToken then
      let tok ← currentToken
      -- Based on Go: parser.go:2316 (parseReturnType)
      match tok with
      | .assertsKeyword =>
        -- Handle 'asserts' type predicate
        let isAsserts ← lookAhead do
          nextToken
          let t ← currentToken
          return t == Kind.identifier || t == Kind.thisKeyword
        if isAsserts then
          let pos ← nodePos
          nextToken  -- skip 'asserts'
          let paramName ← parseIdentifier
          -- asserts x is Type
          let typeNode ← match (← currentToken) with
            | .isKeyword => nextToken; pure (some (← parseType'))
            | _ => pure none
          let tp ← finishNode (Node.typePredicate {} paramName typeNode) pos
          return some tp
        pure (some (← parseType'))
      | .identifier =>
        -- Handle 'x is Type' type predicate
        let isTypePred ← lookAhead do
          nextToken; return (← currentToken) == Kind.isKeyword
        if isTypePred then
          let pos ← nodePos
          let paramName ← parseIdentifier
          nextToken  -- skip 'is'
          let typeNode ← parseType'
          let tp ← finishNode (Node.typePredicate {} paramName (some typeNode)) pos
          return some tp
        pure (some (← parseType'))
      | _ => pure (some (← parseType'))
    else return none

/-- Based on Go: parser.go:3096 (parseTypeParameters) -/
partial def parseTypeParameters : ParserM (Option (Array Node)) :=
  do
    match (← currentToken) with
    | .lessThanLessThanToken => let _ ← reScanLessThanToken
    | _ => pure ()
    match (← currentToken) with
    | .lessThanToken =>
      let _ ← parseExpected Kind.lessThanToken
      let isTP : ParserM Bool := isIdentifierToken
      let params ← parseDelimitedList .typeParameters isTP do
        let pos ← nodePos
        let name ← parseIdentifier
        -- Parse optional constraint: extends Type
        match (← currentToken) with
        | .extendsKeyword =>
          nextToken
          let _constraint ← parseType'
          pure ()
        | _ => pure ()
        -- Parse optional default: = Type
        match (← currentToken) with
        | .equalsToken =>
          nextToken
          let _defaultType ← parseType'
          pure ()
        | _ => pure ()
        finishNode name pos
      let _ ← parseExpected Kind.greaterThanToken
      pure (some params)
    | _ => return none

/-- Based on Go: parser.go:3191 (parseParameter) -/
partial def parseParameter : ParserM Node :=
  do
    let pos ← nodePos
    skipDecorators
    -- Skip modifiers (public, private, protected, readonly)
    match (← currentToken) with
    | .publicKeyword | .privateKeyword | .protectedKeyword | .readonlyKeyword => nextToken
    | _ => pure ()
    let dotDotDot ← parseOptionalToken Kind.dotDotDotToken
    let name ← parseIdentifierOrPattern
    let questionToken ←
      match (← currentToken) with
      | .questionToken =>
        if dotDotDot.isSome then
          parseErrorAtCurrentToken Diagnostics.rest_parameter_cannot_be_optional
        parseOptionalToken Kind.questionToken
      | _ => pure none
    let typeNode ← parseTypeAnnotation
    let initializer ← parseInitializer
    finishNode (Node.parameterDeclaration {} dotDotDot name questionToken typeNode initializer) pos

/-- Based on Go: parser.go:3136 (parseParameters) -/
partial def parseParameters : ParserM (Array Node) :=
  do
    let ok ← parseExpected Kind.openParenToken
    if ok then
      let isParam : ParserM Bool := do
        let tok ← currentToken
        let bindId ← isBindingIdentifierToken
        return bindId || tok == Kind.dotDotDotToken ||
          tok == Kind.openBracketToken || tok == Kind.openBraceToken ||
          isModifierKind tok || tok == Kind.thisKeyword ||
          tok == Kind.atToken
      let params ← parseDelimitedList .parameters isParam (parseParameter)
      let _ ← parseExpected Kind.closeParenToken
      return params
    else return #[]

-- ---- Statement Parsing ----

/-- Based on Go: parser.go:1090 (parseBlock) -/
partial def parseBlock : ParserM Node :=
  do
    let pos ← nodePos
    let ok ← parseExpected Kind.openBraceToken
    if ok then
      let stmts ← parseList .blockStatements isStartOfStatement (parseStatement)
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
partial def parseIfStatement : ParserM Node :=
  do
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
partial def parseReturnStatement : ParserM Node :=
  do
    let pos ← nodePos
    let _ ← parseExpected Kind.returnKeyword
    let expr ← if !(← canParseSemicolon) then do
      let e ← parseExpressionAllowIn; pure (some e)
    else pure none
    let _ ← parseSemicolon
    finishNode (Node.returnStatement {} expr) pos

/-- Based on Go: parser.go:1401 (parseExpressionOrLabeledStatement) -/
partial def parseExpressionOrLabeledStatement : ParserM Node :=
  do
    let pos ← nodePos
    let expr ← parseExpression
    -- Check for labeled statement: identifier followed by ':'
    match (← currentToken) with
    | .colonToken =>
      match expr with
      | .identifier _ _ =>
        nextToken
        let stmt ← parseStatement
        return ← finishNode (Node.labeledStatement {} expr stmt) pos
      | _ => pure ()
    | _ => pure ()
    let _ ← parseSemicolon
    finishNode (Node.expressionStatement {} expr) pos

/-- Based on Go: parser.go:1289 (parseThrowStatement) -/
partial def parseThrowStatement : ParserM Node :=
  do
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
partial def parseWhileStatement : ParserM Node :=
  do
    let pos ← nodePos
    let _ ← parseExpected Kind.whileKeyword
    let _ ← parseExpected Kind.openParenToken
    let expr ← parseExpressionAllowIn
    let _ ← parseExpected Kind.closeParenToken
    let stmt ← parseStatement
    finishNode (Node.whileStatement {} expr stmt) pos

/-- Based on Go: parser.go:1141 (parseDoStatement) -/
partial def parseDoStatement : ParserM Node :=
  do
    let pos ← nodePos
    let _ ← parseExpected Kind.doKeyword
    let stmt ← parseStatement
    let _ ← parseExpected Kind.whileKeyword
    let _ ← parseExpected Kind.openParenToken
    let expr ← parseExpressionAllowIn
    let _ ← parseExpected Kind.closeParenToken
    let _ ← parseSemicolon
    finishNode (Node.doStatement {} stmt expr) pos

/-- Based on Go: parser.go:1160 (parseForStatement) -/
partial def parseForStatement : ParserM Node :=
  do
    let pos ← nodePos
    let _ ← parseExpected Kind.forKeyword
    let _ ← parseExpected Kind.openParenToken
    let initializer ← match (← currentToken) with
      | .semicolonToken => pure none
      | .varKeyword | .letKeyword | .constKeyword =>
        pure (some (← parseVariableDeclarationList))
      | _ => pure (some (← parseExpressionAllowIn))
    let tok ← currentToken
    match tok with
    | .inKeyword =>
      let _ ← parseExpected Kind.inKeyword
      let expr ← parseExpressionAllowIn
      let _ ← parseExpected Kind.closeParenToken
      let stmt ← parseStatement
      finishNode (Node.forInStatement {} initializer expr stmt) pos
    | .ofKeyword =>
      nextToken
      let expr ← parseExpressionAllowIn
      let _ ← parseExpected Kind.closeParenToken
      let stmt ← parseStatement
      finishNode (Node.forOfStatement {} initializer expr stmt) pos
    | _ =>
      let _ ← parseExpected Kind.semicolonToken
      let condition ← match (← currentToken) with
        | .semicolonToken => pure none
        | _ => pure (some (← parseExpressionAllowIn))
      let _ ← parseExpected Kind.semicolonToken
      let incrementor ← match (← currentToken) with
        | .closeParenToken => pure none
        | _ => pure (some (← parseExpressionAllowIn))
      let _ ← parseExpected Kind.closeParenToken
      let stmt ← parseStatement
      finishNode (Node.forStatement {} initializer condition incrementor stmt) pos

/-- Based on Go: parser.go:1305 (parseSwitchStatement) -/
partial def parseSwitchStatement : ParserM Node :=
  do
    let pos ← nodePos
    let _ ← parseExpected Kind.switchKeyword
    let _ ← parseExpected Kind.openParenToken
    let expr ← parseExpressionAllowIn
    let _ ← parseExpected Kind.closeParenToken
    let _ ← parseExpected Kind.openBraceToken
    let clauses ← parseSwitchClauses
    let _ ← parseExpected Kind.closeBraceToken
    finishNode (Node.switchStatement {} expr clauses) pos

/-- Helper: parse switch case/default clauses. -/
partial def parseSwitchClauses (acc : Array Node := #[]) : ParserM (Array Node) := do
      match (← currentToken) with
      | .closeBraceToken | .endOfFile => return acc
      | .caseKeyword =>
        let pos ← nodePos
        let _ ← parseExpected Kind.caseKeyword
        let expr ← parseExpressionAllowIn
        let _ ← parseExpected Kind.colonToken
        let stmts ← parseList .switchClauseStatements isStartOfStatement (parseStatement)
        let node ← finishNode (Node.caseClause {} expr stmts) pos
        parseSwitchClauses (acc.push node)
      | .defaultKeyword =>
        let pos ← nodePos
        let _ ← parseExpected Kind.defaultKeyword
        let _ ← parseExpected Kind.colonToken
        let stmts ← parseList .switchClauseStatements isStartOfStatement (parseStatement)
        let node ← finishNode (Node.defaultClause {} stmts) pos
        parseSwitchClauses (acc.push node)
      | _ =>
        nextToken
        parseSwitchClauses acc

/-- Based on Go: parser.go:1308 (parseTryStatement) -/
partial def parseTryStatement : ParserM Node :=
  do
    let pos ← nodePos
    let _ ← parseExpected Kind.tryKeyword
    let tryBlock ← parseBlock
    let catchClause ← match (← currentToken) with
      | .catchKeyword => do
        let cPos ← nodePos
        let _ ← parseExpected Kind.catchKeyword
        let decl ← match (← currentToken) with
          | .openParenToken => do
            let _ ← parseExpected Kind.openParenToken
            let name ← parseBindingIdentifier
            match (← currentToken) with
            | .lessThanLessThanToken => let _ ← reScanLessThanToken
            | _ => pure ()
            let typeNode ← parseTypeAnnotation
            let _ ← parseExpected Kind.closeParenToken
            pure (some (Node.variableDeclaration {} name typeNode none))
          | _ => pure none
        let block ← parseBlock
        let node ← finishNode (Node.catchClause {} decl block) cPos
        pure (some node)
      | _ => pure none
    let finallyBlock ← match (← currentToken) with
      | .finallyKeyword => do
        let _ ← parseExpected Kind.finallyKeyword
        pure (some (← parseBlock))
      | _ => pure none
    finishNode (Node.tryStatement {} tryBlock catchClause finallyBlock) pos

/-- Based on Go: parser.go:1131 (parseWithStatement) -/
partial def parseWithStatement : ParserM Node :=
  do
    let pos ← nodePos
    let _ ← parseExpected Kind.withKeyword
    let _ ← parseExpected Kind.openParenToken
    let expr ← parseExpressionAllowIn
    let _ ← parseExpected Kind.closeParenToken
    let stmt ← parseStatement
    finishNode (Node.withStatement {} expr stmt) pos

/-- Based on Go: parser.go:1581 (parseInitializer) -/
partial def parseInitializer : ParserM (Option Node) :=
  do
    if ← parseOptional Kind.equalsToken then
      pure (some (← parseAssignmentExpressionOrHigher))
    else return none

/-- Based on Go: parser.go:1514 (parseIdentifierOrPattern) -/
partial def parseIdentifierOrPattern : ParserM Node :=
  do
    match (← currentToken) with
    | .openBracketToken => parseArrayBindingPattern
    | .openBraceToken => parseObjectBindingPattern
    | _ => parseBindingIdentifier

/-- Based on Go: parser.go:1528 (parseArrayBindingPattern) -/
partial def parseArrayBindingPattern : ParserM Node :=
  do
    let pos ← nodePos
    let _ ← parseExpected Kind.openBracketToken
    let isElem : ParserM Bool := do
      let tok ← currentToken
      return tok == Kind.commaToken || tok != Kind.closeBracketToken
    let elements ← parseDelimitedList .arrayBindingElements isElem
      (parseArrayBindingElement)
    let _ ← parseExpected Kind.closeBracketToken
    finishNode (Node.arrayBindingPattern {} elements) pos

/-- Based on Go: parser.go:1539 (parseArrayBindingElement) -/
partial def parseArrayBindingElement : ParserM Node :=
  do
    match (← currentToken) with
    | .commaToken =>
      -- Elision (omitted element)
      let pos ← nodePos
      finishNode (Node.omittedExpression {}) pos
    | _ =>
      let pos ← nodePos
      let dotDotDot ← match (← currentToken) with
        | .dotDotDotToken => let n ← parseTokenNode; pure (some n)
        | _ => pure none
      let name ← parseIdentifierOrPattern
      let initializer ← parseInitializer
      finishNode (Node.bindingElement {} dotDotDot none name initializer) pos

/-- Based on Go: parser.go:1553 (parseObjectBindingPattern) -/
partial def parseObjectBindingPattern : ParserM Node :=
  do
    let pos ← nodePos
    let _ ← parseExpected Kind.openBraceToken
    let isElem : ParserM Bool := do
      let tok ← currentToken
      return tok != Kind.closeBraceToken
    let elements ← parseDelimitedList .objectBindingElements isElem
      (parseObjectBindingElement)
    let _ ← parseExpected Kind.closeBraceToken
    finishNode (Node.objectBindingPattern {} elements) pos

/-- Based on Go: parser.go:1565 (parseObjectBindingElement) -/
partial def parseObjectBindingElement : ParserM Node :=
  do
    let pos ← nodePos
    let dotDotDot ← match (← currentToken) with
      | .dotDotDotToken => let n ← parseTokenNode; pure (some n)
      | _ => pure none
    -- Check if this is propertyName: bindingElement
    let nameOrPropName ← parseIdentifierOrPattern
    let (propName, name) ← match (← currentToken) with
      | .colonToken => do
        nextToken
        let binding ← parseIdentifierOrPattern
        pure (some nameOrPropName, binding)
      | _ =>
        pure (none, nameOrPropName)
    let initializer ← parseInitializer
    finishNode (Node.bindingElement {} dotDotDot propName name initializer) pos

/-- Based on Go: parser.go:1495 (parseVariableDeclaration) -/
partial def parseVariableDeclaration : ParserM Node :=
  do
    let pos ← nodePos
    let name ← parseIdentifierOrPattern
    let typeNode ← parseTypeAnnotation
    let initializer ← parseInitializer
    finishNode (Node.variableDeclaration {} name typeNode initializer) pos

/-- Based on Go: parser.go:1434 (parseVariableDeclarationList) -/
partial def parseVariableDeclarationList : ParserM Node :=
  do
    let pos ← nodePos
    let tok ← currentToken
    let flags := match tok with
      | .letKeyword => NodeFlags.let_
      | .constKeyword => NodeFlags.const_
      | .usingKeyword => NodeFlags.using_
      | _ => NodeFlags.none
    nextToken
    let isDecl : ParserM Bool := do
      let bindId ← isBindingIdentifierToken
      let tok ← currentToken
      return bindId || tok == Kind.openBracketToken || tok == Kind.openBraceToken
    let decls ← parseDelimitedList .variableDeclarations isDecl (parseVariableDeclaration)
    finishNode (Node.variableDeclarationList {} flags decls) pos

/-- Based on Go: parser.go:1425 (parseVariableStatement) -/
partial def parseVariableStatement : ParserM Node :=
  do
    let pos ← nodePos
    let declList ← parseVariableDeclarationList
    let _ ← parseSemicolon
    finishNode (Node.variableStatement {} declList) pos

-- ---- Declaration Parsing ----

/-- Based on Go: parser.go:3370 (parseFunctionBlock) -/
partial def parseFunctionBlock : ParserM (Option Node) :=
  do
    let tok ← currentToken
    match tok with
    | .openBraceToken =>
      pure (some (← parseBlock))
    | _ =>
      if ← canParseSemicolon then
        let _ ← parseSemicolon
        return none
      else
        pure (some (← parseBlock))

/-- Based on Go: parser.go:1595 (parseFunctionDeclaration) -/
partial def parseFunctionDeclaration : ParserM Node :=
  do
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
partial def parsePropertyName : ParserM Node :=
  do
    let tok ← currentToken
    match tok with
    | .stringLiteral
    | .numericLiteral =>
      parseLiteralExpression
    | .openBracketToken =>
      -- Computed property name: [expr]
      let pos ← nodePos
      let _ ← parseExpected Kind.openBracketToken
      let expr ← parseExpressionAllowIn
      let _ ← parseExpected Kind.closeBracketToken
      finishNode (Node.computedPropertyName {} expr) pos
    | _ =>
      parseIdentifierName

partial def isParserClassMemberModifier (tok : Kind) : Bool :=
  match tok with
  | .staticKeyword
  | .readonlyKeyword
  | .abstractKeyword
  | .asyncKeyword
  | .publicKeyword
  | .privateKeyword
  | .protectedKeyword
  | .accessorKeyword
  | .overrideKeyword
  | .declareKeyword => true
  | _ => false

partial def isParserClassMemberModifierNoDeclare (tok : Kind) : Bool :=
  match tok with
  | .staticKeyword
  | .readonlyKeyword
  | .abstractKeyword
  | .asyncKeyword
  | .publicKeyword
  | .privateKeyword
  | .protectedKeyword
  | .accessorKeyword
  | .overrideKeyword => true
  | _ => false

partial def isParserClassMemberModifierThird (tok : Kind) : Bool :=
  match tok with
  | .staticKeyword
  | .readonlyKeyword
  | .abstractKeyword
  | .asyncKeyword => true
  | _ => false

/-- Based on Go: parser.go:1833 (parseMethodDeclaration) rest -/
partial def parseMethodDeclarationRest (pos : Nat) (name : Node)
    (questionToken : Option Node) : ParserM Node :=
  do
    let typeParams ← parseTypeParameters
    let params ← parseParameters
    let returnType ← parseReturnType
    let body ← parseFunctionBlock
    finishNode (Node.methodDeclaration {} name questionToken typeParams params returnType body) pos

/-- Based on Go: parser.go:1821 (parsePropertyOrMethodDeclaration) -/
partial def parsePropertyOrMethodDeclaration : ParserM Node :=
  do
    let pos ← nodePos
    -- Skip modifiers (static, readonly, abstract, async, public, private, protected, accessor, override)
    let tok0 ← currentToken
    if isParserClassMemberModifier tok0 then
      nextToken
      -- Second modifier
      let tok1 ← currentToken
      if isParserClassMemberModifierNoDeclare tok1 then
        nextToken
        -- Third modifier
        let tok2 ← currentToken
        if isParserClassMemberModifierThird tok2 then
          nextToken
    let memberTok ← currentToken
    match memberTok with
    | .constructorKeyword =>
      nextToken
      let params ← parseParameters
      let body ← parseFunctionBlock
      finishNode (Node.constructor_ {} params body) pos
    | .getKeyword
    | .setKeyword =>
      let _accessorKind ← currentToken
      nextToken
      let name ← parsePropertyName
      let questionToken ← parseOptionalToken Kind.questionToken
      parseMethodDeclarationRest pos name questionToken
    | .asteriskToken =>
      nextToken
      let name ← parsePropertyName
      let questionToken ← parseOptionalToken Kind.questionToken
      parseMethodDeclarationRest pos name questionToken
    | _ =>
      let name ← parsePropertyName
      let questionToken ← parseOptionalToken Kind.questionToken
      let _ ← parseOptionalToken Kind.exclamationToken
      let tok ← currentToken
      match tok with
      | .openParenToken
      | .lessThanToken =>
        parseMethodDeclarationRest pos name questionToken
      | _ =>
        let typeNode ← parseTypeAnnotation
        let initializer ← parseInitializer
        let _ ← parseSemicolon
        finishNode (Node.propertyDeclaration {} name questionToken typeNode initializer) pos

/-- Based on Go: parser.go:1728 (parseClassElement) -/
partial def parseClassElement : ParserM Node :=
  do
    let pos ← nodePos
    skipDecorators
    let tok ← currentToken
    match tok with
    | .semicolonToken =>
      nextToken
      finishNode (Node.semicolonClassElement {}) pos
    | _ =>
      parsePropertyOrMethodDeclaration

/-- Parse heritage clauses (extends, implements). -/
partial def parseHeritageClauses (acc : Array Node := #[]) : ParserM (Option (Array Node)) := do
    let tok ← currentToken
    match tok with
    | .extendsKeyword
    | .implementsKeyword =>
      let pos ← nodePos
      let clauseToken ← currentToken
      nextToken
      let isElem : ParserM Bool := isStartOfExpression
      let types ← parseDelimitedList .heritageClauseElement isElem do
        let ePos ← nodePos
        let expr ← parseLeftHandSideExpressionOrHigher
        let typeArgs ← match (← currentToken) with
          | .lessThanToken => do
            let _ ← parseExpected Kind.lessThanToken
            let args ← parseDelimitedList .typeArguments isStartOfType (parseType')
            let _ ← parseExpected Kind.greaterThanToken
            pure (some args)
          | _ => pure none
        finishNode (Node.expressionWithTypeArguments {} expr typeArgs) ePos
      let clause ← finishNode (Node.heritageClause {} clauseToken types) pos
      parseHeritageClauses (acc.push clause)
    | _ =>
      if acc.isEmpty then return none
      else return some acc

/-- Based on Go: parser.go:1619 (parseClassDeclaration) -/
partial def parseClassDeclaration : ParserM Node :=
  do
    let pos ← nodePos
    let _ ← parseExpected Kind.classKeyword
    let name ← if ← isBindingIdentifierToken then do
      match (← currentToken) with
      | .extendsKeyword | .implementsKeyword | .openBraceToken => pure none
      | _ =>
        let n ← parseBindingIdentifier
        pure (some n)
    else pure none
    let typeParams ← parseTypeParameters
    let heritageClauses ← parseHeritageClauses
    let ok ← parseExpected Kind.openBraceToken
    let members ← if ok then
      let isClassElem : ParserM Bool := do
        let tok ← currentToken
        return tok != Kind.closeBraceToken && tok != Kind.endOfFile
      parseList .classMembers isClassElem (parseClassElement)
    else pure #[]
    let _ ← parseExpected Kind.closeBraceToken
    finishNode (Node.classDeclaration {} name typeParams heritageClauses members) pos

/-- Based on Go: parser.go:1964 (parseInterfaceDeclaration) -/
partial def parseInterfaceDeclaration : ParserM Node :=
  do
    let pos ← nodePos
    let _ ← parseExpected Kind.interfaceKeyword
    let name ← parseIdentifier
    let typeParams ← parseTypeParameters
    let heritageClauses ← parseHeritageClauses
    let _ ← parseExpected Kind.openBraceToken
    let members ← parseList .typeMembers isTypeMemberStart (parseTypeMember)
    let _ ← parseExpected Kind.closeBraceToken
    finishNode (Node.interfaceDeclaration {} name typeParams heritageClauses members) pos

/-- Based on Go: parser.go:1976 (parseTypeAliasDeclaration) -/
partial def parseTypeAliasDeclaration : ParserM Node :=
  do
    let pos ← nodePos
    let _ ← parseExpected Kind.typeKeyword
    let name ← parseIdentifier
    let typeParams ← parseTypeParameters
    let _ ← parseExpected Kind.equalsToken
    let typeNode ← parseType'
    let _ ← parseSemicolon
    finishNode (Node.typeAliasDeclaration {} name typeParams typeNode) pos

/-- Based on Go: parser.go:2015 (parseEnumDeclaration) -/
partial def parseEnumDeclaration : ParserM Node :=
  do
    let pos ← nodePos
    -- Skip 'const' if present (const enum)
    let _ ← parseOptional Kind.constKeyword
    let _ ← parseExpected Kind.enumKeyword
    let name ← parseIdentifier
    let _ ← parseExpected Kind.openBraceToken
    let isEnumMember : ParserM Bool := do
      let tok ← currentToken
      return tok == Kind.identifier || tok == Kind.stringLiteral ||
        tok == Kind.numericLiteral || tok == Kind.openBracketToken ||
        Kind.isKeywordKind tok
    let members ← parseDelimitedList .enumMembers isEnumMember do
      let mPos ← nodePos
      let mName ← parsePropertyName
      let init ← parseInitializer
      finishNode (Node.enumMember {} mName init) mPos
    let _ ← parseExpected Kind.closeBraceToken
    finishNode (Node.enumDeclaration {} name members) pos

/-- Based on Go: parser.go:2036 (parseModuleDeclaration) -/
partial def parseModuleDeclaration : ParserM Node :=
  do
    let pos ← nodePos
    let tok ← currentToken
    -- Based on Go: parser.go:2036-2074
    match tok with
    | .globalKeyword =>
      -- global augmentation: `declare global { }`
      let name ← parseIdentifier
      let body ← match (← currentToken) with
        | .openBraceToken => do
          let bPos ← nodePos
          let _ ← parseExpected Kind.openBraceToken
          let stmts ← parseList .blockStatements isStartOfStatement (parseStatement)
          let _ ← parseExpected Kind.closeBraceToken
          let mb ← finishNode (Node.moduleBlock {} stmts) bPos
          pure (some mb)
        | _ =>
          let _ ← parseSemicolon
          pure none
      return ← finishNode (Node.moduleDeclaration {} name body) pos
    -- module or namespace keyword
    | .moduleKeyword | .namespaceKeyword => nextToken
    | _ => pure ()
    -- Parse name (identifier or string literal for ambient module)
    let name ← match (← currentToken) with
      | .stringLiteral => parseLiteralExpression
      | _ =>
        let first ← parseIdentifier
        -- Handle dotted names: A.B.C
        parseQualifiedNameRest first pos
    -- Parse body
    let body ← match (← currentToken) with
      | .openBraceToken => do
        let bPos ← nodePos
        let _ ← parseExpected Kind.openBraceToken
        let stmts ← parseList .blockStatements isStartOfStatement (parseStatement)
        let _ ← parseExpected Kind.closeBraceToken
        let mb ← finishNode (Node.moduleBlock {} stmts) bPos
        pure (some mb)
      | .dotToken =>
        -- Nested: namespace A.B { } — inner module
        nextToken
        let inner ← parseModuleDeclaration
        pure (some inner)
      | _ =>
        let _ ← parseSemicolon
        pure none
    finishNode (Node.moduleDeclaration {} name body) pos

-- ---- Import/Export Parsing ----

/-- Based on Go: parser.go:2943 (parseImportAttribute) -/
partial def parseImportAttribute : ParserM Node := do
  let pos ← nodePos
  let name ← match (← currentToken) with
    | .stringLiteral => parseLiteralExpression
    | _ => parseIdentifierName
  let _ ← parseExpected Kind.colonToken
  let value ← parseAssignmentExpressionOrHigher
  finishNode (Node.importAttribute {} name value) pos

/-- Based on Go: parser.go:2380 (tryParseImportAttributes)
    Skip optional `with { ... }` or `assert { ... }` after module specifier. -/
partial def tryParseImportAttributes : ParserM Unit := do
  match (← currentToken) with
  | .withKeyword =>
    nextToken
    let _ ← parseExpected Kind.openBraceToken
    let isAttr : ParserM Bool := do
      let t ← currentToken
      return t == Kind.identifier || t == Kind.stringLiteral || Kind.isKeywordKind t
    let _ ← parseDelimitedList .importAttributes isAttr parseImportAttribute
    let _ ← parseExpected Kind.closeBraceToken
  | .assertKeyword =>
    if !(← get).scanner.hasPrecedingLineBreak then
      nextToken
      let _ ← parseExpected Kind.openBraceToken
      let isAttr : ParserM Bool := do
        let t ← currentToken
        return t == Kind.identifier || t == Kind.stringLiteral || Kind.isKeywordKind t
      let _ ← parseDelimitedList .importAttributes isAttr parseImportAttribute
      let _ ← parseExpected Kind.closeBraceToken
  | _ => pure ()

/-- Based on Go: parser.go:2292 (parseImportOrExportSpecifier) -/
partial def parseImportOrExportSpecifier : ParserM Node := do
  let pos ← nodePos
  let first ← parseIdentifierName
  match (← currentToken) with
  | .asKeyword =>
    nextToken
    let second ← parseIdentifierName
    finishNode (Node.importSpecifier {} (some first) second) pos
  | _ =>
    finishNode (Node.importSpecifier {} none first) pos

/-- Based on Go: parser.go:2228 (parseNamedImports) -/
partial def parseNamedImportsOrExports (isImport : Bool) : ParserM Node :=
  do
    let pos ← nodePos
    let _ ← parseExpected Kind.openBraceToken
    let isSpec : ParserM Bool := do
      let tok ← currentToken
      return tok == Kind.identifier || Kind.isKeywordKind tok
    let specs ← parseDelimitedList .importOrExportSpecifiers isSpec
      (parseImportOrExportSpecifier)
    let _ ← parseExpected Kind.closeBraceToken
    if isImport then finishNode (Node.namedImports {} specs) pos
    else finishNode (Node.namedExports {} specs) pos

/-- Based on Go: parser.go:2113 (parseImportDeclaration) -/
partial def parseImportDeclaration : ParserM Node :=
  do
    let pos ← nodePos
    let _ ← parseExpected Kind.importKeyword
    -- Skip 'type' modifier if present
    let tok ← currentToken
    match tok with
    | .typeKeyword =>
      let isTypeOnly ← lookAhead do
        nextToken
        let t ← currentToken
        -- "import type X" or "import type { X }" or "import type * as X"
        return t == Kind.identifier || t == Kind.openBraceToken || t == Kind.asteriskToken
      if isTypeOnly then nextToken
    | _ =>
      pure ()
    let tok ← currentToken
    match tok with
    -- import "module" (side-effect import)
    | .stringLiteral =>
      let moduleSpec ← parseLiteralExpression
      tryParseImportAttributes
      let _ ← parseSemicolon
      finishNode (Node.importDeclaration {} none moduleSpec) pos
    -- import { named } from "module"
    | .openBraceToken =>
      let namedImports ← parseNamedImportsOrExports true
      let clausePos := pos
      let clause ← finishNode (Node.importClause {} none (some namedImports)) clausePos
      let _ ← parseExpected Kind.fromKeyword
      let moduleSpec ← parseLiteralExpression
      tryParseImportAttributes
      let _ ← parseSemicolon
      finishNode (Node.importDeclaration {} (some clause) moduleSpec) pos
    -- import * as name from "module"
    | .asteriskToken =>
      nextToken
      let _ ← parseExpected Kind.asKeyword
      let name ← parseBindingIdentifier
      let nsImport ← finishNode (Node.namespaceImport {} name) pos
      let clause ← finishNode (Node.importClause {} none (some nsImport)) pos
      let _ ← parseExpected Kind.fromKeyword
      let moduleSpec ← parseLiteralExpression
      tryParseImportAttributes
      let _ ← parseSemicolon
      finishNode (Node.importDeclaration {} (some clause) moduleSpec) pos
    | _ =>
      if ← isBindingIdentifierToken then
        -- Lookahead for import X = ...
        let isImportEquals ← lookAhead do
          nextToken
          return (← currentToken) == Kind.equalsToken
        if isImportEquals then
          let name ← parseBindingIdentifier
          let _ ← parseExpected Kind.equalsToken
          -- require("module") or entity name
          let moduleRef ← match (← currentToken) with
            | .requireKeyword => do
              let rPos ← nodePos
              nextToken
              let _ ← parseExpected Kind.openParenToken
              let expr ← parseLiteralExpression
              let _ ← parseExpected Kind.closeParenToken
              finishNode (Node.externalModuleReference {} expr) rPos
            | _ =>
              let qPos ← nodePos
              let first ← parseIdentifier
              parseQualifiedNameRest first qPos
          let _ ← parseSemicolon
          finishNode (Node.importEqualsDeclaration {} name moduleRef) pos
        else
          -- import defaultExport from "module" or import defaultExport, { named } from "module"
          let importClause ← parseImportClause
          let _ ← parseExpected Kind.fromKeyword
          let moduleSpec ← parseLiteralExpression
          tryParseImportAttributes
          let _ ← parseSemicolon
          finishNode (Node.importDeclaration {} (some importClause) moduleSpec) pos
      else
        parseErrorAtCurrentToken Diagnostics.declaration_or_statement_expected
        nextToken
        finishNode (Node.missing {} Kind.importDeclaration) pos

/-- Parse import clause (default import + optional named bindings). -/
partial def parseImportClause : ParserM Node :=
  do
    let pos ← nodePos
    let defaultImport ← parseBindingIdentifier
    let namedBindings ← match (← currentToken) with
      | .commaToken =>
        nextToken
        match (← currentToken) with
        | .openBraceToken =>
          pure (some (← parseNamedImportsOrExports true))
        | .asteriskToken =>
          nextToken
          let _ ← parseExpected Kind.asKeyword
          let name ← parseBindingIdentifier
          let nsImport ← finishNode (Node.namespaceImport {} name) pos
          pure (some nsImport)
        | _ => pure none
      | _ => pure none
    finishNode (Node.importClause {} (some defaultImport) namedBindings) pos

/-- Based on Go: parser.go:2420 (parseExportDeclaration) -/
partial def parseExportDeclarationOrAssignment : ParserM Node :=
  do
    let pos ← nodePos
    let _ ← parseExpected Kind.exportKeyword
    let tok ← currentToken
    -- Skip 'type' modifier if present
    let tok ← match tok with
      | .typeKeyword => do
        let isTypeOnly ← lookAhead do
          nextToken
          let t ← currentToken
          return t == Kind.openBraceToken || t == Kind.asteriskToken
        if isTypeOnly then nextToken; currentToken
        else pure tok
      | _ => pure tok
    match tok with
    -- export default
    | .defaultKeyword =>
      nextToken
      let tok' ← currentToken
      let expr ← match tok' with
        | .functionKeyword => parseFunctionDeclaration
        | .classKeyword => parseClassDeclaration
        | .abstractKeyword =>
          -- abstract class
          nextToken
          parseClassDeclaration
        | .interfaceKeyword => parseInterfaceDeclaration
        | _ => parseAssignmentExpressionOrHigher
      let _ ← tryParseSemicolon
      finishNode (Node.exportAssignment {} expr) pos
    -- export =
    | .equalsToken =>
      nextToken
      let expr ← parseAssignmentExpressionOrHigher
      let _ ← parseSemicolon
      finishNode (Node.exportAssignment {} expr) pos
    -- export * from "module"
    | .asteriskToken =>
      nextToken
      -- export * as ns from "module"
      match (← currentToken) with
      | .asKeyword =>
        nextToken
        let name ← parseIdentifierName
        let nsExport ← finishNode (Node.namespaceExport {} name) pos
        let _ ← parseExpected Kind.fromKeyword
        let moduleSpec ← parseLiteralExpression
        tryParseImportAttributes
        let _ ← parseSemicolon
        finishNode (Node.exportDeclaration {} (some nsExport) (some moduleSpec)) pos
      | _ =>
        let _ ← parseExpected Kind.fromKeyword
        let moduleSpec ← parseLiteralExpression
        tryParseImportAttributes
        let _ ← parseSemicolon
        finishNode (Node.exportDeclaration {} none (some moduleSpec)) pos
    -- export { named } or export { named } from "module"
    | .openBraceToken =>
      let namedExports ← parseNamedImportsOrExports false
      let moduleSpec ← match (← currentToken) with
        | .fromKeyword => do
          nextToken
          pure (some (← parseLiteralExpression))
        | _ => pure none
      if moduleSpec.isSome then tryParseImportAttributes
      let _ ← parseSemicolon
      finishNode (Node.exportDeclaration {} (some namedExports) moduleSpec) pos
    -- export [declaration]
    | _ =>
      let decl ← parseDeclarationAfterModifiers
      finishNode (Node.exportDeclaration {} (some decl) none) pos

/-- Parse a declaration after modifiers have been consumed. -/
partial def parseDeclarationAfterModifiers : ParserM Node :=
  do
    let tok ← currentToken
    match tok with
    | .constKeyword =>
      let isConstEnum ← lookAhead do
        nextToken
        return (← currentToken) == Kind.enumKeyword
      if isConstEnum then
        nextToken
        parseEnumDeclaration
      else
        parseVariableStatement
    | .varKeyword
    | .letKeyword =>
      parseVariableStatement
    | .functionKeyword => parseFunctionDeclaration
    | .classKeyword => parseClassDeclaration
    | .interfaceKeyword => parseInterfaceDeclaration
    | .typeKeyword => parseTypeAliasDeclaration
    | .enumKeyword => parseEnumDeclaration
    | .moduleKeyword
    | .namespaceKeyword
    | .globalKeyword =>
      parseModuleDeclaration
    | .asyncKeyword =>
      nextToken
      parseFunctionDeclaration
    | .abstractKeyword =>
      nextToken
      parseClassDeclaration
    | .declareKeyword =>
      nextToken
      parseDeclarationAfterModifiers
    | _ =>
      -- Fallback: parse as expression statement
      parseExpressionOrLabeledStatement

/-- Based on Go: parser.go:945 (parseStatement) — dispatch on token -/
partial def parseStatement : ParserM Node :=
  do
    let tok ← currentToken
    match tok with
    | .semicolonToken => parseEmptyStatement
    | .openBraceToken => parseBlock
    | .constKeyword =>
      -- Based on Go: parser.go:3837 — const is modifier only if followed by enum
      let isConstEnum ← lookAhead do
        nextToken
        return (← currentToken) == Kind.enumKeyword
      if isConstEnum then
        nextToken  -- skip 'const'
        parseEnumDeclaration
      else
        parseVariableStatement
    | .varKeyword
    | .letKeyword =>
      parseVariableStatement
    | .functionKeyword => parseFunctionDeclaration
    | .classKeyword => parseClassDeclaration
    | .ifKeyword => parseIfStatement
    | .returnKeyword => parseReturnStatement
    | .throwKeyword => parseThrowStatement
    | .breakKeyword => parseBreakStatement
    | .continueKeyword => parseContinueStatement
    | .debuggerKeyword => parseDebuggerStatement
    | .whileKeyword => parseWhileStatement
    | .doKeyword => parseDoStatement
    | .forKeyword => parseForStatement
    | .switchKeyword => parseSwitchStatement
    | .tryKeyword => parseTryStatement
    | .withKeyword => parseWithStatement
    -- Declaration keywords
    | .exportKeyword => parseExportDeclarationOrAssignment
    | .importKeyword => parseImportDeclaration
    | .interfaceKeyword => parseInterfaceDeclaration
    | .typeKeyword =>
      -- 'type' can be an identifier in expression position
      let isTypeAlias ← lookAhead do
        nextToken
        let t ← currentToken
        return t == Kind.identifier || (Kind.isKeywordKind t && !Kind.isReservedWord t)
      if isTypeAlias then parseTypeAliasDeclaration
      else parseExpressionOrLabeledStatement
    | .enumKeyword => parseEnumDeclaration
    | .moduleKeyword
    | .namespaceKeyword =>
      let isModuleDecl ← lookAhead do
        nextToken
        let t ← currentToken
        return t == Kind.stringLiteral || t == Kind.identifier ||
          (Kind.isKeywordKind t && !Kind.isReservedWord t)
      if isModuleDecl then parseModuleDeclaration
      else parseExpressionOrLabeledStatement
    | .abstractKeyword =>
      nextToken
      match (← currentToken) with
      | .classKeyword => parseClassDeclaration
      | _ => parseExpressionOrLabeledStatement
    | .declareKeyword =>
      nextToken
      parseDeclarationAfterModifiers
    | .asyncKeyword =>
      let isAsyncFunc ← lookAhead do
        nextToken
        return (← currentToken) == Kind.functionKeyword
      if isAsyncFunc then
        nextToken  -- skip 'async'
        parseFunctionDeclaration
      else parseExpressionOrLabeledStatement
    -- Decorator: @expr class/function
    | .atToken =>
      -- Skip decorators until we hit the declaration
      skipDecorators
      -- After decorators, parse the declaration
      let tok2 ← currentToken
      match tok2 with
      | .exportKeyword => parseExportDeclarationOrAssignment
      | .abstractKeyword =>
        nextToken
        parseClassDeclaration
      | .classKeyword => parseClassDeclaration
      | .functionKeyword => parseFunctionDeclaration
      | .declareKeyword =>
        nextToken
        parseDeclarationAfterModifiers
      | _ =>
        parseExpressionOrLabeledStatement
    | _ =>
      parseExpressionOrLabeledStatement

-- ---- Entry Point ----

/-- Based on Go: parser.go:336 (parseSourceFileWorker) -/
partial def parseSourceFileWorker : ParserM Node :=
  do
    let pos ← nodePos
    let isStmtNotEof : ParserM Bool := do
      match (← currentToken) with
      | .endOfFile => return false
      | _ => isStartOfStatement
    let stmts ← parseList .sourceElements isStmtNotEof (parseStatement)
    let eof ← parseTokenNode
    finishNode (Node.sourceFile {} stmts eof) pos

end -- mutual

-- ============================================================
-- Section: Public Entry Point
-- Based on Go: parser.go:114-390
-- ============================================================

/-- Initialize a parser from source text. -/
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

/-- ASCII whitespace for lightweight JSDoc scanning. -/
@[inline] private def isAsciiWhitespaceByte (b : UInt8) : Bool :=
  b == 0x20 || b == 0x09 || b == 0x0A || b == 0x0D || b == 0x0C

/-- Find `pat` in `bytes` starting at `start`, searching up to (but not including) `stop`. -/
private partial def findSubarrayBounded
    (bytes : ByteArray) (pat : ByteArray) (start stop : Nat) : Option Nat :=
  if pat.size == 0 || start >= stop then
    none
  else
    let maxStart := stop - pat.size
    let rec go (i : Nat) : Option Nat :=
      if i > maxStart then
        none
      else
        let rec matchesAt (j : Nat) : Bool :=
          if j >= pat.size then true
          else if bytes[i + j]! == pat[j]! then matchesAt (j + 1)
          else false
        if matchesAt 0 then some i else go (i + 1)
    go start

/-- Skip ASCII whitespace in `bytes` from `start` up to (but not including) `stop`. -/
private partial def skipAsciiWhitespace
    (bytes : ByteArray) (start stop : Nat) : Nat :=
  if start < stop && isAsciiWhitespaceByte bytes[start]! then
    skipAsciiWhitespace bytes (start + 1) stop
  else
    start

/-- Scan `@type` tags within one JSDoc comment span and collect TS1110 diagnostics
    for inline-tag starts (`{@...}`). -/
private partial def collectJsDocTypeTagDiagnostics
    (bytes typePat bracePat : ByteArray)
    (searchPos commentEnd : Nat)
    (acc : Array Diagnostic) : Array Diagnostic :=
  match findSubarrayBounded bytes typePat searchPos commentEnd with
  | none => acc
  | some typeIdx =>
    let afterType := typeIdx + typePat.size
    let acc' :=
      match findSubarrayBounded bytes bracePat afterType commentEnd with
      | none => acc
      | some openBraceIdx =>
        let typeStart := skipAsciiWhitespace bytes (openBraceIdx + 1) commentEnd
        if typeStart < commentEnd && bytes[typeStart]! == 0x40 then
          acc.push
            { loc := TextRange.mk' typeStart (typeStart + 1)
            , message := Diagnostics.type_expected
            , args := #[] }
        else acc
    collectJsDocTypeTagDiagnostics
      bytes typePat bracePat (typeIdx + typePat.size) commentEnd acc'

/-- Scan all JSDoc comments and collect TS1110 diagnostics for invalid `@type` inline tags. -/
private partial def collectJsDocCommentsDiagnostics
    (bytes openPat closePat typePat bracePat : ByteArray)
    (searchPos : Nat)
    (acc : Array Diagnostic) : Array Diagnostic :=
  if searchPos + openPat.size > bytes.size then
    acc
  else
    match findSubarrayBounded bytes openPat searchPos bytes.size with
    | none => acc
    | some openIdx =>
      match findSubarrayBounded bytes closePat (openIdx + openPat.size) bytes.size with
      | none => acc
      | some closeIdx =>
        let acc' := collectJsDocTypeTagDiagnostics
          bytes typePat bracePat (openIdx + openPat.size) closeIdx acc
        collectJsDocCommentsDiagnostics
          bytes openPat closePat typePat bracePat (closeIdx + closePat.size) acc'

/-- Add TS1110 diagnostics for invalid JSDoc `@type` forms where the type
    expression starts with an inline tag (`{@...}`).
    This covers cases like `/** @type {@import("a").Type} */`. -/
private def collectJsDocTypeDiagnostics (sourceText : String) : Array Diagnostic :=
  let bytes := sourceText.toUTF8
  let openPat := "/**".toUTF8
  let closePat := "*/".toUTF8
  let typePat := "@type".toUTF8
  let bracePat := "{".toUTF8
  collectJsDocCommentsDiagnostics bytes openPat closePat typePat bracePat 0 #[]

/-- Based on Go: parser.go:114 (ParseSourceFile) -/
def parseSourceFile (_fileName : String) (sourceText : String)
    (scriptKind : ScriptKind) : ParseResult :=
  let p := Parser.initializeState sourceText scriptKind
  let action : ParserM Node := do nextToken; parseSourceFileWorker
  let (result, p) := action |>.run p
  { sourceFile := result
  , diagnostics := p.diagnostics ++ collectJsDocTypeDiagnostics sourceText }

end TSLean.Compiler
