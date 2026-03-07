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
    let startPos := Int32.ofNat start
    let loc := TextRange.mk' (Int.ofNat start) (Int.ofNat (start + len))
    let diagnostics :=
      if let some last := p.diagnostics.back? then
        if last.loc.pos == startPos then p.diagnostics
        else p.diagnostics.push { loc := loc, message := msg, args := args }
      else
        p.diagnostics.push { loc := loc, message := msg, args := args }
    { p with diagnostics := diagnostics, hasParseError := true }

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

/-- Based on Go: parser.go:2870 (reScanSlashToken) -/
partial def reScanSlashToken : ParserM Kind := do
  modify fun p =>
    let s := p.scanner.reScanSlashToken
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
  else
    let tok ← currentToken
    if tok == Kind.privateIdentifier then
      parseErrorAtCurrentToken Diagnostics.private_identifiers_not_allowed
    else if Kind.isReservedWord tok then
      parseErrorAtCurrentToken Diagnostics.identifier_expected_reserved #[tokenToString tok]
    else
      parseErrorAtCurrentToken Diagnostics.identifier_expected
    let pos ← nodePos
    finishNode (Node.missing {} Kind.identifier) pos

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
  if tok == Kind.endOfFile then
    return true
  match kind with
  | .sourceElements => return tok == Kind.endOfFile
  | .blockStatements => return tok == Kind.closeBraceToken
  | .switchClauses => return tok == Kind.closeBraceToken
  | .switchClauseStatements =>
    return tok == Kind.caseKeyword || tok == Kind.defaultKeyword || tok == Kind.closeBraceToken
  | .typeMembers => return tok == Kind.closeBraceToken
  | .classMembers => return tok == Kind.closeBraceToken
  | .enumMembers => return tok == Kind.closeBraceToken
  | .heritageClauseElement =>
    return tok == Kind.openBraceToken || tok == Kind.extendsKeyword || tok == Kind.implementsKeyword
  | .variableDeclarations =>
    return tok == Kind.inKeyword || tok == Kind.ofKeyword || tok == Kind.equalsGreaterThanToken ||
      (← canParseSemicolon)
  | .objectBindingElements => return tok == Kind.closeBraceToken
  | .arrayBindingElements => return tok == Kind.closeBracketToken
  | .argumentExpressions => return tok == Kind.closeParenToken || tok == Kind.semicolonToken
  | .objectLiteralMembers => return tok == Kind.closeBraceToken
  | .jsxAttributes => return tok == Kind.greaterThanToken || tok == Kind.slashToken
  | .jsxChildren =>
    return tok == Kind.lessThanToken && (← lookAhead do nextToken; return (← currentToken) == Kind.slashToken)
  | .arrayLiteralMembers => return tok == Kind.closeBracketToken
  | .parameters => return tok == Kind.closeParenToken || tok == Kind.closeBracketToken
  | .jsDocParameters => return tok == Kind.closeParenToken || tok == Kind.closeBracketToken
  | .restProperties => return tok == Kind.closeParenToken || tok == Kind.closeBracketToken
  | .typeParameters =>
    return tok == Kind.greaterThanToken || tok == Kind.openParenToken || tok == Kind.openBraceToken
  | .typeArguments => return tok != Kind.commaToken
  | .tupleElementTypes => return tok == Kind.closeBracketToken
  | .heritageClauses => return tok == Kind.openBraceToken || tok == Kind.closeBraceToken
  | .importOrExportSpecifiers => return tok == Kind.closeBraceToken
  | .importAttributes => return tok == Kind.closeBraceToken
  | .jsDocComment => return false

partial def isLiteralPropertyName : ParserM Bool := do
  let tok ← currentToken
  return tok == Kind.identifier || tok == Kind.stringLiteral || tok == Kind.numericLiteral || Kind.isKeywordKind tok

partial def isBindingIdentifierOrPrivateIdentifierOrPattern : ParserM Bool := do
  let tok ← currentToken
  if tok == Kind.privateIdentifier || tok == Kind.openBracketToken || tok == Kind.openBraceToken then
    return true
  isBindingIdentifierToken

partial def isImportAttributeName : ParserM Bool := do
  let tok ← currentToken
  return tok == Kind.stringLiteral || tok == Kind.identifier || Kind.isKeywordKind tok

partial def isHeritageClause : ParserM Bool := do
  let tok ← currentToken
  return tok == Kind.extendsKeyword || tok == Kind.implementsKeyword

partial def isStartOfParameterToken : ParserM Bool := do
  let tok ← currentToken
  if tok == Kind.dotDotDotToken || tok == Kind.atToken || tok == Kind.thisKeyword then
    return true
  if tok == Kind.openBracketToken || tok == Kind.openBraceToken || tok == Kind.privateIdentifier then
    return true
  if isModifierKind tok then
    return true
  if ← isBindingIdentifierToken then
    return true
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

partial def canFollowModifierToken : ParserM Bool := do
  let tok ← currentToken
  return tok == Kind.openBracketToken || tok == Kind.openBraceToken || tok == Kind.asteriskToken ||
    tok == Kind.dotDotDotToken || (← isLiteralPropertyName)

partial def canFollowGetOrSetKeyword : ParserM Bool := do
  let tok ← currentToken
  return tok == Kind.openBracketToken || (← isLiteralPropertyName)

partial def canFollowExportModifier : ParserM Bool := do
  let tok ← currentToken
  return tok == Kind.atToken ||
    (tok != Kind.asteriskToken && tok != Kind.asKeyword && tok != Kind.openBraceToken &&
      (← canFollowModifierToken))

partial def nextTokenIsIdentifierOrKeywordOrLiteralOnSameLine : ParserM Bool :=
  lookAhead do
    nextToken
    let tok ← currentToken
    return (tok == Kind.identifier || Kind.isKeywordKind tok || tok == Kind.numericLiteral ||
      tok == Kind.bigIntLiteral || tok == Kind.stringLiteral) &&
      !((← get).scanner.hasPrecedingLineBreak)

partial def nextTokenIsClassKeywordOnSameLine : ParserM Bool :=
  lookAhead do
    nextToken
    return (← currentToken) == Kind.classKeyword && !((← get).scanner.hasPrecedingLineBreak)

partial def nextTokenIsFunctionKeywordOnSameLine : ParserM Bool :=
  lookAhead do
    nextToken
    return (← currentToken) == Kind.functionKeyword && !((← get).scanner.hasPrecedingLineBreak)

partial def nextTokenCanFollowDefaultKeyword : ParserM Bool :=
  lookAhead do
    nextToken
    match (← currentToken) with
    | .classKeyword | .functionKeyword | .interfaceKeyword | .atToken =>
      return true
    | .abstractKeyword =>
      return (← nextTokenIsClassKeywordOnSameLine)
    | .asyncKeyword =>
      return (← nextTokenIsFunctionKeywordOnSameLine)
    | _ =>
      return false

partial def nextTokenCanFollowExportModifier : ParserM Bool :=
  lookAhead do
    nextToken
    return (← canFollowExportModifier)

partial def nextTokenIsOnSameLineAndCanFollowModifier : ParserM Bool :=
  lookAhead do
    nextToken
    if (← get).scanner.hasPrecedingLineBreak then
      return false
    canFollowModifierToken

partial def nextTokenCanFollowModifier : ParserM Bool := do
  match (← currentToken) with
  | .constKeyword =>
    return ← lookAhead do
      nextToken
      return (← currentToken) == Kind.enumKeyword
  | .exportKeyword =>
    return ← lookAhead do
      nextToken
      if (← currentToken) == Kind.defaultKeyword then
        nextTokenCanFollowDefaultKeyword
      else if (← currentToken) == Kind.typeKeyword then
        nextTokenCanFollowExportModifier
      else
        canFollowExportModifier
  | .defaultKeyword =>
    nextTokenCanFollowDefaultKeyword
  | .staticKeyword =>
    return ← lookAhead do
      nextToken
      canFollowModifierToken
  | .getKeyword | .setKeyword =>
    return ← lookAhead do
      nextToken
      canFollowGetOrSetKeyword
  | _ =>
    nextTokenIsOnSameLineAndCanFollowModifier

partial def nextTokenIsIdentifierOrKeywordOnSameLine : ParserM Bool :=
  lookAhead do
    nextToken
    let tok ← currentToken
    return (tok == Kind.identifier || Kind.isKeywordKind tok) && !((← get).scanner.hasPrecedingLineBreak)

partial def nextTokenCanFollowClassMemberModifier : ParserM Bool := do
  match (← currentToken) with
  | .constKeyword =>
    nextTokenIsOnSameLineAndCanFollowModifier
  | .staticKeyword =>
    if ← lookAhead do
      nextToken
      return (← currentToken) == Kind.openBraceToken
    then
      return false
    nextTokenCanFollowModifier
  | _ =>
    nextTokenCanFollowModifier

partial def nextTokenIsOpenBrace : ParserM Bool :=
  lookAhead do
    nextToken
    return (← currentToken) == Kind.openBraceToken

partial def parseContextualModifier (kind : Kind) : ParserM Bool := do
  lookAhead do
    if (← currentToken) != kind then
      return false
    nextTokenCanFollowModifier

partial def isClassMemberStart : ParserM Bool := do
  lookAhead do
    let tok ← currentToken
    if tok == Kind.atToken then
      return true
    if tok == Kind.staticKeyword && (← nextTokenIsOpenBrace) then
      return true
    let rec skipModifiers (lastModifier : Option Kind) : ParserM (Option Kind × Bool) := do
      let tok ← currentToken
      if isModifierKind tok then
        if isClassMemberModifier tok then
          return (some tok, true)
        else
          nextToken
          skipModifiers (some tok)
      else
        return (lastModifier, false)
    let (idToken?, hasCertainMemberModifier) ← skipModifiers none
    if hasCertainMemberModifier then
      return true
    if (← currentToken) == Kind.asteriskToken then
      return true
    if (← currentToken) == Kind.privateIdentifier then
      return true
    let idToken? ←
      if ← isLiteralPropertyName then
        let tok ← currentToken
        nextToken
        pure (some tok)
      else
        pure idToken?
    if (← currentToken) == Kind.openBracketToken then
      return true
    match idToken? with
    | some idToken =>
      if !Kind.isKeywordKind idToken || idToken == Kind.setKeyword || idToken == Kind.getKeyword then
        return true
      let tok ← currentToken
      return tok == Kind.openParenToken || tok == Kind.lessThanToken || tok == Kind.exclamationToken ||
        tok == Kind.colonToken || tok == Kind.equalsToken || tok == Kind.questionToken || (← canParseSemicolon)
    | none =>
      return false

/-- Based on Go: parser.go:683 (parsingContextErrors) -/
partial def parsingContextErrors (kind : ParsingContext) : ParserM Unit := do
  let tok ← currentToken
  match kind with
  | .sourceElements =>
    if tok == Kind.defaultKeyword then
      parseErrorAtCurrentToken Diagnostics.X_0_expected #["export"]
    else
      parseErrorAtCurrentToken Diagnostics.declaration_or_statement_expected
  | .blockStatements =>
    parseErrorAtCurrentToken Diagnostics.declaration_or_statement_expected
  | .switchClauses =>
    parseErrorAtCurrentToken Diagnostics.case_or_default_expected
  | .switchClauseStatements =>
    parseErrorAtCurrentToken Diagnostics.statement_expected
  | .restProperties | .typeMembers =>
    parseErrorAtCurrentToken Diagnostics.property_or_signature_expected
  | .classMembers =>
    parseErrorAtCurrentToken Diagnostics.unexpected_token_constructor
  | .enumMembers =>
    parseErrorAtCurrentToken Diagnostics.enum_member_expected
  | .heritageClauseElement =>
    parseErrorAtCurrentToken Diagnostics.expression_expected
  | .variableDeclarations =>
    if Kind.isKeywordKind tok then
      parseErrorAtCurrentToken Diagnostics.variable_declaration_name_not_allowed #[tokenToString tok]
    else
      parseErrorAtCurrentToken Diagnostics.variable_declaration_expected
  | .objectBindingElements =>
    parseErrorAtCurrentToken Diagnostics.property_destructuring_pattern_expected
  | .arrayBindingElements =>
    parseErrorAtCurrentToken Diagnostics.array_element_destructuring_pattern_expected
  | .argumentExpressions =>
    parseErrorAtCurrentToken Diagnostics.argument_expression_expected
  | .objectLiteralMembers =>
    parseErrorAtCurrentToken Diagnostics.property_assignment_expected
  | .arrayLiteralMembers =>
    parseErrorAtCurrentToken Diagnostics.expression_or_comma_expected
  | .jsDocParameters =>
    parseErrorAtCurrentToken Diagnostics.parameter_declaration_expected
  | .parameters =>
    if Kind.isKeywordKind tok then
      parseErrorAtCurrentToken Diagnostics.parameter_name_not_allowed #[tokenToString tok]
    else
      parseErrorAtCurrentToken Diagnostics.parameter_declaration_expected
  | .typeParameters =>
    parseErrorAtCurrentToken Diagnostics.type_parameter_declaration_expected
  | .typeArguments =>
    parseErrorAtCurrentToken Diagnostics.type_argument_expected
  | .tupleElementTypes =>
    parseErrorAtCurrentToken Diagnostics.type_expected
  | .heritageClauses =>
    parseErrorAtCurrentToken Diagnostics.unexpected_token_lbrace_expected
  | .importOrExportSpecifiers =>
    if tok == Kind.fromKeyword then
      parseErrorAtCurrentToken Diagnostics.X_0_expected #["}"]
    else
      parseErrorAtCurrentToken Diagnostics.identifier_expected
  | .jsxAttributes | .jsxChildren | .jsDocComment =>
    parseErrorAtCurrentToken Diagnostics.identifier_expected
  | .importAttributes =>
    parseErrorAtCurrentToken Diagnostics.identifier_or_string_literal_expected

/-- Helper: check if current token starts an expression. -/
partial def isStartOfExpression : ParserM Bool := do
  let tok ← currentToken
  let identStart ← isIdentifierToken
  if identStart || tok == Kind.numericLiteral ||
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
    tok == Kind.noSubstitutionTemplateLiteral ||
    tok == Kind.privateIdentifier || tok == Kind.atToken then
    return true
  if tok == Kind.importKeyword then
    return ← lookAhead do
      nextToken
      let t ← currentToken
      return t == Kind.openParenToken || t == Kind.lessThanToken || t == Kind.dotToken
  return false

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

partial def nextTokenIsColonOrQuestionColon : ParserM Bool := do
  nextToken
  if (← currentToken) == Kind.colonToken then
    return true
  if (← currentToken) == Kind.questionToken then
    nextToken
    return (← currentToken) == Kind.colonToken
  return false

partial def scanStartOfNamedTupleElement : ParserM Bool := do
  if (← currentToken) == Kind.dotDotDotToken then
    nextToken
    if !(← isIdentifierToken) then
      return false
    nextTokenIsColonOrQuestionColon
  else if ← isIdentifierToken then
    nextTokenIsColonOrQuestionColon
  else
    return false

partial def isStartOfLeftHandSideExpression : ParserM Bool := do
  let tok ← currentToken
  let identStart ← isIdentifierToken
  return identStart || tok == Kind.superKeyword || tok == Kind.thisKeyword || tok == Kind.nullKeyword ||
    tok == Kind.trueKeyword || tok == Kind.falseKeyword || tok == Kind.numericLiteral ||
    tok == Kind.stringLiteral || tok == Kind.bigIntLiteral || tok == Kind.noSubstitutionTemplateLiteral ||
    tok == Kind.templateHead || tok == Kind.openParenToken || tok == Kind.openBracketToken ||
    tok == Kind.openBraceToken || tok == Kind.functionKeyword || tok == Kind.classKeyword ||
    tok == Kind.newKeyword || tok == Kind.slashToken || tok == Kind.slashEqualsToken ||
    tok == Kind.importKeyword || tok == Kind.privateIdentifier

/-- Based on Go: parser.go:706 (isListElement) -/
partial def isListElement (kind : ParsingContext) (inErrorRecovery : Bool) : ParserM Bool := do
  match kind with
  | .sourceElements | .blockStatements | .switchClauseStatements =>
    return !((← currentToken) == Kind.semicolonToken && inErrorRecovery) && (← isStartOfStatement)
  | .switchClauses =>
    let tok ← currentToken
    return tok == Kind.caseKeyword || tok == Kind.defaultKeyword
  | .typeMembers =>
    let tok ← currentToken
    return tok == Kind.openBracketToken || tok == Kind.openParenToken || tok == Kind.lessThanToken ||
      tok == Kind.getKeyword || tok == Kind.setKeyword || tok == Kind.readonlyKeyword ||
      tok == Kind.minusToken || tok == Kind.plusToken || tok == Kind.stringLiteral ||
      tok == Kind.numericLiteral || (← isLiteralPropertyName)
  | .classMembers =>
    let tok ← currentToken
    return (tok == Kind.semicolonToken && !inErrorRecovery) || (← isClassMemberStart)
  | .enumMembers =>
    let tok ← currentToken
    return tok == Kind.openBracketToken || (← isLiteralPropertyName)
  | .objectLiteralMembers =>
    let tok ← currentToken
    return tok == Kind.openBracketToken || tok == Kind.asteriskToken || tok == Kind.dotDotDotToken ||
      tok == Kind.dotToken || (← isLiteralPropertyName)
  | .restProperties =>
    isLiteralPropertyName
  | .objectBindingElements =>
    let tok ← currentToken
    return tok == Kind.openBracketToken || tok == Kind.dotDotDotToken || (← isLiteralPropertyName)
  | .importAttributes =>
    isImportAttributeName
  | .heritageClauseElement =>
    if (← currentToken) == Kind.openBraceToken then
      return true
    else if !inErrorRecovery then
      return (← isStartOfLeftHandSideExpression) && !(← isHeritageClause)
    else
      return (← isIdentifierToken) && !(← isHeritageClause)
  | .variableDeclarations =>
    isBindingIdentifierOrPrivateIdentifierOrPattern
  | .arrayBindingElements =>
    let tok ← currentToken
    return tok == Kind.commaToken || tok == Kind.dotDotDotToken || (← isBindingIdentifierOrPrivateIdentifierOrPattern)
  | .argumentExpressions =>
    let tok ← currentToken
    return tok == Kind.dotDotDotToken || (← isStartOfExpression)
  | .arrayLiteralMembers =>
    let tok ← currentToken
    if tok == Kind.commaToken || tok == Kind.dotToken then
      return true
    else
      return tok == Kind.dotDotDotToken || (← isStartOfExpression)
  | .parameters =>
    isStartOfParameterToken
  | .jsDocParameters =>
    isStartOfParameterToken
  | .typeParameters =>
    let tok ← currentToken
    return tok == Kind.inKeyword || tok == Kind.outKeyword || tok == Kind.constKeyword || (← isIdentifierToken)
  | .typeArguments | .tupleElementTypes =>
    return (← currentToken) == Kind.commaToken || (← isStartOfType)
  | .heritageClauses =>
    isHeritageClause
  | .importOrExportSpecifiers =>
    let tok ← currentToken
    if tok == Kind.fromKeyword then
      return !(← lookAhead do nextToken; return (← currentToken) == Kind.stringLiteral)
    else if tok == Kind.stringLiteral then
      return true
    else
      return tok == Kind.identifier || Kind.isKeywordKind tok
  | .jsxAttributes =>
    let tok ← currentToken
    return tok == Kind.openBraceToken || tok == Kind.identifier || Kind.isKeywordKind tok
  | .jsxChildren =>
    return true
  | .jsDocComment =>
    return true

@[inline] private def parsingContextBit (kind : ParsingContext) : UInt32 :=
  ((1 : UInt32) <<< kind.toNat.toUInt32)

@[inline] private def hasParsingContext (contexts : UInt32) (kind : ParsingContext) : Bool :=
  (contexts &&& parsingContextBit kind) != 0

/-- Based on Go: parser.go:623 (isInSomeParsingContext) -/
partial def isInSomeParsingContext : ParserM Bool := do
  let contexts := (← get).parsingContexts
  let activeKinds := [
    ParsingContext.sourceElements,
    ParsingContext.blockStatements,
    ParsingContext.switchClauses,
    ParsingContext.switchClauseStatements,
    ParsingContext.typeMembers,
    ParsingContext.classMembers,
    ParsingContext.enumMembers,
    ParsingContext.heritageClauseElement,
    ParsingContext.variableDeclarations,
    ParsingContext.objectBindingElements,
    ParsingContext.arrayBindingElements,
    ParsingContext.argumentExpressions,
    ParsingContext.objectLiteralMembers,
    ParsingContext.jsxAttributes,
    ParsingContext.jsxChildren,
    ParsingContext.arrayLiteralMembers,
    ParsingContext.parameters,
    ParsingContext.jsDocParameters,
    ParsingContext.restProperties,
    ParsingContext.typeParameters,
    ParsingContext.typeArguments,
    ParsingContext.tupleElementTypes,
    ParsingContext.heritageClauses,
    ParsingContext.importOrExportSpecifiers,
    ParsingContext.importAttributes,
    ParsingContext.jsDocComment
  ]
  let rec loop (remaining : List ParsingContext) : ParserM Bool := do
    match remaining with
    | [] => return false
    | kind :: rest =>
      if hasParsingContext contexts kind then
        if (← isListElement kind true) || (← isListTerminator kind) then
          return true
        else
          loop rest
      else
        loop rest
  loop activeKinds

/-- Based on Go: parser.go:613 (abortParsingListOrMoveToNextToken) -/
partial def abortParsingListOrMoveToNextToken (kind : ParsingContext) : ParserM Bool := do
  if (← currentToken) == Kind.unknown then
    nextToken
    return false
  parsingContextErrors kind
  if ← isInSomeParsingContext then return true
  else nextToken; return false

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
    if (← currentToken) != Kind.openBracketToken then
      return false
    nextToken
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

partial def nextIsStartOfTypeOfImportType : ParserM Bool := do
  nextToken
  return (← currentToken) == Kind.importKeyword

partial def parseImportType : ParserM Node := do
  let pos ← nodePos
  let isTypeOf ← parseOptional Kind.typeOfKeyword
  let _ ← parseExpected Kind.importKeyword
  let _ ← parseExpected Kind.openParenToken
  let argType ← parseType'
  let attributes ←
    if (← parseOptional Kind.commaToken) then do
      let attrPos ← nodePos
      let _ ← parseExpected Kind.openBraceToken
      let token ← currentToken
      if token == Kind.withKeyword || token == Kind.assertKeyword then
        nextToken
      else
        parseErrorAtCurrentToken Diagnostics.X_0_expected #[tokenToString Kind.withKeyword]
      let _ ← parseExpected Kind.colonToken
      let isAttr : ParserM Bool := isListElement .importAttributes false
      let attrs ← parseDelimitedList .importAttributes isAttr parseImportAttribute
      let _ ← parseOptional Kind.commaToken
      let _ ← parseExpected Kind.closeBraceToken
      pure (some (← finishNode (Node.importAttributes {} token attrs) attrPos))
    else pure none
  let _ ← parseExpected Kind.closeParenToken
  let qualifier ←
    if (← parseOptional Kind.dotToken) then do
      let qPos ← nodePos
      let first ← parseIdentifierName
      pure (some (← parseQualifiedNameRest first qPos))
    else pure none
  let typeArgs ← match (← currentToken) with
    | .lessThanToken => do
      let _ ← parseExpected Kind.lessThanToken
      let args ← parseDelimitedList .typeArguments isStartOfType parseType'
      let _ ← parseExpected Kind.greaterThanToken
      pure (some args)
    | _ => pure none
  finishNode (Node.importType {} isTypeOf argType attributes qualifier typeArgs) pos

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
      if ← parseOptional Kind.commaToken then
        parseDelimitedListLoop kind isElement parseElement acc'
      else if ← isListTerminator kind then return acc'
      else if (← currentToken) == Kind.unknown then
        nextToken
        parseDelimitedListLoop kind isElement parseElement acc'
      else
        let _ ← parseExpected Kind.commaToken
        if (kind == .objectLiteralMembers || kind == .importAttributes) &&
            (← currentToken) == Kind.semicolonToken &&
            !((← get).scanner.hasPrecedingLineBreak) then
          nextToken
        if startPos == (← get).scanner.tokenFullStart then
          nextToken
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

/-- Parse spread element, omitted expression, or assignment expression
    (for array/argument lists).
    Go: parser.go:5359 (parseArgumentOrArrayLiteralElement) -/
partial def parseSpreadOrAssignmentExpression : ParserM Node :=
  do
    match (← currentToken) with
    | .dotDotDotToken =>
      let pos ← nodePos
      nextToken
      let expr ← parseAssignmentExpressionOrHigher
      finishNode (Node.spreadElement {} expr) pos
    | .commaToken =>
      -- Array hole / elision: the comma will be consumed by parseDelimitedList
      let pos ← nodePos
      finishNode (Node.omittedExpression {}) pos
    | _ => parseAssignmentExpressionOrHigher

/-- Based on Go: parser.go:5479 (parseObjectLiteralExpression) -/
partial def parseObjectLiteralExpression : ParserM Node :=
  do
    let pos ← nodePos
    let _ ← parseExpected Kind.openBraceToken
    let isElem : ParserM Bool := isListElement .objectLiteralMembers false
    let properties ← parseDelimitedList .objectLiteralMembers isElem
      (parseObjectLiteralElement)
    let _ ← parseExpected Kind.closeBraceToken
    finishNode (Node.objectLiteralExpression {} properties) pos

/-- Helper: after parsing a property name, dispatch on the next token to decide
    whether this is a method shorthand, property assignment, or shorthand property. -/
partial def parsePropertyBody (name : Node) (pos : Nat) (tokenIsIdentifier : Bool) : ParserM Node := do
  if (← currentToken) == .questionToken then
    parseErrorAtCurrentToken Diagnostics.object_member_cannot_be_declared_optional
    nextToken
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
    if tokenIsIdentifier then
      -- Shorthand property: name  (or name = default)
      finishNode (Node.shorthandPropertyAssignment {} name) pos
    else
      let _ ← parseExpected Kind.colonToken
      let value ← parseAssignmentExpressionOrHigher
      finishNode (Node.propertyAssignment {} name (some value)) pos

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
      let tok ← currentToken
      let isAccessor ← parseContextualModifier tok
      if isAccessor then
        nextToken
        let name ← parsePropertyName
        let questionToken ←
          if (← currentToken) == .questionToken then do
            parseErrorAtCurrentToken Diagnostics.object_member_cannot_be_declared_optional
            parseOptionalToken Kind.questionToken
          else
            pure (none : Option Node)
        let typeParams ← parseTypeParameters
        let params ← parseParameters
        let returnType ← parseReturnType
        let body ← parseFunctionBlock
        finishNode (Node.methodDeclaration {} name questionToken typeParams params returnType body) pos
      else
        let tokenIsIdentifier ← isIdentifierToken
        let name ← parsePropertyName
        parsePropertyBody name pos tokenIsIdentifier
    | _ =>
      let tokenIsIdentifier ← isIdentifierToken
      let name ← parsePropertyName
      parsePropertyBody name pos tokenIsIdentifier

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
    -- Go: parser.go:5553 — asteriskToken for generator expressions
    let _ ← parseOptional Kind.asteriskToken
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
    | .asyncKeyword =>
      -- Based on Go: parser.go:5430-5437 — async function expression
      let isAsyncFunc ← lookAhead do
        nextToken
        return (← currentToken) == Kind.functionKeyword && !(← get).scanner.hasPrecedingLineBreak
      if isAsyncFunc then
        parseFunctionExpression
      else
        parseIdentifier
    | .functionKeyword =>
      parseFunctionExpression
    | .newKeyword =>
      parseNewExpression
    | .importKeyword =>
      -- Based on Go: parser.go:5909 / isStartOfExpression
      -- import(expr) dynamic import or import.meta
      let isImportExpr ← lookAhead do
        nextToken
        let tok ← currentToken
        return tok == Kind.openParenToken || tok == Kind.dotToken || tok == Kind.lessThanToken
      if isImportExpr then
        let pos ← nodePos
        nextToken  -- consume 'import'
        match (← currentToken) with
        | .openParenToken =>
          -- Dynamic import: import(expr)
          let _ ← parseExpected Kind.openParenToken
          let arg ← parseAssignmentExpressionOrHigher
          let _ ← parseExpected Kind.closeParenToken
          finishNode (Node.callExpression {} (Node.token {} Kind.importKeyword) #[arg]) pos
        | .dotToken =>
          -- import.meta
          nextToken  -- consume '.'
          let name ← parseIdentifierName
          finishNode (Node.propertyAccessExpression {} (Node.token {} Kind.importKeyword) name) pos
        | _ => parseIdentifier
      else
        parseIdentifier
    | .classKeyword =>
      -- Class expression
      parseClassDeclaration
    | .lessThanToken
    | .lessThanSlashToken =>
      -- JSX only — non-JSX <Type>expr is handled in parseUnaryExpressionOrHigher
      if (← get).scanner.languageVariant == LanguageVariant.jsx then
        parseJsxLikeExpression
      else
        parseIdentifier
    | .slashToken
    | .slashEqualsToken =>
      -- Based on Go: parser.go:5446-5449 — regex literal
      let tok ← reScanSlashToken
      if tok == Kind.regularExpressionLiteral then
        parseLiteralExpression
      else
        parseIdentifier
    | _ =>
      -- Go: parser.go:5455 — uses Expression_expected (TS1109), not Identifier_expected (TS1003)
      let isIdent ← isIdentifierToken
      if isIdent then
        let pos ← nodePos
        let text ← internIdentifier (← get).scanner.tokenValue
        nextToken
        finishNode (Node.identifier {} text) pos
      else
        let pos ← nodePos
        parseErrorAtCurrentToken Diagnostics.expression_expected
        finishNode (Node.missing {} Kind.identifier) pos

/-- Based on Go: parser.go:5458 (parseParenthesizedExpression) -/
partial def parseParenthesizedExpression : ParserM Node :=
  do
    let pos ← nodePos
    let _ ← parseExpected Kind.openParenToken
    let expr ← parseExpressionAllowIn
    let _ ← parseExpected Kind.closeParenToken
    finishNode (Node.parenthesizedExpression {} expr) pos

/-- Based on Go: parser.go:5388 (parseTemplateExpression) -/
partial def parseTemplateExpression : ParserM Node :=
  do
    let pos ← nodePos
    -- Parse the template head (current token should be templateHead)
    let head ← parseLiteralExpression
    -- Parse template spans: expression + (templateMiddle | templateTail)
    let rec parseSpans (spans : Array Node) : ParserM (Array Node) := do
      let spanPos ← nodePos
      let expr ← parseExpressionAllowIn
      -- Expect } then rescan to get templateMiddle or templateTail.
      let (literal, literalKind) ← if (← currentToken) == Kind.closeBraceToken then do
        let literalKind ← reScanTemplateToken false
        let literal ← parseLiteralExpression
        pure (literal, literalKind)
      else do
        parseErrorAtCurrentToken Diagnostics.X_0_expected #[tokenToString Kind.closeBraceToken]
        let literal ← finishNode (Node.token {} Kind.templateTail) (← nodePos)
        pure (literal, Kind.templateTail)
      let span ← finishNode (Node.templateSpan {} expr literal) spanPos
      let spans := spans.push span
      if literalKind == Kind.templateMiddle then
        parseSpans spans
      else
        return spans
    let spans ← parseSpans #[]
    finishNode (Node.templateExpression {} head spans) pos

partial def isTemplateStartOfTaggedTemplate : ParserM Bool := do
  let tok ← currentToken
  return tok == Kind.noSubstitutionTemplateLiteral || tok == Kind.templateHead

partial def parseSuperExpression : ParserM Node := do
  let expr ← parseTokenNode
  let canParseTypeArgs ← lookAhead do
    match (← currentToken) with
    | .lessThanToken | .lessThanLessThanToken => pure true
    | _ => pure false
  if canParseTypeArgs then
    match (← currentToken) with
    | .lessThanLessThanToken => let _ ← reScanLessThanToken
    | _ => pure ()
    if (← currentToken) == Kind.lessThanToken then
      let _ ← parseExpected Kind.lessThanToken
      let _ ← parseDelimitedList .typeArguments isStartOfType parseType'
      match (← currentToken) with
      | .greaterThanToken => pure ()
      | _ => let _ ← reScanGreaterThanToken
      let _ ← parseExpected Kind.greaterThanToken
  match (← currentToken) with
  | .openParenToken | .dotToken | .openBracketToken => pure ()
  | _ => parseErrorAtCurrentToken Diagnostics.super_must_be_followed_by_an_argument_list_or_member_access
  return expr

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
partial def tryParseTypeArgumentsInExpression : ParserM (Option (Array Node)) := do
  let isTypeArgs ← lookAhead do
    match (← currentToken) with
    | .lessThanLessThanToken =>
      let tok ← reScanLessThanToken
      if tok != Kind.lessThanToken then
        return false
    | _ => pure ()
    if (← currentToken) != Kind.lessThanToken then
      return false
    let _ ← parseExpected Kind.lessThanToken
    let _ ← parseDelimitedList .typeArguments isStartOfType parseType'
    match (← currentToken) with
    | .greaterThanToken =>
      return true
    | _ =>
      let tok ← reScanGreaterThanToken
      return tok == Kind.greaterThanToken
  if !isTypeArgs then
    return none
  match (← currentToken) with
  | .lessThanLessThanToken =>
    let _ ← reScanLessThanToken
  | _ => pure ()
  let _ ← parseExpected Kind.lessThanToken
  let typeArgs ← parseDelimitedList .typeArguments isStartOfType parseType'
  match (← currentToken) with
  | .greaterThanToken => pure ()
  | _ => let _ ← reScanGreaterThanToken
  let _ ← parseExpected Kind.greaterThanToken
  return some typeArgs

partial def parseMemberExpressionRest (pos : Nat) (current : Node) : ParserM Node := do
      let tok ← currentToken
      match tok with
      | .dotToken =>
        nextToken
        let name ← if (← currentToken) == Kind.privateIdentifier then parsePropertyName else parseIdentifierName
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
          let name ← if (← currentToken) == Kind.privateIdentifier then parsePropertyName else parseIdentifierName
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
      | .lessThanToken | .lessThanLessThanToken =>
        match (← tryParseTypeArgumentsInExpression) with
        | some typeArgs =>
          let node ← finishNode (Node.expressionWithTypeArguments {} current (some typeArgs)) pos
          parseMemberExpressionRest pos node
        | none =>
          return current
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
        -- Generic call/tagged template: expr<T>(args) or expr<T>`...`
        let isTypeArgCall ← lookAhead do
          match (← currentToken) with
          | .lessThanLessThanToken => let _ ← reScanLessThanToken
          | _ => pure ()
          match (← currentToken) with
          | .lessThanToken => pure ()
          | _ => return false
          let _ ← parseExpected Kind.lessThanToken
          let _ ← parseDelimitedList .typeArguments isStartOfType (parseType')
          match (← currentToken) with
          | .greaterThanToken => pure ()
          | _ =>
            let tok ← reScanGreaterThanToken
            if tok != Kind.greaterThanToken then
              return false
          let _ ← parseExpected Kind.greaterThanToken
          let tok ← currentToken
          return tok == Kind.openParenToken || tok == Kind.noSubstitutionTemplateLiteral || tok == Kind.templateHead
        if isTypeArgCall then
          match (← currentToken) with
          | .lessThanLessThanToken => let _ ← reScanLessThanToken
          | _ => pure ()
          let _ ← parseExpected Kind.lessThanToken
          let typeArgs ← parseDelimitedList .typeArguments isStartOfType (parseType')
          match (← currentToken) with
          | .greaterThanToken => pure ()
          | _ => let _ ← reScanGreaterThanToken
          let _ ← parseExpected Kind.greaterThanToken
          match (← currentToken) with
          | .openParenToken =>
            let _ ← parseExpected Kind.openParenToken
            let args ← parseDelimitedList .argumentExpressions isStartOfExpression
              (parseSpreadOrAssignmentExpression)
            let _ ← parseExpected Kind.closeParenToken
            let node ← finishNode (Node.callExpression {} current args) pos
            parseCallExpressionRest pos node
          | .noSubstitutionTemplateLiteral | .templateHead =>
            let tagPos := current.base.loc.pos.toInt.toNat
            let tag ← finishNode (Node.expressionWithTypeArguments {} current (some typeArgs)) tagPos
            let tmpl ← match (← currentToken) with
              | .noSubstitutionTemplateLiteral =>
                let _ ← reScanTemplateToken true
                parseLiteralExpression
              | _ => parseTemplateExpression
            let node ← finishNode (Node.taggedTemplateExpression {} tag tmpl) pos
            parseCallExpressionRest pos node
          | _ => return current
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
    let expr ← if (← currentToken) == Kind.superKeyword then parseSuperExpression else parseMemberExpressionOrHigher
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
      -- Based on Go: parser.go:4975 (isAwaitExpression)
      -- Only parse as await if next token looks like operand on same line
      let isAwait ← lookAhead do
        nextToken
        let tok ← currentToken
        let onSameLine := !(← get).scanner.hasPrecedingLineBreak
        return onSameLine && (tok == Kind.identifier || Kind.isKeywordKind tok ||
          tok == Kind.numericLiteral || tok == Kind.stringLiteral ||
          tok == Kind.noSubstitutionTemplateLiteral || tok == Kind.templateHead ||
          tok == Kind.openBraceToken || tok == Kind.openBracketToken ||
          tok == Kind.openParenToken || tok == Kind.lessThanToken ||
          tok == Kind.plusToken || tok == Kind.minusToken ||
          tok == Kind.tildeToken || tok == Kind.exclamationToken ||
          tok == Kind.deleteKeyword || tok == Kind.typeOfKeyword ||
          tok == Kind.voidKeyword || tok == Kind.awaitKeyword ||
          tok == Kind.functionKeyword || tok == Kind.classKeyword ||
          tok == Kind.newKeyword || tok == Kind.slashToken ||
          tok == Kind.slashEqualsToken)
      if isAwait then
        let pos ← nodePos
        nextToken
        let operand ← parseUnaryExpressionOrHigher
        finishNode (Node.awaitExpression {} operand) pos
      else
        -- Treat 'await' as an identifier
        let pos ← nodePos
        let expr ← parseLeftHandSideExpressionOrHigher
        if !(← get).scanner.hasPrecedingLineBreak then
          let tok ← currentToken
          match tok with
          | .plusPlusToken | .minusMinusToken =>
            nextToken
            finishNode (Node.postfixUnaryExpression {} expr tok) pos
          | _ => return expr
        else return expr
    | .lessThanToken =>
      -- Based on Go: parser.go:4930-4939 (parseSimpleUnaryExpression)
      -- In non-JSX mode, <Type>expr is a type assertion
      if (← get).scanner.languageVariant != LanguageVariant.jsx then
        let pos ← nodePos
        let _ ← parseExpected Kind.lessThanToken
        let typeNode ← parseType'
        let _ ← parseExpected Kind.greaterThanToken
        let expr ← parseUnaryExpressionOrHigher
        finishNode (Node.typeAssertionExpression {} typeNode expr) pos
      else
        let pos ← nodePos
        let expr ← parseLeftHandSideExpressionOrHigher
        if !(← get).scanner.hasPrecedingLineBreak then
          let tok ← currentToken
          match tok with
          | .plusPlusToken
          | .minusMinusToken =>
            nextToken
            finishNode (Node.postfixUnaryExpression {} expr tok) pos
          | _ => return expr
        else return expr
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
            | .openBraceToken => return true
            | .colonToken =>
              let _ ← parseReturnType
              let tok ← currentToken
              return tok == Kind.equalsGreaterThanToken || tok == Kind.openBraceToken
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
  | .lessThanToken =>
    -- Go: parser.go:4162 — <T>(...) => {} could be an arrow function with type params
    -- In non-JSX mode, speculatively try to parse type params then check for arrow pattern
    if (← get).scanner.languageVariant != LanguageVariant.jsx then
      lookAhead do
        -- Try to skip past type parameters <T, U extends V, ...>
        let _ ← parseTypeParameters
        if (← currentToken) == Kind.openParenToken then
          -- Now scan for the closing ) and =>
          let rec scanToArrowGeneric (parenDepth bracketDepth braceDepth : Nat) : ParserM Bool := do
            match (← currentToken) with
            | .endOfFile => return false
            | .openParenToken =>
              nextToken
              scanToArrowGeneric (parenDepth + 1) bracketDepth braceDepth
            | .closeParenToken =>
              if parenDepth == 1 && bracketDepth == 0 && braceDepth == 0 then
                nextToken
                match (← currentToken) with
                | .equalsGreaterThanToken => return true
                | .openBraceToken => return true
                | .colonToken =>
                  let _ ← parseReturnType
                  let tok ← currentToken
                  return tok == Kind.equalsGreaterThanToken || tok == Kind.openBraceToken
                | _ => return false
              else
                nextToken
                scanToArrowGeneric (parenDepth - 1) bracketDepth braceDepth
            | .openBracketToken =>
              nextToken
              scanToArrowGeneric parenDepth (bracketDepth + 1) braceDepth
            | .closeBracketToken =>
              if bracketDepth == 0 then return false
              nextToken
              scanToArrowGeneric parenDepth (bracketDepth - 1) braceDepth
            | .openBraceToken =>
              nextToken
              scanToArrowGeneric parenDepth bracketDepth (braceDepth + 1)
            | .closeBraceToken =>
              if braceDepth == 0 then return false
              nextToken
              scanToArrowGeneric parenDepth bracketDepth (braceDepth - 1)
            | _ =>
              nextToken
              scanToArrowGeneric parenDepth bracketDepth braceDepth
          scanToArrowGeneric 0 0 0
        else return false
    else return false
  | _ =>
    if ← isBindingIdentifierToken then
      lookAhead do
        nextToken
        return (← currentToken) == Kind.equalsGreaterThanToken
    else return false

partial def isStartOfExpressionStatement : ParserM Bool := do
  let tok ← currentToken
  return tok != Kind.openBraceToken && tok != Kind.functionKeyword && tok != Kind.classKeyword &&
    tok != Kind.atToken && (← isStartOfExpression)

partial def parseArrowFunctionExpressionBody : ParserM Node := do
  match (← currentToken) with
  | .openBraceToken =>
    parseBlock
  | .semicolonToken | .functionKeyword | .classKeyword =>
    parseAssignmentExpressionOrHigher
  | _ =>
    if (← isStartOfStatement) && !(← isStartOfExpressionStatement) then
      parseBlock
    else
      parseAssignmentExpressionOrHigher

/-- Parse arrow function expression. -/
partial def parseArrowFunction : ParserM Node :=
  do
    let pos ← nodePos
    match (← currentToken) with
    | .openParenToken | .lessThanToken =>
      -- Handles both (x) => {} and <T>(x: T) => {}
      let typeParams ← parseTypeParameters
      let params ← parseParameters
      let returnType ← parseReturnType
      let _ ← parseExpected Kind.equalsGreaterThanToken
      let body ← parseArrowFunctionExpressionBody
      finishNode (Node.arrowFunction {} typeParams params returnType body) pos
    | _ =>
      -- Single parameter arrow: x => expr
      let param ← parseBindingIdentifier
      let paramNode ← finishNode (Node.parameterDeclaration {} none param none none none) pos
      let _ ← parseExpected Kind.equalsGreaterThanToken
      let body ← parseArrowFunctionExpressionBody
      finishNode (Node.arrowFunction {} none #[paramNode] none body) pos

/-- Based on Go: parser.go:3952 (parseAssignmentExpressionOrHigher) -/
partial def parseAssignmentExpressionOrHigher : ParserM Node :=
  do
    let tok0 ← currentToken
    if ((tok0 == Kind.lessThanToken) || (tok0 == Kind.lessThanSlashToken)) &&
       (← get).scanner.languageVariant == LanguageVariant.jsx then
      return ← parseJsxLikeExpression
    -- Check for arrow function (includes async arrows)
    -- Go: parser.go:3982 — tryParseParenthesizedArrowFunctionExpression handles async (...)  => {}
    -- Go: parser.go:3986 — tryParseAsyncSimpleArrowFunctionExpression handles async x => expr
    if (← currentToken) == Kind.asyncKeyword then
      let isAsyncArrow ← lookAhead do
        nextToken  -- skip 'async'
        if (← get).scanner.hasPrecedingLineBreak then return false
        -- async => is just `async` as identifier followed by =>
        if (← currentToken) == Kind.equalsGreaterThanToken then return false
        isArrowFunctionStart
      if isAsyncArrow then
        nextToken  -- consume 'async'
        return ← parseArrowFunction
    if ← isArrowFunctionStart then
      return ← parseArrowFunction
    -- Check for yield — Based on Go: parser.go:4025 (isYieldExpression)
    -- Only parse as yield expression if next token looks like yield operand on same line
    match (← currentToken) with
    | .yieldKeyword =>
      let isYield ← lookAhead do
        nextToken
        let tok ← currentToken
        let onSameLine := !(← get).scanner.hasPrecedingLineBreak
        return onSameLine && (tok == Kind.identifier || Kind.isKeywordKind tok ||
          tok == Kind.numericLiteral || tok == Kind.stringLiteral ||
          tok == Kind.noSubstitutionTemplateLiteral || tok == Kind.templateHead ||
          tok == Kind.openBraceToken || tok == Kind.openBracketToken ||
          tok == Kind.asteriskToken)
      if isYield then
        let pos ← nodePos
        nextToken
        -- Check for yield* (asterisk)
        let _ ← parseOptional Kind.asteriskToken
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

partial def parseTypeOrTypePredicate : ParserM Node := do
  match (← currentToken) with
  | .assertsKeyword =>
    let isAssertsPredicate ← lookAhead do
      nextToken
      let tok ← currentToken
      return tok == Kind.identifier || tok == Kind.thisKeyword
    if isAssertsPredicate then
      let pos ← nodePos
      nextToken
      let paramName ← if (← currentToken) == Kind.thisKeyword then parseTokenNode else parseIdentifier
      let typeNode ← if (← parseOptional Kind.isKeyword) then
        pure (some (← parseType'))
      else pure none
      finishNode (Node.typePredicate {} paramName typeNode) pos
    else
      parseType'
  | .identifier =>
    let isTypePred ← lookAhead do
      nextToken
      return (← currentToken) == Kind.isKeyword
    if isTypePred then
      let pos ← nodePos
      let paramName ← parseIdentifier
      nextToken
      let typeNode ← parseType'
      finishNode (Node.typePredicate {} paramName (some typeNode)) pos
    else
      parseType'
  | .thisKeyword =>
    let isTypePred ← lookAhead do
      nextToken
      return (← currentToken) == Kind.isKeyword
    if isTypePred then
      let pos ← nodePos
      let paramName ← parseTokenNode
      nextToken
      let typeNode ← parseType'
      finishNode (Node.typePredicate {} paramName (some typeNode)) pos
    else
      parseType'
  | _ => parseType'

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
      let retType ← parseTypeOrTypePredicate
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
        let retType ← parseTypeOrTypePredicate
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
      let typeParams ← parseTypeParameters
      let params ← parseParameters
      let _ ← parseExpected Kind.equalsGreaterThanToken
      let retType ← parseTypeOrTypePredicate
      finishNode (Node.constructorType {} typeParams params (some retType)) pos
    -- keyof, unique, readonly, infer — handled by parseTypeOperatorOrHigher
    | .keyOfKeyword | .uniqueKeyword | .readonlyKeyword | .inferKeyword =>
      let typeNode ← parseTypeOperatorOrHigher
      let typeNode ← parseUnionOrIntersectionPostfix typeNode
      -- fall through to conditional type check below
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
    | _ =>
      -- Union/intersection prefix: | Type, & Type
      let hasLeadingBar := tok == Kind.barToken
      let hasLeadingAmp := tok == Kind.ampersandToken
      if hasLeadingBar || hasLeadingAmp then nextToken
      let primaryType ←
        if (hasLeadingBar || hasLeadingAmp) && (← isStartOfFunctionOrConstructorType) then
          parseType'
        else
          parseTypeOperatorOrHigher
      let typeNode ←
        if hasLeadingAmp then
          parseIntersectionPostfix primaryType
        else
          parseUnionOrIntersectionPostfix primaryType
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

/-- Based on Go: parser.go:2597 (parseTypeOperatorOrHigher)
    Parses type operators (keyof, unique, readonly, infer) + primary type + array postfix.
    Does NOT parse union/intersection/conditional — just the operand level. -/
partial def parseTypeOperatorOrHigher : ParserM Node := do
  match (← currentToken) with
  | .keyOfKeyword | .uniqueKeyword | .readonlyKeyword =>
    let pos ← nodePos
    let op ← currentToken
    nextToken
    let inner ← parseTypeOperatorOrHigher
    finishNode (Node.typeOperator {} op inner) pos
  | .inferKeyword =>
    -- Based on Go: parser.go:2566 (parseInferType)
    let pos ← nodePos
    nextToken
    let tpPos ← nodePos
    let name ← parseIdentifier
    -- Check for `infer T extends U` constraint (fix #13)
    let constraint ← if (← currentToken) == Kind.extendsKeyword &&
        !(← get).scanner.hasPrecedingLineBreak then do
      nextToken
      -- Parse constraint at restricted level (no conditional types)
      let ct ← parseTypeOperatorOrHigher
      pure (some ct)
    else pure none
    -- infer T creates a typeParameter node wrapping the name
    let _ := constraint  -- constraint not stored yet (would need TypeParameterDeclaration node)
    let tp ← finishNode (Node.typeReference {} name none) tpPos
    finishNode (Node.inferType {} tp) pos
  | _ =>
    let primary ← parsePrimaryType
    parseArrayTypePostfix primary

/-- Based on Go: parser.go:3009 (parseMappedType) -/
partial def parseMappedType : ParserM Node := do
  let pos ← nodePos
  let _ ← parseExpected Kind.openBraceToken
  -- Optional readonly modifier: readonly | +readonly | -readonly
  if (← currentToken) == Kind.readonlyKeyword || (← currentToken) == Kind.plusToken ||
     (← currentToken) == Kind.minusToken then
    nextToken  -- skip readonly/+/-
    if (← currentToken) == Kind.readonlyKeyword then nextToken
  -- [K in T]
  let _ ← parseExpected Kind.openBracketToken
  let tpPos ← nodePos
  let name ← parseIdentifierName
  let _ ← parseExpected Kind.inKeyword
  let constraint ← parseType'
  let typeParam ← finishNode (Node.typeReference {} name (some #[constraint])) tpPos
  -- Optional `as NameType`
  let nameType ← if (← parseOptional Kind.asKeyword) then
    pure (some (← parseType'))
  else pure none
  let _ ← parseExpected Kind.closeBracketToken
  -- Optional ? modifier: ? | +? | -?
  if (← currentToken) == Kind.questionToken || (← currentToken) == Kind.plusToken ||
     (← currentToken) == Kind.minusToken then
    nextToken
    if (← currentToken) == Kind.questionToken then nextToken
  let typeNode ← parseTypeAnnotation
  let _ ← tryParseSemicolon
  let _ ← parseExpected Kind.closeBraceToken
  finishNode (Node.mappedType {} typeParam nameType typeNode) pos

/-- Parse a primary (non-union, non-intersection) type. -/
partial def parsePrimaryType : ParserM Node :=
  do
    let tok ← currentToken
    let baseType ←
      match tok with
      -- Type literal or mapped type: { members } or { [K in T]: V }
      | .openBraceToken =>
        -- Based on Go: parser.go:2676-2680 — check for mapped type
        let isMapped ← lookAhead do
          nextToken  -- skip {
          -- Optional +/- readonly
          if (← currentToken) == Kind.plusToken || (← currentToken) == Kind.minusToken then
            nextToken
            return (← currentToken) == Kind.readonlyKeyword
          if (← currentToken) == Kind.readonlyKeyword then
            nextToken
          -- [identifier in ...]
          if (← currentToken) != Kind.openBracketToken then return false
          nextToken
          if !(← isIdentifierToken) then return false
          nextToken
          return (← currentToken) == Kind.inKeyword
        if isMapped then
          parseMappedType
        else
          let pos ← nodePos
          let _ ← parseExpected Kind.openBraceToken
          let members ← parseList .typeMembers (isTypeMemberStart) (parseTypeMember)
          let _ ← parseExpected Kind.closeBraceToken
          finishNode (Node.typeLiteral {} members) pos
      -- Tuple type: [Type, Type]
      | .openBracketToken =>
        let pos ← nodePos
        let _ ← parseExpected Kind.openBracketToken
        let parseTupleElementType : ParserM Node := do
          let elemPos ← nodePos
          if (← currentToken) == Kind.dotDotDotToken then
            nextToken
            let typeNode ← parseType'
            finishNode (Node.restType {} typeNode) elemPos
          else
            let typeNode ← parseType'
            if (← currentToken) == Kind.questionToken then
              nextToken
              finishNode (Node.optionalType {} typeNode) elemPos
            else
              pure typeNode
        let parseTupleElementNameOrTupleElementType : ParserM Node := do
          if ← lookAhead scanStartOfNamedTupleElement then
            let elemPos ← nodePos
            let dotDotDotToken ← parseOptionalToken Kind.dotDotDotToken
            let name ← parseIdentifierName
            let questionToken ← parseOptionalToken Kind.questionToken
            let _ ← parseExpected Kind.colonToken
            let typeNode ← parseTupleElementType
            finishNode (Node.namedTupleMember {} dotDotDotToken name questionToken typeNode) elemPos
          else
            parseTupleElementType
        let elements ←
          parseDelimitedList .tupleElementTypes isStartOfType parseTupleElementNameOrTupleElementType
        let _ ← parseExpected Kind.closeBracketToken
        finishNode (Node.tupleType {} elements) pos
      | .openParenToken =>
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
          let retType ← parseTypeOrTypePredicate
          return ← finishNode (Node.functionType {} none params (some retType)) pos
        else
          let pos ← nodePos
          let _ ← parseExpected Kind.openParenToken
          let inner ← parseType'
          let _ ← parseExpected Kind.closeParenToken
          finishNode (Node.parenthesizedType {} inner) pos
      -- typeof type: typeof expr
      | .typeOfKeyword =>
        let isImportType ← lookAhead nextIsStartOfTypeOfImportType
        if isImportType then
          parseImportType
        else
          let pos ← nodePos
          nextToken
          let name ← parseIdentifierName
          let qname ← parseQualifiedNameRest name pos
          if !((← get).scanner.hasPrecedingLineBreak) && (← currentToken) == Kind.lessThanToken then
            let _ ← parseExpected Kind.lessThanToken
            let _ ← parseDelimitedList .typeArguments isStartOfType parseType'
            let _ ← parseExpected Kind.greaterThanToken
          finishNode (Node.typeQuery {} qname) pos
      | .voidKeyword | .undefinedKeyword | .nullKeyword => parseTokenNode
      -- Template literal type: `hello${string}world`
      | .noSubstitutionTemplateLiteral =>
        let pos ← nodePos
        let lit ← parseLiteralExpression
        finishNode (Node.literalType {} lit) pos
      | .templateHead =>
        -- Based on Go: parser.go:3560 (parseTemplateType)
        -- Parse as template expression (reuse expr template nodes for type template)
        let pos ← nodePos
        let head ← parseLiteralExpression
        let rec parseTypeSpans (spans : Array Node) : ParserM (Array Node) := do
          let spanPos ← nodePos
          let typeNode ← parseType'
          let (literal, literalKind) ← if (← currentToken) == Kind.closeBraceToken then do
            let literalKind ← reScanTemplateToken false
            let literal ← parseLiteralExpression
            pure (literal, literalKind)
          else do
            parseErrorAtCurrentToken Diagnostics.X_0_expected #[tokenToString Kind.closeBraceToken]
            let literal ← finishNode (Node.token {} Kind.templateTail) (← nodePos)
            pure (literal, Kind.templateTail)
          let span ← finishNode (Node.templateSpan {} typeNode literal) spanPos
          let spans := spans.push span
          if literalKind == Kind.templateMiddle then
            parseTypeSpans spans
          else
            return spans
        let spans ← parseTypeSpans #[]
        finishNode (Node.templateExpression {} head spans) pos
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
      | .importKeyword =>
        parseImportType
      -- Based on Go: parser.go:2687-2691 — asserts type predicate
      | .assertsKeyword =>
        let isAssertsPredicate ← lookAhead do
          nextToken
          let tok ← currentToken
          return (tok == Kind.identifier || tok == Kind.thisKeyword) &&
            !(← get).scanner.hasPrecedingLineBreak
        if isAssertsPredicate then
          let pos ← nodePos
          nextToken  -- skip 'asserts'
          let paramName ← if (← currentToken) == Kind.thisKeyword then parseTokenNode
            else parseIdentifier
          let typeNode ← if (← parseOptional Kind.isKeyword) then
            pure (some (← parseType'))
          else pure none
          finishNode (Node.typePredicate {} paramName typeNode) pos
        else
          -- 'asserts' as regular type reference
          let pos ← nodePos
          let name ← parseIdentifier
          let qname ← parseQualifiedNameRest name pos
          let typeArgs ← match (← currentToken) with
            | .lessThanToken => do
              let _ ← parseExpected Kind.lessThanToken
              let args ← parseDelimitedList .typeArguments isStartOfType (parseType')
              let _ ← parseExpected Kind.greaterThanToken
              pure (some args)
            | _ => pure none
          finishNode (Node.typeReference {} qname typeArgs) pos
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
      if (← get).scanner.hasPrecedingLineBreak then
        return current
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

partial def isUnambiguouslyStartOfFunctionType : ParserM Bool :=
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

partial def isStartOfFunctionOrConstructorType : ParserM Bool := do
  match (← currentToken) with
  | .lessThanToken | .newKeyword => return true
  | .openParenToken => isUnambiguouslyStartOfFunctionType
  | _ => return false

partial def parseErrorAtLoc (loc : TextRange) (msg : DiagnosticMessage)
    (args : Array String := #[]) : ParserM Unit :=
  modify fun p =>
    let diagnostics := p.diagnostics.push { loc := loc, message := msg, args := args }
    { p with diagnostics := diagnostics, hasParseError := true }

partial def parseFunctionOrConstructorTypeToError (isInUnionType : Bool) : ParserM Node := do
  let _ := isInUnionType
  parseType'

partial def parseTypeConstituentAfterOperator : ParserM Node := do
  match (← currentToken) with
  | .openParenToken | .lessThanToken | .newKeyword | .barToken | .ampersandToken =>
    parseType'
  | _ =>
    let primary ← parseTypeOperatorOrHigher
    parseIntersectionPostfix primary

/-- Parse intersection type: Type & Type & Type
    Based on Go: parser.go:2379 (parseIntersectionTypeOrHigher)
    Each intersection member is a primary type with array/indexed-access postfix. -/
partial def collectIntersectionTypes (acc : Array Node) : ParserM (Array Node) := do
    match (← currentToken) with
    | .ampersandToken =>
      nextToken
      let nextType ← parseTypeConstituentAfterOperator
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
      let member ← parseTypeConstituentAfterOperator
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
    if (← currentToken) == Kind.openBraceToken then
      let body ← parseBlock
      parseErrorAtLoc body.base.loc Diagnostics.implementation_cannot_be_declared_in_ambient_contexts
    else
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
    | .getKeyword | .setKeyword =>
      let accessorKind ← currentToken
      if ← parseContextualModifier accessorKind then
        nextToken
        let name ← parsePropertyName
        let questionToken ← parseOptionalToken Kind.questionToken
        parseTypeMemberPropertyOrMethod name questionToken pos
      else
        let name ← parsePropertyName
        let questionToken ← parseOptionalToken Kind.questionToken
        parseTypeMemberPropertyOrMethod name questionToken pos
    -- Call signature: (params): Type
    | .openParenToken | .lessThanToken =>
      let typeParams ← parseTypeParameters
      let params ← parseParameters
      let returnType ← parseReturnType
      parseTypeMemberSemicolon
      finishNode (Node.callSignature {} typeParams params returnType) pos
    -- Construct signature: new (params): Type
    | .newKeyword =>
      let isConstructSig ← lookAhead do
        nextToken
        let tok ← currentToken
        return tok == Kind.openParenToken || tok == Kind.lessThanToken
      if isConstructSig then
        nextToken
        let typeParams ← parseTypeParameters
        let params ← parseParameters
        let returnType ← parseReturnType
        parseTypeMemberSemicolon
        finishNode (Node.constructSignature {} typeParams params returnType) pos
      else
        let name ← parseIdentifierName
        let questionToken ← parseOptionalToken Kind.questionToken
        parseTypeMemberPropertyOrMethod name questionToken pos
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
      let isTP : ParserM Bool := do
        let tok ← currentToken
        return tok == Kind.inKeyword || tok == Kind.outKeyword || tok == Kind.constKeyword ||
          (← isIdentifierToken)
      let params ← parseDelimitedList .typeParameters isTP do
        let pos ← nodePos
        let rec skipTypeParamModifiers : ParserM Unit := do
          match (← currentToken) with
          | .inKeyword | .outKeyword | .constKeyword =>
            nextToken
            skipTypeParamModifiers
          | _ => pure ()
        skipTypeParamModifiers
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
    let tok ← currentToken
    if (tok == Kind.publicKeyword || tok == Kind.privateKeyword || tok == Kind.protectedKeyword ||
        tok == Kind.readonlyKeyword) && (← nextTokenCanFollowClassMemberModifier) then
      nextToken
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
      let params ← parseDelimitedList .parameters isStartOfParameterToken (parseParameter)
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
      | _ =>
        let savedFlags := (← get).contextFlags
        setContextFlag NodeFlags.disallowInContext true
        let expr ← parseExpression
        modify fun p => { p with contextFlags := savedFlags }
        pure (some expr)
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
        | .semicolonToken | .closeParenToken => pure none
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
    let savedFlags := (← get).contextFlags
    setContextFlag NodeFlags.disallowInContext false
    let isElem : ParserM Bool := isListElement .arrayBindingElements false
    let elements ← parseDelimitedList .arrayBindingElements isElem
      (parseArrayBindingElement)
    modify fun p => { p with contextFlags := savedFlags }
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
    let savedFlags := (← get).contextFlags
    setContextFlag NodeFlags.disallowInContext false
    let isElem : ParserM Bool := isListElement .objectBindingElements false
    let elements ← parseDelimitedList .objectBindingElements isElem
      (parseObjectBindingElement)
    modify fun p => { p with contextFlags := savedFlags }
    let _ ← parseExpected Kind.closeBraceToken
    finishNode (Node.objectBindingPattern {} elements) pos

/-- Based on Go: parser.go:1565 (parseObjectBindingElement) -/
partial def parseObjectBindingElement : ParserM Node :=
  do
    let pos ← nodePos
    let dotDotDot ← match (← currentToken) with
      | .dotDotDotToken => let n ← parseTokenNode; pure (some n)
      | _ => pure none
    let tokenIsBindingIdentifier ← isBindingIdentifierToken
    let nameOrPropName ← parsePropertyName
    let (propName, name) ←
      if tokenIsBindingIdentifier && (← currentToken) != Kind.colonToken then
        pure (none, nameOrPropName)
      else do
        let _ ← parseExpected Kind.colonToken
        let binding ← parseIdentifierOrPattern
        pure (some nameOrPropName, binding)
    let initializer ← parseInitializer
    finishNode (Node.bindingElement {} dotDotDot propName name initializer) pos

/-- Based on Go: parser.go:1495 (parseVariableDeclaration) -/
partial def parseVariableDeclaration : ParserM Node :=
  do
    let pos ← nodePos
    let name ← parseIdentifierOrPattern
    match name with
    | .identifier .. =>
      if (← currentToken) == Kind.exclamationToken && !(← get).scanner.hasPrecedingLineBreak then
        nextToken
    | _ => pure ()
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
    if flags.hasFlag NodeFlags.const_ &&
       !((← get).contextFlags.hasFlag NodeFlags.ambient) &&
       (← currentToken) != Kind.inKeyword && (← currentToken) != Kind.ofKeyword then
      for decl in decls do
        match decl with
        | .variableDeclaration _ _ _ initializer =>
          if initializer.isNone then
            parseErrorAtLoc decl.base.loc Diagnostics.declarations_must_be_initialized #[tokenToString Kind.constKeyword]
        | _ => pure ()
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
    -- Go: parser.go:1597 — asteriskToken for generator functions
    let _ ← parseOptional Kind.asteriskToken
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
    | .privateIdentifier =>
      -- Go: parser.go:3336 — private field name: #name
      let pos ← nodePos
      let text ← internIdentifier (← get).scanner.tokenValue
      nextToken
      finishNode (Node.identifier {} text) pos
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
    let rec skipModifiers (sawStaticLoc : Option TextRange := none) : ParserM Unit := do
      let tok ← currentToken
      if isModifierKind tok && (← nextTokenCanFollowClassMemberModifier) &&
          !(sawStaticLoc.isSome && tok == Kind.staticKeyword) then
        let p ← get
        let currentLoc := TextRange.mk' (Int.ofNat p.scanner.tokenStart) (Int.ofNat p.scanner.state.pos)
        match sawStaticLoc, tok with
        | some staticLoc, .publicKeyword
        | some staticLoc, .privateKeyword
        | some staticLoc, .protectedKeyword =>
          parseErrorAtLoc staticLoc Diagnostics.modifier_must_precede_modifier
            #[tokenToString tok, tokenToString Kind.staticKeyword]
        | _, _ => pure ()
        nextToken
        let sawStaticLoc := if tok == Kind.staticKeyword then some currentLoc else sawStaticLoc
        skipModifiers sawStaticLoc
      else
        pure ()
    skipModifiers
    let memberTok ← currentToken
    match memberTok with
    | .constructorKeyword =>
      nextToken
      let params ← parseParameters
      let body ← parseFunctionBlock
      finishNode (Node.constructor_ {} params body) pos
    | .getKeyword
    | .setKeyword =>
      let accessorKind ← currentToken
      let isAccessor ← parseContextualModifier accessorKind
      if isAccessor then
        nextToken
        let name ← parsePropertyName
        let questionToken ← parseOptionalToken Kind.questionToken
        parseMethodDeclarationRest pos name questionToken
      else
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
          if initializer.isSome || typeNode.isSome then
            let _ ← parseSemicolon
            pure ()
          else
            match name with
            | .identifier _ _ =>
              let _ ← tryParseSemicolon
              pure ()
            | _ =>
              let _ ← parseSemicolon
              pure ()
          finishNode (Node.propertyDeclaration {} name questionToken typeNode initializer) pos
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
        if initializer.isSome || typeNode.isSome then
          let _ ← parseSemicolon
          pure ()
        else
          match name with
          | .identifier _ _ =>
            let _ ← tryParseSemicolon
            pure ()
          | _ =>
            let _ ← parseSemicolon
            pure ()
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
    | .staticKeyword =>
      if ← nextTokenIsOpenBrace then
        nextToken
        parseBlock
      else if ← lookAhead (do nextToken; isIndexSignature) then
        nextToken
        let _ ← parseExpected Kind.openBracketToken
        let isIdx : ParserM Bool := do
          let tok ← currentToken
          let bindId ← isBindingIdentifierToken
          return bindId || tok == Kind.dotDotDotToken
        let params ← parseDelimitedList .parameters isIdx parseParameter
        let _ ← parseExpected Kind.closeBracketToken
        let typeNode ← parseTypeAnnotation
        let _ ← tryParseSemicolon
        finishNode (Node.indexSignature {} params typeNode) pos
      else
        parsePropertyOrMethodDeclaration
    | .openBracketToken =>
      if ← isIndexSignature then
        let _ ← parseExpected Kind.openBracketToken
        let isIdx : ParserM Bool := do
          let tok ← currentToken
          let bindId ← isBindingIdentifierToken
          return bindId || tok == Kind.dotDotDotToken
        let params ← parseDelimitedList .parameters isIdx parseParameter
        let _ ← parseExpected Kind.closeBracketToken
        let typeNode ← parseTypeAnnotation
        let _ ← tryParseSemicolon
        finishNode (Node.indexSignature {} params typeNode) pos
      else
        parsePropertyOrMethodDeclaration
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
      let isClassElem : ParserM Bool := isListElement .classMembers false
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
      | .stringLiteral | .noSubstitutionTemplateLiteral => parseLiteralExpression
      | .templateHead => parseTemplateExpression
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
    -- export as namespace Name;
    | .asKeyword =>
      nextToken
      let _ ← parseExpected Kind.namespaceKeyword
      let name ← parseIdentifierName
      let _ ← parseSemicolon
      let nsExport ← finishNode (Node.namespaceExport {} name) pos
      finishNode (Node.exportDeclaration {} (some nsExport) none) pos
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
    | .varKeyword =>
      parseVariableStatement
    | .letKeyword =>
      -- Based on Go: parser.go:954 (isLetDeclaration)
      -- Only parse as variable statement if followed by identifier, {, or [
      let isLetDecl ← lookAhead do
        nextToken
        let tok ← currentToken
        return (← isIdentifierToken) || tok == Kind.openBraceToken || tok == Kind.openBracketToken
      if isLetDecl then parseVariableStatement
      else parseExpressionOrLabeledStatement
    | .functionKeyword => parseFunctionDeclaration
    | .classKeyword => parseClassDeclaration
    | .importKeyword => parseImportDeclaration
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
      let savedFlags := (← get).contextFlags
      setContextFlag NodeFlags.ambient true
      let decl ← parseDeclarationAfterModifiers
      modify fun p => { p with contextFlags := savedFlags }
      pure decl
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
    | .varKeyword =>
      parseVariableStatement
    | .letKeyword =>
      -- Based on Go: parser.go:954 (isLetDeclaration)
      let isLetDecl ← lookAhead do
        nextToken
        let tok ← currentToken
        return (← isIdentifierToken) || tok == Kind.openBraceToken || tok == Kind.openBracketToken
      if isLetDecl then parseVariableStatement
      else parseExpressionOrLabeledStatement
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
      let savedFlags := (← get).contextFlags
      setContextFlag NodeFlags.ambient true
      let decl ← parseDeclarationAfterModifiers
      modify fun p => { p with contextFlags := savedFlags }
      pure decl
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
        let savedFlags := (← get).contextFlags
        setContextFlag NodeFlags.ambient true
        let decl ← parseDeclarationAfterModifiers
        modify fun p => { p with contextFlags := savedFlags }
        pure decl
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

@[inline] private def isAsciiIdentByte (b : UInt8) : Bool :=
  (b >= 0x41 && b <= 0x5A) || (b >= 0x61 && b <= 0x7A) || b == 0x5F

private partial def identifierEnd (bytes : ByteArray) (start stop : Nat) : Nat :=
  if start < stop then
    let b := bytes[start]!
    if isAsciiIdentByte b || (b >= 0x30 && b <= 0x39) then
      identifierEnd bytes (start + 1) stop
    else
      start
  else
    start

private partial def collectJsDocTypedefMissingSeparatorDiagnostics
    (bytes typedefPat : ByteArray)
    (searchPos commentEnd : Nat)
    (acc : Array Diagnostic) : Array Diagnostic :=
  match findSubarrayBounded bytes typedefPat searchPos commentEnd with
  | none => acc
  | some typedefIdx =>
    let afterTypedef := typedefIdx + typedefPat.size
    let acc' :=
      match findSubarrayBounded bytes "[".toUTF8 afterTypedef commentEnd with
      | none => acc
      | some bracketIdx =>
        match findSubarrayBounded bytes "]".toUTF8 (bracketIdx + 1) commentEnd with
        | none => acc
        | some closeBracketIdx =>
          let nextPos := skipAsciiWhitespace bytes (closeBracketIdx + 1) commentEnd
          if nextPos < commentEnd && isAsciiIdentByte bytes[nextPos]! then
            let endPos := identifierEnd bytes nextPos commentEnd
            acc.push
              { loc := TextRange.mk' nextPos endPos
              , message := Diagnostics.X_0_expected
              , args := #[tokenToString Kind.semicolonToken] }
          else
            acc
    collectJsDocTypedefMissingSeparatorDiagnostics
      bytes typedefPat (typedefIdx + typedefPat.size) commentEnd acc'

private partial def collectJsDocTypedefCommentsDiagnostics
    (bytes openPat closePat typedefPat : ByteArray)
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
        let acc' := collectJsDocTypedefMissingSeparatorDiagnostics
          bytes typedefPat (openIdx + openPat.size) closeIdx acc
        collectJsDocTypedefCommentsDiagnostics
          bytes openPat closePat typedefPat (closeIdx + closePat.size) acc'

/-- Add TS1110 diagnostics for invalid JSDoc `@type` forms where the type
    expression starts with an inline tag (`{@...}`).
    This covers cases like `/** @type {@import("a").Type} */`. -/
private def collectJsDocTypeDiagnostics (sourceText : String) : Array Diagnostic :=
  let bytes := sourceText.toUTF8
  let openPat := "/**".toUTF8
  let closePat := "*/".toUTF8
  let typePat := "@type".toUTF8
  let typedefPat := "@typedef".toUTF8
  let bracePat := "{".toUTF8
  let diags := collectJsDocCommentsDiagnostics bytes openPat closePat typePat bracePat 0 #[]
  collectJsDocTypedefCommentsDiagnostics bytes openPat closePat typedefPat 0 diags

/-- Based on Go: parser.go:114 (ParseSourceFile) -/
private def scannerDiagnosticToDiagnostic? (diag : ScannerDiagnostic) : Option Diagnostic :=
  let msg := diag.message
  let message :=
    if msg == Diagnostics.unterminated_string_literal.message then
      some Diagnostics.unterminated_string_literal
    else if msg == Diagnostics.invalid_character.message || msg == "Invalid character" then
      some Diagnostics.invalid_character
    else if msg == Diagnostics.unexpected_end_of_text.message || msg == "Unexpected end of text" then
      some Diagnostics.unexpected_end_of_text
    else if msg == Diagnostics.unterminated_regular_expression_literal.message then
      some Diagnostics.unterminated_regular_expression_literal
    else if msg == Diagnostics.unterminated_template_literal.message then
      some Diagnostics.unterminated_template_literal
    else
      none
  message.map fun message =>
    let start := diag.start
    let stop := start + diag.length
    { loc := TextRange.mk' (Int.ofNat start) (Int.ofNat stop), message := message }

private def grammarNodeChildren : Node → Array Node
  | .token .. | .identifier .. | .numericLiteral .. | .stringLiteral ..
  | .noSubstitutionTemplateLiteral .. | .emptyStatement ..
  | .debuggerStatement .. | .semicolonClassElement .. | .omittedExpression ..
  | .missing .. => #[]
  | .qualifiedName _ l r => #[l, r]
  | .computedPropertyName _ e => #[e]
  | .binaryExpression _ l op r => #[l, op, r]
  | .parenthesizedExpression _ e => #[e]
  | .prefixUnaryExpression _ _ e => #[e]
  | .postfixUnaryExpression _ e _ => #[e]
  | .propertyAccessExpression _ e n => #[e, n]
  | .elementAccessExpression _ e a => #[e, a]
  | .callExpression _ e args => #[e] ++ args
  | .newExpression _ e args => #[e] ++ (args.getD #[])
  | .taggedTemplateExpression _ t tl => #[t, tl]
  | .arrayLiteralExpression _ es => es
  | .objectLiteralExpression _ ps => ps
  | .functionExpression _ nm tps ps ret body =>
    nm.toArray ++ (tps.getD #[]) ++ ps ++ ret.toArray ++ body.toArray
  | .arrowFunction _ tps ps ret body =>
    (tps.getD #[]) ++ ps ++ ret.toArray ++ #[body]
  | .conditionalExpression _ c t f => #[c, t, f]
  | .templateExpression _ h spans => #[h] ++ spans
  | .templateSpan _ e lit => #[e, lit]
  | .spreadElement _ e => #[e]
  | .deleteExpression _ e => #[e]
  | .typeOfExpression _ e => #[e]
  | .voidExpression _ e => #[e]
  | .awaitExpression _ e => #[e]
  | .typeAssertionExpression _ t e => #[t, e]
  | .yieldExpression _ e => e.toArray
  | .asExpression _ e t => #[e, t]
  | .nonNullExpression _ e => #[e]
  | .satisfiesExpression _ e t => #[e, t]
  | .expressionWithTypeArguments _ e ta => #[e] ++ (ta.getD #[])
  | .propertyAssignment _ n init => #[n] ++ init.toArray
  | .shorthandPropertyAssignment _ n => #[n]
  | .spreadAssignment _ e => #[e]
  | .objectBindingPattern _ es => es
  | .arrayBindingPattern _ es => es
  | .bindingElement _ dot pn n init => dot.toArray ++ pn.toArray ++ #[n] ++ init.toArray
  | .expressionStatement _ e => #[e]
  | .block _ stmts => stmts
  | .ifStatement _ e t el => #[e, t] ++ el.toArray
  | .returnStatement _ e => e.toArray
  | .throwStatement _ e => e.toArray
  | .breakStatement _ lbl => lbl.toArray
  | .continueStatement _ lbl => lbl.toArray
  | .whileStatement _ e s => #[e, s]
  | .doStatement _ s e => #[s, e]
  | .forStatement _ init cond inc s => init.toArray ++ cond.toArray ++ inc.toArray ++ #[s]
  | .forInStatement _ init e s => init.toArray ++ #[e, s]
  | .forOfStatement _ init e s => init.toArray ++ #[e, s]
  | .switchStatement _ e clauses => #[e] ++ clauses
  | .caseClause _ e stmts => #[e] ++ stmts
  | .defaultClause _ stmts => stmts
  | .tryStatement _ tb cc fb => #[tb] ++ cc.toArray ++ fb.toArray
  | .catchClause _ vd blk => vd.toArray ++ #[blk]
  | .withStatement _ e s => #[e, s]
  | .labeledStatement _ l s => #[l, s]
  | .variableStatement _ dl => #[dl]
  | .variableDeclarationList _ _ ds => ds
  | .variableDeclaration _ n t init => #[n] ++ t.toArray ++ init.toArray
  | .functionDeclaration _ nm tps ps ret body =>
    nm.toArray ++ (tps.getD #[]) ++ ps ++ ret.toArray ++ body.toArray
  | .parameterDeclaration _ dot n q t init =>
    dot.toArray ++ #[n] ++ q.toArray ++ t.toArray ++ init.toArray
  | .classDeclaration _ nm tps hcs ms =>
    nm.toArray ++ (tps.getD #[]) ++ (hcs.getD #[]) ++ ms
  | .methodDeclaration _ n q tps ps ret body =>
    #[n] ++ q.toArray ++ (tps.getD #[]) ++ ps ++ ret.toArray ++ body.toArray
  | .propertyDeclaration _ n q t init => #[n] ++ q.toArray ++ t.toArray ++ init.toArray
  | .constructor_ _ ps body => ps ++ body.toArray
  | .interfaceDeclaration _ n tps hcs ms =>
    #[n] ++ (tps.getD #[]) ++ (hcs.getD #[]) ++ ms
  | .typeAliasDeclaration _ n tps t => #[n] ++ (tps.getD #[]) ++ #[t]
  | .enumDeclaration _ n ms => #[n] ++ ms
  | .enumMember _ n init => #[n] ++ init.toArray
  | .moduleDeclaration _ n body => #[n] ++ body.toArray
  | .moduleBlock _ stmts => stmts
  | .propertySignature _ n q t => #[n] ++ q.toArray ++ t.toArray
  | .methodSignature _ n q tps ps ret => #[n] ++ q.toArray ++ (tps.getD #[]) ++ ps ++ ret.toArray
  | .callSignature _ tps ps ret => (tps.getD #[]) ++ ps ++ ret.toArray
  | .constructSignature _ tps ps ret => (tps.getD #[]) ++ ps ++ ret.toArray
  | .indexSignature _ ps t => ps ++ t.toArray
  | .heritageClause _ _ ts => ts
  | .importDeclaration _ ic ms => ic.toArray ++ #[ms]
  | .importClause _ n nb => n.toArray ++ nb.toArray
  | .namedImports _ es => es
  | .importSpecifier _ pn n => pn.toArray ++ #[n]
  | .namespaceImport _ n => #[n]
  | .importEqualsDeclaration _ n mr => #[n, mr]
  | .externalModuleReference _ e => #[e]
  | .exportDeclaration _ ec ms => ec.toArray ++ ms.toArray
  | .exportAssignment _ e => #[e]
  | .namedExports _ es => es
  | .exportSpecifier _ pn n => pn.toArray ++ #[n]
  | .namespaceExport _ n => #[n]
  | .importAttributes _ _ es => es
  | .importAttribute _ n v => #[n, v]
  | .typeReference _ tn ta => #[tn] ++ (ta.getD #[])
  | .unionType _ ts => ts
  | .intersectionType _ ts => ts
  | .arrayType _ et => #[et]
  | .tupleType _ es => es
  | .functionType _ tps ps ret => (tps.getD #[]) ++ ps ++ ret.toArray
  | .constructorType _ tps ps ret => (tps.getD #[]) ++ ps ++ ret.toArray
  | .typeLiteral _ ms => ms
  | .parenthesizedType _ t => #[t]
  | .typeQuery _ en => #[en]
  | .typeOperator _ _ t => #[t]
  | .literalType _ lit => #[lit]
  | .conditionalType _ c e t f => #[c, e, t, f]
  | .inferType _ tp => #[tp]
  | .indexedAccessType _ o i => #[o, i]
  | .mappedType _ tp nt t => #[tp] ++ nt.toArray ++ t.toArray
  | .typePredicate _ pn t => #[pn] ++ t.toArray
  | .optionalType _ t => #[t]
  | .restType _ t => #[t]
  | .namedTupleMember _ d n q t => d.toArray ++ #[n] ++ q.toArray ++ #[t]
  | .importType _ _ a attrs q ta => #[a] ++ attrs.toArray ++ q.toArray ++ (ta.getD #[])
  | .sourceFile _ stmts eof => stmts ++ #[eof]

private def sourceSlice (sourceText : String) (start stop : Int32) : String :=
  let bytes := sourceText.toUTF8
  let s := start.toInt.toNat
  let e := stop.toInt.toNat
  String.fromUTF8! (bytes.extract s e)

private partial def findAsciiOffset (sourceText : String) (start stop : Int32) (needle : String) : Nat :=
  let haystack := sourceText.toUTF8
  let needleBytes := needle.toUTF8
  let s := start.toInt.toNat
  let e := stop.toInt.toNat
  let rec go (i : Nat) : Nat :=
    if i + needleBytes.size > e then s
    else
      let rec matchesAt (j : Nat) : Bool :=
        if j >= needleBytes.size then true
        else if haystack[i + j]! == needleBytes[j]! then matchesAt (j + 1)
        else false
      if matchesAt 0 then i else go (i + 1)
  go s

private def computeLineStarts (text : String) : Array Nat :=
  let bytes := text.toUTF8
  let rec go (i : Nat) (acc : Array Nat) : Array Nat :=
    if i >= bytes.size then acc
    else
      let b := bytes[i]!
      if b == 10 then
        go (i + 1) (acc.push (i + 1))
      else if b == 13 then
        if i + 1 < bytes.size && bytes[i + 1]! == 10 then
          go (i + 2) (acc.push (i + 2))
        else
          go (i + 1) (acc.push (i + 1))
      else
        go (i + 1) acc
  go 0 #[0]

private def positionToLine (lineStarts : Array Nat) (pos : Nat) : Nat :=
  let rec go (lo hi : Nat) : Nat :=
    if lo + 1 >= hi then lo
    else
      let mid := (lo + hi) / 2
      if lineStarts[mid]! <= pos then go mid hi else go lo mid
  go 0 lineStarts.size

private def posToNat (p : Int32) : Nat :=
  if p < 0 then 0 else p.toInt.toNat

private def isIgnoredDiagnostic (lineStarts : Array Nat) (commentDirectives : Array CommentDirective)
    (diag : Diagnostic) : Bool :=
  let diagLine := positionToLine lineStarts (posToNat diag.loc.pos)
  commentDirectives.any fun directive =>
    directive.kind == CommentDirectiveKind.ignore &&
    positionToLine lineStarts (posToNat directive.loc.end_) + 1 == diagLine

private def functionHeaderHasGeneratorStar (sourceText : String) (fnNode bodyNode : Node) : Bool :=
  let header := sourceSlice sourceText fnNode.base.loc.pos bodyNode.base.loc.pos
  header.contains '*'

private partial def isConstantEnumExpression : Node → Bool
  | .numericLiteral .. | .stringLiteral .. | .noSubstitutionTemplateLiteral .. | .identifier .. => true
  | .prefixUnaryExpression _ op expr =>
    op == Kind.plusToken || op == Kind.minusToken || op == Kind.tildeToken && isConstantEnumExpression expr
  | .parenthesizedExpression _ expr =>
    isConstantEnumExpression expr
  | .propertyAccessExpression _ expr _ =>
    match expr with
    | .identifier .. => true
    | .propertyAccessExpression .. => isConstantEnumExpression expr
    | _ => false
  | .elementAccessExpression _ expr arg =>
    isConstantEnumExpression expr && isConstantEnumExpression arg
  | .binaryExpression _ left op right =>
    (op.kind == Kind.barToken || op.kind == Kind.ampersandToken || op.kind == Kind.caretToken ||
      op.kind == Kind.lessThanLessThanToken || op.kind == Kind.greaterThanGreaterThanToken ||
      op.kind == Kind.greaterThanGreaterThanGreaterThanToken || op.kind == Kind.plusToken ||
      op.kind == Kind.minusToken || op.kind == Kind.asteriskToken || op.kind == Kind.slashToken ||
      op.kind == Kind.percentToken) &&
      isConstantEnumExpression left && isConstantEnumExpression right
  | _ => false

private def statementIsUseStrictPrologue (stmt : Node) : Bool :=
  match stmt with
  | .expressionStatement _ (.stringLiteral _ text) => text == "use strict"
  | _ => false

private def hasUseStrictPrologue (stmts : Array Node) : Bool :=
  let rec go (i : Nat) : Bool :=
    if i >= stmts.size then false
    else
      match stmts[i]! with
      | .expressionStatement _ (.stringLiteral _ text) =>
        if text == "use strict" then true else go (i + 1)
      | _ => false
  go 0

private def isAmbientStatementDiagnosticCandidate (node : Node) : Bool :=
  match node with
  | .whileStatement .. => true
  | _ => false

private partial def isAmbientConstEnumReference (node : Node) : Bool :=
  match node with
  | .identifier .. => true
  | .propertyAccessExpression _ target _ => isAmbientConstEnumReference target
  | .elementAccessExpression _ target arg =>
    isAmbientConstEnumReference target &&
      match arg with
      | .stringLiteral .. | .numericLiteral .. | .noSubstitutionTemplateLiteral .. => true
      | _ => false
  | _ => false

private def isAllowedAmbientConstInitializer (node : Node) : Bool :=
  match node with
  | .stringLiteral .. | .numericLiteral .. | .noSubstitutionTemplateLiteral .. => true
  | .token _ kind => kind == Kind.trueKeyword || kind == Kind.falseKeyword
  | .prefixUnaryExpression _ op operand =>
    op == Kind.minusToken &&
      match operand with
      | .numericLiteral .. => true
      | _ => false
  | _ => isAmbientConstEnumReference node

private partial def collectGrammarDiagnostics
    (sourceText : String) (inStrict : Bool) (inGenerator : Bool) (allowBreak : Bool) (allowContinue : Bool)
    (node : Node) : Array Diagnostic :=
  let here :=
    match node with
    | .yieldExpression base _ =>
      if inGenerator then
        #[]
      else
        let start := base.loc.pos.toInt
        #[{ loc := TextRange.mk' start (start + 5), message := Diagnostics.yield_expression_only_allowed_in_generator_body }]
    | .variableDeclarationList base declFlags decls =>
      if base.flags.hasFlag NodeFlags.ambient then
        decls.foldl
          (fun acc decl =>
            match decl with
            | .variableDeclaration _ _ typeNode initializer =>
              match initializer with
              | some init =>
                if declFlags.hasFlag NodeFlags.const_ && typeNode.isNone then
                  if isAllowedAmbientConstInitializer init then
                    acc
                  else
                    acc.push { loc := init.base.loc, message := Diagnostics.const_initializer_in_ambient_context_must_be_literal_or_enum_reference }
                else
                  acc.push { loc := init.base.loc, message := Diagnostics.initializers_not_allowed_in_ambient_contexts }
              | none => acc
            | _ => acc)
          #[]
      else
        #[]
    | .variableDeclaration _ name _ _ =>
      let strictDiags :=
        if inStrict then
          match name with
          | .identifier nameBase text =>
            if text == "eval" || text == "arguments" then
              #[{ loc := nameBase.loc, message := Diagnostics.invalid_use_of_0_in_strict_mode, args := #[text] }]
            else
              #[]
          | _ => #[]
        else
          #[]
      strictDiags
    | .enumMember base _ initializer =>
      if base.flags.hasFlag NodeFlags.ambient then
        match initializer with
        | some init =>
          if isConstantEnumExpression init then
            #[]
          else
            #[{ loc := init.base.loc, message := Diagnostics.ambient_enum_member_initializer_must_be_constant_expression }]
        | none =>
          #[]
      else
        #[]
    | _ => #[]
  let childStrict :=
    match node with
    | .sourceFile _ stmts _ => inStrict || hasUseStrictPrologue stmts
    | .block _ stmts => inStrict || hasUseStrictPrologue stmts
    | .moduleBlock _ stmts => inStrict || hasUseStrictPrologue stmts
    | _ => inStrict
  let childGenerator :=
    match node with
    | .functionDeclaration _ _ _ _ _ (some body) => functionHeaderHasGeneratorStar sourceText node body
    | .functionExpression _ _ _ _ _ (some body) => functionHeaderHasGeneratorStar sourceText node body
    | .methodDeclaration _ _ _ _ _ _ (some body) => functionHeaderHasGeneratorStar sourceText node body
    | _ => inGenerator
  let (childAllowBreak, childAllowContinue) :=
    match node with
    | .whileStatement .. | .doStatement .. | .forStatement .. | .forInStatement .. | .forOfStatement .. =>
      (true, true)
    | .switchStatement .. =>
      (true, allowContinue)
    | _ =>
      (allowBreak, allowContinue)
  let foldChildren (children : Array Node) : Array Diagnostic :=
    (children.foldl
      (fun (state : Array Diagnostic × Bool) child =>
        let (acc, hasReportedAmbientStatement) := state
        let ambientDiags :=
          if !hasReportedAmbientStatement && child.base.flags.hasFlag NodeFlags.ambient && isAmbientStatementDiagnosticCandidate child then
            #[{ loc := child.base.loc, message := Diagnostics.statements_not_allowed_in_ambient_contexts }]
          else
            #[]
        let childDiags :=
          collectGrammarDiagnostics sourceText childStrict childGenerator childAllowBreak childAllowContinue child
        (acc ++ ambientDiags ++ childDiags, hasReportedAmbientStatement || !ambientDiags.isEmpty))
      (here, false)).fst
  match node with
  | .sourceFile _ stmts _ => foldChildren stmts
  | .block _ stmts => foldChildren stmts
  | .moduleBlock _ stmts => foldChildren stmts
  | _ =>
    grammarNodeChildren node |>.foldl
      (fun acc child =>
        acc ++ collectGrammarDiagnostics sourceText childStrict childGenerator childAllowBreak childAllowContinue child)
      here

def parseSourceFile (fileName : String) (sourceText : String)
    (scriptKind : ScriptKind) (alwaysStrict : Bool := false) : ParseResult :=
  let initialContextFlags :=
    if fileName.endsWith ".d.ts" then NodeFlags.ambient else NodeFlags.none
  let p := { Parser.initializeState sourceText scriptKind with contextFlags := initialContextFlags }
  let action : ParserM Node := do nextToken; parseSourceFileWorker
  let (result, p) := action |>.run p
  let scannerDiagnostics := p.scanner.diagnostics.filterMap scannerDiagnosticToDiagnostic?
  let lineStarts := computeLineStarts sourceText
  let grammarDiagnostics :=
    (collectGrammarDiagnostics sourceText alwaysStrict false false false result).filter fun diag =>
      !(isIgnoredDiagnostic lineStarts p.scanner.state.commentDirectives diag)
  { result := result
  , diagnostics := scannerDiagnostics ++ p.diagnostics ++ grammarDiagnostics ++ collectJsDocTypeDiagnostics sourceText }

end TSLean.Compiler
