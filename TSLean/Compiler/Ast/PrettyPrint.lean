/-
  TSLean.Compiler.Ast.PrettyPrint — Pretty-print AST nodes as indented trees.
-/
import TSLean.Compiler.Ast.Kind
import TSLean.Compiler.Ast.NodeFlags
import TSLean.Compiler.Ast.Node

namespace TSLean.Compiler

-- ============================================================
-- Kind → readable name
-- ============================================================

private def kindNameTable : Array String := #[
  "Unknown", "EndOfFile", "SingleLineCommentTrivia", "MultiLineCommentTrivia",
  "NewLineTrivia", "WhitespaceTrivia", "ConflictMarkerTrivia", "NonTextFileMarkerTrivia",
  "NumericLiteral", "BigIntLiteral", "StringLiteral", "JsxText",
  "JsxTextAllWhiteSpaces", "RegularExpressionLiteral", "NoSubstitutionTemplateLiteral",
  "TemplateHead", "TemplateMiddle", "TemplateTail",
  "OpenBraceToken", "CloseBraceToken", "OpenParenToken", "CloseParenToken",
  "OpenBracketToken", "CloseBracketToken", "DotToken", "DotDotDotToken",
  "SemicolonToken", "CommaToken", "QuestionDotToken", "LessThanToken",
  "LessThanSlashToken", "GreaterThanToken", "LessThanEqualsToken", "GreaterThanEqualsToken",
  "EqualsEqualsToken", "ExclamationEqualsToken", "EqualsEqualsEqualsToken",
  "ExclamationEqualsEqualsToken", "EqualsGreaterThanToken", "PlusToken", "MinusToken",
  "AsteriskToken", "AsteriskAsteriskToken", "SlashToken", "PercentToken",
  "PlusPlusToken", "MinusMinusToken", "LessThanLessThanToken",
  "GreaterThanGreaterThanToken", "GreaterThanGreaterThanGreaterThanToken",
  "AmpersandToken", "BarToken", "CaretToken", "ExclamationToken", "TildeToken",
  "AmpersandAmpersandToken", "BarBarToken", "QuestionToken", "ColonToken",
  "AtToken", "QuestionQuestionToken", "BacktickToken", "HashToken",
  "EqualsToken", "PlusEqualsToken", "MinusEqualsToken", "AsteriskEqualsToken",
  "AsteriskAsteriskEqualsToken", "SlashEqualsToken", "PercentEqualsToken",
  "LessThanLessThanEqualsToken", "GreaterThanGreaterThanEqualsToken",
  "GreaterThanGreaterThanGreaterThanEqualsToken", "AmpersandEqualsToken",
  "BarEqualsToken", "BarBarEqualsToken", "AmpersandAmpersandEqualsToken",
  "QuestionQuestionEqualsToken", "CaretEqualsToken",
  "Identifier", "PrivateIdentifier", "JsDocCommentTextToken",
  "break", "case", "catch", "class", "const", "continue", "debugger", "default",
  "delete", "do", "else", "enum", "export", "extends", "false", "finally",
  "for", "function", "if", "import", "in", "instanceof", "new", "null",
  "return", "super", "switch", "this", "throw", "true", "try", "typeof",
  "var", "void", "while", "with",
  "implements", "interface", "let", "package", "private", "protected", "public",
  "static", "yield",
  "abstract", "accessor", "as", "asserts", "assert", "any", "async", "await",
  "boolean", "constructor", "declare", "get", "immediate", "infer", "intrinsic",
  "is", "keyof", "module", "namespace", "never", "out", "readonly", "require",
  "number", "object", "satisfies", "set", "string", "symbol", "type",
  "undefined", "unique", "unknown", "using", "from", "global", "bigint",
  "override", "of", "defer",
  "QualifiedName", "ComputedPropertyName",
  "TypeParameter", "Parameter", "Decorator",
  "PropertySignature", "PropertyDeclaration", "MethodSignature", "MethodDeclaration",
  "ClassStaticBlockDeclaration", "Constructor", "GetAccessor", "SetAccessor",
  "CallSignature", "ConstructSignature", "IndexSignature",
  "TypePredicate", "TypeReference", "FunctionType", "ConstructorType",
  "TypeQuery", "TypeLiteral", "ArrayType", "TupleType", "OptionalType", "RestType",
  "UnionType", "IntersectionType", "ConditionalType", "InferType",
  "ParenthesizedType", "ThisType", "TypeOperator", "IndexedAccessType",
  "MappedType", "LiteralType", "NamedTupleMember", "TemplateLiteralType",
  "TemplateLiteralTypeSpan", "ImportType",
  "ObjectBindingPattern", "ArrayBindingPattern", "BindingElement",
  "ArrayLiteralExpression", "ObjectLiteralExpression", "PropertyAccessExpression",
  "ElementAccessExpression", "CallExpression", "NewExpression",
  "TaggedTemplateExpression", "TypeAssertionExpression", "ParenthesizedExpression",
  "FunctionExpression", "ArrowFunction", "DeleteExpression", "TypeOfExpression",
  "VoidExpression", "AwaitExpression", "PrefixUnaryExpression", "PostfixUnaryExpression",
  "BinaryExpression", "ConditionalExpression", "TemplateExpression", "YieldExpression",
  "SpreadElement", "ClassExpression", "OmittedExpression",
  "ExpressionWithTypeArguments", "AsExpression", "NonNullExpression",
  "MetaProperty", "SyntheticExpression", "SatisfiesExpression",
  "TemplateSpan", "SemicolonClassElement",
  "Block", "EmptyStatement", "VariableStatement", "ExpressionStatement",
  "IfStatement", "DoStatement", "WhileStatement", "ForStatement",
  "ForInStatement", "ForOfStatement", "ContinueStatement", "BreakStatement",
  "ReturnStatement", "WithStatement", "SwitchStatement", "LabeledStatement",
  "ThrowStatement", "TryStatement", "DebuggerStatement",
  "VariableDeclaration", "VariableDeclarationList", "FunctionDeclaration",
  "ClassDeclaration", "InterfaceDeclaration", "TypeAliasDeclaration",
  "EnumDeclaration", "ModuleDeclaration", "ModuleBlock", "CaseBlock",
  "NamespaceExportDeclaration", "ImportEqualsDeclaration", "ImportDeclaration",
  "ImportClause", "NamespaceImport", "NamedImports", "ImportSpecifier",
  "ExportAssignment", "ExportDeclaration", "NamedExports", "NamespaceExport",
  "ExportSpecifier", "MissingDeclaration",
  "ExternalModuleReference",
  "JsxElement", "JsxSelfClosingElement", "JsxOpeningElement", "JsxClosingElement",
  "JsxFragment", "JsxOpeningFragment", "JsxClosingFragment", "JsxAttribute",
  "JsxAttributes", "JsxSpreadAttribute", "JsxExpression", "JsxNamespacedName",
  "CaseClause", "DefaultClause", "HeritageClause", "CatchClause",
  "ImportAttributes", "ImportAttribute",
  "PropertyAssignment", "ShorthandPropertyAssignment", "SpreadAssignment",
  "EnumMember",
  "SourceFile",
  "JsDocTypeExpression", "JsDocNameReference", "JsDocMemberName", "JsDocAllType",
  "JsDocNullableType", "JsDocNonNullableType", "JsDocOptionalType",
  "JsDocVariadicType", "JsDoc", "JsDocText", "JsDocTypeLiteral", "JsDocSignature",
  "JsDocLink", "JsDocLinkCode", "JsDocLinkPlain", "JsDocTag", "JsDocAugmentsTag",
  "JsDocImplementsTag", "JsDocDeprecatedTag", "JsDocPublicTag", "JsDocPrivateTag",
  "JsDocProtectedTag", "JsDocReadonlyTag", "JsDocOverrideTag", "JsDocCallbackTag",
  "JsDocOverloadTag", "JsDocParameterTag", "JsDocReturnTag", "JsDocThisTag",
  "JsDocTypeTag", "JsDocTemplateTag", "JsDocTypedefTag", "JsDocSeeTag",
  "JsDocPropertyTag", "JsDocSatisfiesTag", "JsDocImportTag",
  "SyntaxList", "JsTypeAliasDeclaration", "JsExportAssignment", "CommonJSExport",
  "JsImportDeclaration", "NotEmittedStatement", "PartiallyEmittedExpression",
  "CommaListExpression", "SyntheticReferenceExpression", "NotEmittedTypeElement",
  "Count"
]

def kindName (k : Kind) : String :=
  let idx := k.val.toNat
  if idx < kindNameTable.size then kindNameTable[idx]!
  else s!"Kind({k.val})"

-- ============================================================
-- NodeFlags → readable name
-- ============================================================

def flagsStr (f : NodeFlags) : String :=
  let v := f.val
  if v == 0 then ""
  else
    let checks : List (UInt32 × String) := [
      (1, "let"), (2, "const"), (4, "using"), (8, "awaitUsing"),
      (16, "export"), (32, "ambient"), (64, "public"), (128, "private"),
      (256, "protected"), (512, "static"), (1024, "readonly"), (2048, "abstract"),
      (4096, "async"), (8192, "default"), (65536, "generator"), (131072, "decorator")]
    let parts := checks.foldl (init := #[]) fun acc (mask, name) =>
      if v &&& mask != 0 then acc.push name else acc
    if parts.isEmpty then s!" flags={v}" else " " ++ " ".intercalate parts.toList

-- ============================================================
-- Node child extraction (for tree walking)
-- ============================================================

private def nodeChildren : Node → Array Node
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
  | .bindingElement _ dot pn n init =>
    dot.toArray ++ pn.toArray ++ #[n] ++ init.toArray
  | .expressionStatement _ e => #[e]
  | .block _ stmts => stmts
  | .ifStatement _ e t el => #[e, t] ++ el.toArray
  | .returnStatement _ e => e.toArray
  | .throwStatement _ e => e.toArray
  | .breakStatement _ lbl => lbl.toArray
  | .continueStatement _ lbl => lbl.toArray
  | .whileStatement _ e s => #[e, s]
  | .doStatement _ s e => #[s, e]
  | .forStatement _ init cond inc s =>
    init.toArray ++ cond.toArray ++ inc.toArray ++ #[s]
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
  | .propertyDeclaration _ n q t init =>
    #[n] ++ q.toArray ++ t.toArray ++ init.toArray
  | .constructor_ _ ps body => ps ++ body.toArray
  | .interfaceDeclaration _ n tps hcs ms =>
    #[n] ++ (tps.getD #[]) ++ (hcs.getD #[]) ++ ms
  | .typeAliasDeclaration _ n tps t => #[n] ++ (tps.getD #[]) ++ #[t]
  | .enumDeclaration _ n ms => #[n] ++ ms
  | .enumMember _ n init => #[n] ++ init.toArray
  | .moduleDeclaration _ n body => #[n] ++ body.toArray
  | .moduleBlock _ stmts => stmts
  | .propertySignature _ n q t => #[n] ++ q.toArray ++ t.toArray
  | .methodSignature _ n q tps ps ret =>
    #[n] ++ q.toArray ++ (tps.getD #[]) ++ ps ++ ret.toArray
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

-- ============================================================
-- Pretty-print a node line
-- ============================================================

private def nodeLabel (n : Node) : String :=
  let name := kindName n.kind
  let b := n.base
  let span := s!"[{b.loc.pos}..{b.loc.end_})"
  let extra := match n with
    | .identifier _ text => s!" \"{text}\""
    | .numericLiteral _ text => s!" {text}"
    | .stringLiteral _ text => s!" \"{text}\""
    | .noSubstitutionTemplateLiteral _ text => s!" `{text}`"
    | .missing _ k => s!" (missing {kindName k})"
    | .variableDeclarationList _ f _ => flagsStr f
    | .prefixUnaryExpression _ op _ => s!" {kindName op}"
    | .postfixUnaryExpression _ _ op => s!" {kindName op}"
    | .typeOperator _ op _ => s!" {kindName op}"
    | .heritageClause _ tok _ => s!" {kindName tok}"
    | _ => ""
  s!"{name}{extra} {span}"

-- ============================================================
-- Tree printer
-- ============================================================

partial def ppTree (node : Node) (indent : String := "") (isLast : Bool := true) (isRoot : Bool := true) : String :=
  let connector := if isRoot then "" else if isLast then "└─ " else "├─ "
  let line := s!"{indent}{connector}{nodeLabel node}\n"
  let children := nodeChildren node
  let nextIndent := if isRoot then ""
    else indent ++ (if isLast then "   " else "│  ")
  let rec go (i : Nat) (acc : String) : String :=
    if i >= children.size then acc
    else
      let child := children[i]!
      go (i + 1) (acc ++ ppTree child nextIndent (i + 1 == children.size) false)
  go 0 line

end TSLean.Compiler
