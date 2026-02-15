/-
  TSLean.Compiler.Ast.Utilities — AST helper functions.

  Based on Go: internal/ast/utilities.go, internal/scanner/scanner.go (TokenToString)
-/
import TSLean.Compiler.Ast.Kind
import TSLean.Compiler.Ast.Node
import TSLean.Compiler.Scanner.Keywords
import Std.Data.HashMap

open Std

namespace TSLean.Compiler

/-- Based on Go: internal/scanner/scanner.go (TokenToString via textToToken map)
    Returns the string representation of a token kind.
    Uses reversed textToToken HashMap for O(1) lookup. -/
private def kindToTextMap : HashMap Kind String :=
  let pairs := textToToken.toList
  HashMap.ofList (pairs.map fun (text, kind) => (kind, text))

def tokenToString (kind : Kind) : String :=
  match kindToTextMap[kind]? with
  | some s => s
  | none => ""

open Kind in
/-- Based on Go: internal/ast/utilities.go (IsModifierKind)
    Checks if a token kind is a modifier keyword. -/
def isModifierKind (kind : Kind) : Bool :=
  kind == abstractKeyword || kind == accessorKeyword || kind == asyncKeyword ||
  kind == constKeyword || kind == declareKeyword || kind == defaultKeyword ||
  kind == exportKeyword || kind == inKeyword || kind == outKeyword ||
  kind == overrideKeyword || kind == privateKeyword || kind == protectedKeyword ||
  kind == publicKeyword || kind == readonlyKeyword || kind == staticKeyword

open Kind in
/-- Based on Go: internal/ast/utilities.go (IsClassMemberModifier) -/
def isClassMemberModifier (kind : Kind) : Bool :=
  kind == publicKeyword || kind == privateKeyword || kind == protectedKeyword ||
  kind == staticKeyword || kind == readonlyKeyword || kind == accessorKeyword ||
  kind == abstractKeyword || kind == overrideKeyword

open Kind in
/-- Checks whether a token is an identifier or keyword.
    Based on Go: internal/parser/utilities.go (tokenIsIdentifierOrKeyword) -/
def tokenIsIdentifierOrKeyword (kind : Kind) : Bool :=
  kind == Kind.identifier || Kind.isKeywordKind kind

open Kind in
/-- Checks whether a token kind is a keyword type (number, string, void, etc.).
    Based on Go: internal/ast/utilities.go -/
def isKeywordType (kind : Kind) : Bool :=
  kind == anyKeyword || kind == unknownKeyword || kind == stringKeyword ||
  kind == numberKeyword || kind == bigIntKeyword || kind == symbolKeyword ||
  kind == booleanKeyword || kind == undefinedKeyword || kind == neverKeyword ||
  kind == objectKeyword || kind == intrinsicKeyword || kind == voidKeyword

open Kind in
/-- Based on Go: internal/ast/utilities.go (IsLeftHandSideExpressionKind) -/
def isLeftHandSideExpressionKind (kind : Kind) : Bool :=
  kind == Kind.propertyAccessExpression || kind == Kind.elementAccessExpression ||
  kind == Kind.callExpression || kind == Kind.identifier ||
  kind == Kind.numericLiteral || kind == Kind.stringLiteral ||
  kind == Kind.parenthesizedExpression || kind == Kind.thisKeyword ||
  kind == Kind.superKeyword || kind == Kind.nullKeyword ||
  kind == Kind.trueKeyword || kind == Kind.falseKeyword ||
  kind == Kind.regularExpressionLiteral || kind == Kind.arrayLiteralExpression ||
  kind == Kind.objectLiteralExpression || kind == Kind.functionExpression ||
  kind == Kind.classExpression || kind == Kind.newExpression ||
  kind == Kind.taggedTemplateExpression || kind == Kind.templateExpression ||
  kind == Kind.noSubstitutionTemplateLiteral || kind == Kind.bigIntLiteral

/-- Based on Go: internal/ast/utilities.go (IsLeftHandSideExpression) -/
def isLeftHandSideExpression (node : Node) : Bool :=
  isLeftHandSideExpressionKind node.kind

end TSLean.Compiler
