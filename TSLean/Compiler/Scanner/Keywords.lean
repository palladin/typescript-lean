/-
  TSLean.Compiler.Scanner.Keywords — Keyword and token text-to-Kind maps.

  Based on Go: internal/scanner/scanner.go (lines 35-189)
  Go vars: textToKeyword (map[string]ast.Kind), textToToken (map[string]ast.Kind)
-/
import TSLean.Compiler.Ast.Kind
import Std.Data.HashMap

open Std

namespace TSLean.Compiler

open Kind in
/-- Based on Go: internal/scanner/scanner.go:35-121 (textToKeyword)
    81 keyword entries mapping string → Kind.
    Uses Std.HashMap for O(1) lookup. -/
def textToKeyword : HashMap String Kind :=
  HashMap.ofList
  [ ("abstract",    abstractKeyword)
  , ("accessor",    accessorKeyword)
  , ("any",         anyKeyword)
  , ("as",          asKeyword)
  , ("asserts",     assertsKeyword)
  , ("assert",      assertKeyword)
  , ("bigint",      bigIntKeyword)
  , ("boolean",     booleanKeyword)
  , ("break",       breakKeyword)
  , ("case",        caseKeyword)
  , ("catch",       catchKeyword)
  , ("class",       classKeyword)
  , ("continue",    continueKeyword)
  , ("const",       constKeyword)
  , ("constructor", constructorKeyword)
  , ("debugger",    debuggerKeyword)
  , ("declare",     declareKeyword)
  , ("default",     defaultKeyword)
  , ("defer",       deferKeyword)
  , ("delete",      deleteKeyword)
  , ("do",          doKeyword)
  , ("else",        elseKeyword)
  , ("enum",        enumKeyword)
  , ("export",      exportKeyword)
  , ("extends",     extendsKeyword)
  , ("false",       falseKeyword)
  , ("finally",     finallyKeyword)
  , ("for",         forKeyword)
  , ("from",        fromKeyword)
  , ("function",    functionKeyword)
  , ("get",         getKeyword)
  , ("if",          ifKeyword)
  , ("immediate",   immediateKeyword)
  , ("implements",  implementsKeyword)
  , ("import",      importKeyword)
  , ("in",          inKeyword)
  , ("infer",       inferKeyword)
  , ("instanceof",  instanceOfKeyword)
  , ("interface",   interfaceKeyword)
  , ("intrinsic",   intrinsicKeyword)
  , ("is",          isKeyword)
  , ("keyof",       keyOfKeyword)
  , ("let",         letKeyword)
  , ("module",      moduleKeyword)
  , ("namespace",   namespaceKeyword)
  , ("never",       neverKeyword)
  , ("new",         newKeyword)
  , ("null",        nullKeyword)
  , ("number",      numberKeyword)
  , ("object",      objectKeyword)
  , ("package",     packageKeyword)
  , ("private",     privateKeyword)
  , ("protected",   protectedKeyword)
  , ("public",      publicKeyword)
  , ("override",    overrideKeyword)
  , ("out",         outKeyword)
  , ("readonly",    readonlyKeyword)
  , ("require",     requireKeyword)
  , ("global",      globalKeyword)
  , ("return",      returnKeyword)
  , ("satisfies",   satisfiesKeyword)
  , ("set",         setKeyword)
  , ("static",      staticKeyword)
  , ("string",      stringKeyword)
  , ("super",       superKeyword)
  , ("switch",      switchKeyword)
  , ("symbol",      symbolKeyword)
  , ("this",        thisKeyword)
  , ("throw",       throwKeyword)
  , ("true",        trueKeyword)
  , ("try",         tryKeyword)
  , ("type",        typeKeyword)
  , ("typeof",      typeOfKeyword)
  , ("undefined",   undefinedKeyword)
  , ("unique",      uniqueKeyword)
  , ("unknown",     unknownKeyword)
  , ("using",       usingKeyword)
  , ("var",         varKeyword)
  , ("void",        voidKeyword)
  , ("while",       whileKeyword)
  , ("with",        withKeyword)
  , ("yield",       yieldKeyword)
  , ("async",       asyncKeyword)
  , ("await",       awaitKeyword)
  , ("of",          ofKeyword)
  ]

/-- Based on Go: internal/scanner/scanner.go:35-121 (textToKeyword) -/
def lookupKeyword (text : String) : Option Kind :=
  textToKeyword[text]?

open Kind in
/-- Based on Go: internal/scanner/scanner.go:123-189 (textToToken)
    Includes all keywords plus operator/punctuation tokens.
    Uses Std.HashMap for O(1) lookup. -/
def textToToken : HashMap String Kind :=
  textToKeyword |>.insertMany
  [ ("{",    openBraceToken)
  , ("}",    closeBraceToken)
  , ("(",    openParenToken)
  , (")",    closeParenToken)
  , ("[",    openBracketToken)
  , ("]",    closeBracketToken)
  , (".",    dotToken)
  , ("...",  dotDotDotToken)
  , (";",    semicolonToken)
  , (",",    commaToken)
  , ("<",    lessThanToken)
  , (">",    greaterThanToken)
  , ("<=",   lessThanEqualsToken)
  , (">=",   greaterThanEqualsToken)
  , ("==",   equalsEqualsToken)
  , ("!=",   exclamationEqualsToken)
  , ("===",  equalsEqualsEqualsToken)
  , ("!==",  exclamationEqualsEqualsToken)
  , ("=>",   equalsGreaterThanToken)
  , ("+",    plusToken)
  , ("-",    minusToken)
  , ("**",   asteriskAsteriskToken)
  , ("*",    asteriskToken)
  , ("/",    slashToken)
  , ("%",    percentToken)
  , ("++",   plusPlusToken)
  , ("--",   minusMinusToken)
  , ("<<",   lessThanLessThanToken)
  , ("</",   lessThanSlashToken)
  , (">>",   greaterThanGreaterThanToken)
  , (">>>",  greaterThanGreaterThanGreaterThanToken)
  , ("&",    ampersandToken)
  , ("|",    barToken)
  , ("^",    caretToken)
  , ("!",    exclamationToken)
  , ("~",    tildeToken)
  , ("&&",   ampersandAmpersandToken)
  , ("||",   barBarToken)
  , ("?",    questionToken)
  , ("??",   questionQuestionToken)
  , ("?.",   questionDotToken)
  , (":",    colonToken)
  , ("=",    equalsToken)
  , ("+=",   plusEqualsToken)
  , ("-=",   minusEqualsToken)
  , ("*=",   asteriskEqualsToken)
  , ("**=",  asteriskAsteriskEqualsToken)
  , ("/=",   slashEqualsToken)
  , ("%=",   percentEqualsToken)
  , ("<<=",  lessThanLessThanEqualsToken)
  , (">>=",  greaterThanGreaterThanEqualsToken)
  , (">>>=", greaterThanGreaterThanGreaterThanEqualsToken)
  , ("&=",   ampersandEqualsToken)
  , ("|=",   barEqualsToken)
  , ("^=",   caretEqualsToken)
  , ("||=",  barBarEqualsToken)
  , ("&&=",  ampersandAmpersandEqualsToken)
  , ("??=",  questionQuestionEqualsToken)
  , ("@",    atToken)
  , ("#",    hashToken)
  , ("`",    backtickToken)
  ]

/-- Based on Go: internal/scanner/scanner.go:123-189 (textToToken) -/
def lookupToken (text : String) : Option Kind :=
  textToToken[text]?

/-- Based on Go: internal/scanner/scanner.go (GetIdentifierToken)
    Look up a token value in the keyword map; default to identifier. -/
def getIdentifierToken (text : String) : Kind :=
  match textToKeyword[text]? with
  | some k => k
  | none => Kind.identifier

end TSLean.Compiler
