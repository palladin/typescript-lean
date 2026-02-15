/-
  TSLean.Compiler.Ast.Kind — Token and node kind enumeration.

  Based on Go: internal/ast/kind.go (lines 6-429)
  Go type: ast.Kind (int16) with 393 iota-enumerated values.
  We use a UInt16 wrapper for efficiency and to match Go's representation.
-/

namespace TSLean.Compiler

/-- Based on Go: internal/ast/kind.go:6 (Kind) -/
structure Kind where
  val : UInt16
  deriving BEq, Repr, Hashable, Inhabited

instance : Ord Kind where
  compare a b := compare a.val b.val

instance : LT Kind where
  lt a b := a.val < b.val

instance : LE Kind where
  le a b := a.val <= b.val

instance : DecidableEq Kind := fun a b =>
  if h : a.val = b.val then isTrue (by cases a; cases b; simp_all)
  else isFalse (by intro h'; cases h'; exact h rfl)

namespace Kind

-- Based on Go: internal/ast/kind.go:9-391
-- Each constant corresponds to a Go iota value.

/-- Go: kind.go:9 -/ def «unknown» : Kind := ⟨0⟩
/-- Go: kind.go:10 -/ def endOfFile : Kind := ⟨1⟩
/-- Go: kind.go:11 -/ def singleLineCommentTrivia : Kind := ⟨2⟩
/-- Go: kind.go:12 -/ def multiLineCommentTrivia : Kind := ⟨3⟩
/-- Go: kind.go:13 -/ def newLineTrivia : Kind := ⟨4⟩
/-- Go: kind.go:14 -/ def whitespaceTrivia : Kind := ⟨5⟩
/-- Go: kind.go:15 -/ def conflictMarkerTrivia : Kind := ⟨6⟩
/-- Go: kind.go:16 -/ def nonTextFileMarkerTrivia : Kind := ⟨7⟩
/-- Go: kind.go:17 -/ def numericLiteral : Kind := ⟨8⟩
/-- Go: kind.go:18 -/ def bigIntLiteral : Kind := ⟨9⟩
/-- Go: kind.go:19 -/ def stringLiteral : Kind := ⟨10⟩
/-- Go: kind.go:20 -/ def jsxText : Kind := ⟨11⟩
/-- Go: kind.go:21 -/ def jsxTextAllWhiteSpaces : Kind := ⟨12⟩
/-- Go: kind.go:22 -/ def regularExpressionLiteral : Kind := ⟨13⟩
/-- Go: kind.go:23 -/ def noSubstitutionTemplateLiteral : Kind := ⟨14⟩
-- Pseudo-literals
/-- Go: kind.go:25 -/ def templateHead : Kind := ⟨15⟩
/-- Go: kind.go:26 -/ def templateMiddle : Kind := ⟨16⟩
/-- Go: kind.go:27 -/ def templateTail : Kind := ⟨17⟩
-- Punctuation
/-- Go: kind.go:29 -/ def openBraceToken : Kind := ⟨18⟩
/-- Go: kind.go:30 -/ def closeBraceToken : Kind := ⟨19⟩
/-- Go: kind.go:31 -/ def openParenToken : Kind := ⟨20⟩
/-- Go: kind.go:32 -/ def closeParenToken : Kind := ⟨21⟩
/-- Go: kind.go:33 -/ def openBracketToken : Kind := ⟨22⟩
/-- Go: kind.go:34 -/ def closeBracketToken : Kind := ⟨23⟩
/-- Go: kind.go:35 -/ def dotToken : Kind := ⟨24⟩
/-- Go: kind.go:36 -/ def dotDotDotToken : Kind := ⟨25⟩
/-- Go: kind.go:37 -/ def semicolonToken : Kind := ⟨26⟩
/-- Go: kind.go:38 -/ def commaToken : Kind := ⟨27⟩
/-- Go: kind.go:39 -/ def questionDotToken : Kind := ⟨28⟩
/-- Go: kind.go:40 -/ def lessThanToken : Kind := ⟨29⟩
/-- Go: kind.go:41 -/ def lessThanSlashToken : Kind := ⟨30⟩
/-- Go: kind.go:42 -/ def greaterThanToken : Kind := ⟨31⟩
/-- Go: kind.go:43 -/ def lessThanEqualsToken : Kind := ⟨32⟩
/-- Go: kind.go:44 -/ def greaterThanEqualsToken : Kind := ⟨33⟩
/-- Go: kind.go:45 -/ def equalsEqualsToken : Kind := ⟨34⟩
/-- Go: kind.go:46 -/ def exclamationEqualsToken : Kind := ⟨35⟩
/-- Go: kind.go:47 -/ def equalsEqualsEqualsToken : Kind := ⟨36⟩
/-- Go: kind.go:48 -/ def exclamationEqualsEqualsToken : Kind := ⟨37⟩
/-- Go: kind.go:49 -/ def equalsGreaterThanToken : Kind := ⟨38⟩
/-- Go: kind.go:50 -/ def plusToken : Kind := ⟨39⟩
/-- Go: kind.go:51 -/ def minusToken : Kind := ⟨40⟩
/-- Go: kind.go:52 -/ def asteriskToken : Kind := ⟨41⟩
/-- Go: kind.go:53 -/ def asteriskAsteriskToken : Kind := ⟨42⟩
/-- Go: kind.go:54 -/ def slashToken : Kind := ⟨43⟩
/-- Go: kind.go:55 -/ def percentToken : Kind := ⟨44⟩
/-- Go: kind.go:56 -/ def plusPlusToken : Kind := ⟨45⟩
/-- Go: kind.go:57 -/ def minusMinusToken : Kind := ⟨46⟩
/-- Go: kind.go:58 -/ def lessThanLessThanToken : Kind := ⟨47⟩
/-- Go: kind.go:59 -/ def greaterThanGreaterThanToken : Kind := ⟨48⟩
/-- Go: kind.go:60 -/ def greaterThanGreaterThanGreaterThanToken : Kind := ⟨49⟩
/-- Go: kind.go:61 -/ def ampersandToken : Kind := ⟨50⟩
/-- Go: kind.go:62 -/ def barToken : Kind := ⟨51⟩
/-- Go: kind.go:63 -/ def caretToken : Kind := ⟨52⟩
/-- Go: kind.go:64 -/ def exclamationToken : Kind := ⟨53⟩
/-- Go: kind.go:65 -/ def tildeToken : Kind := ⟨54⟩
/-- Go: kind.go:66 -/ def ampersandAmpersandToken : Kind := ⟨55⟩
/-- Go: kind.go:67 -/ def barBarToken : Kind := ⟨56⟩
/-- Go: kind.go:68 -/ def questionToken : Kind := ⟨57⟩
/-- Go: kind.go:69 -/ def colonToken : Kind := ⟨58⟩
/-- Go: kind.go:70 -/ def atToken : Kind := ⟨59⟩
/-- Go: kind.go:71 -/ def questionQuestionToken : Kind := ⟨60⟩
/-- Go: kind.go:73 -/ def backtickToken : Kind := ⟨61⟩
/-- Go: kind.go:75 -/ def hashToken : Kind := ⟨62⟩
-- Assignments
/-- Go: kind.go:77 -/ def equalsToken : Kind := ⟨63⟩
/-- Go: kind.go:78 -/ def plusEqualsToken : Kind := ⟨64⟩
/-- Go: kind.go:79 -/ def minusEqualsToken : Kind := ⟨65⟩
/-- Go: kind.go:80 -/ def asteriskEqualsToken : Kind := ⟨66⟩
/-- Go: kind.go:81 -/ def asteriskAsteriskEqualsToken : Kind := ⟨67⟩
/-- Go: kind.go:82 -/ def slashEqualsToken : Kind := ⟨68⟩
/-- Go: kind.go:83 -/ def percentEqualsToken : Kind := ⟨69⟩
/-- Go: kind.go:84 -/ def lessThanLessThanEqualsToken : Kind := ⟨70⟩
/-- Go: kind.go:85 -/ def greaterThanGreaterThanEqualsToken : Kind := ⟨71⟩
/-- Go: kind.go:86 -/ def greaterThanGreaterThanGreaterThanEqualsToken : Kind := ⟨72⟩
/-- Go: kind.go:87 -/ def ampersandEqualsToken : Kind := ⟨73⟩
/-- Go: kind.go:88 -/ def barEqualsToken : Kind := ⟨74⟩
/-- Go: kind.go:89 -/ def barBarEqualsToken : Kind := ⟨75⟩
/-- Go: kind.go:90 -/ def ampersandAmpersandEqualsToken : Kind := ⟨76⟩
/-- Go: kind.go:91 -/ def questionQuestionEqualsToken : Kind := ⟨77⟩
/-- Go: kind.go:92 -/ def caretEqualsToken : Kind := ⟨78⟩
-- Identifiers and PrivateIdentifier
/-- Go: kind.go:94 -/ def identifier : Kind := ⟨79⟩
/-- Go: kind.go:95 -/ def privateIdentifier : Kind := ⟨80⟩
/-- Go: kind.go:96 -/ def jsDocCommentTextToken : Kind := ⟨81⟩
-- Reserved words
/-- Go: kind.go:98 -/ def breakKeyword : Kind := ⟨82⟩
/-- Go: kind.go:99 -/ def caseKeyword : Kind := ⟨83⟩
/-- Go: kind.go:100 -/ def catchKeyword : Kind := ⟨84⟩
/-- Go: kind.go:101 -/ def classKeyword : Kind := ⟨85⟩
/-- Go: kind.go:102 -/ def constKeyword : Kind := ⟨86⟩
/-- Go: kind.go:103 -/ def continueKeyword : Kind := ⟨87⟩
/-- Go: kind.go:104 -/ def debuggerKeyword : Kind := ⟨88⟩
/-- Go: kind.go:105 -/ def defaultKeyword : Kind := ⟨89⟩
/-- Go: kind.go:106 -/ def deleteKeyword : Kind := ⟨90⟩
/-- Go: kind.go:107 -/ def doKeyword : Kind := ⟨91⟩
/-- Go: kind.go:108 -/ def elseKeyword : Kind := ⟨92⟩
/-- Go: kind.go:109 -/ def enumKeyword : Kind := ⟨93⟩
/-- Go: kind.go:110 -/ def exportKeyword : Kind := ⟨94⟩
/-- Go: kind.go:111 -/ def extendsKeyword : Kind := ⟨95⟩
/-- Go: kind.go:112 -/ def falseKeyword : Kind := ⟨96⟩
/-- Go: kind.go:113 -/ def finallyKeyword : Kind := ⟨97⟩
/-- Go: kind.go:114 -/ def forKeyword : Kind := ⟨98⟩
/-- Go: kind.go:115 -/ def functionKeyword : Kind := ⟨99⟩
/-- Go: kind.go:116 -/ def ifKeyword : Kind := ⟨100⟩
/-- Go: kind.go:117 -/ def importKeyword : Kind := ⟨101⟩
/-- Go: kind.go:118 -/ def inKeyword : Kind := ⟨102⟩
/-- Go: kind.go:119 -/ def instanceOfKeyword : Kind := ⟨103⟩
/-- Go: kind.go:120 -/ def newKeyword : Kind := ⟨104⟩
/-- Go: kind.go:121 -/ def nullKeyword : Kind := ⟨105⟩
/-- Go: kind.go:122 -/ def returnKeyword : Kind := ⟨106⟩
/-- Go: kind.go:123 -/ def superKeyword : Kind := ⟨107⟩
/-- Go: kind.go:124 -/ def switchKeyword : Kind := ⟨108⟩
/-- Go: kind.go:125 -/ def thisKeyword : Kind := ⟨109⟩
/-- Go: kind.go:126 -/ def throwKeyword : Kind := ⟨110⟩
/-- Go: kind.go:127 -/ def trueKeyword : Kind := ⟨111⟩
/-- Go: kind.go:128 -/ def tryKeyword : Kind := ⟨112⟩
/-- Go: kind.go:129 -/ def typeOfKeyword : Kind := ⟨113⟩
/-- Go: kind.go:130 -/ def varKeyword : Kind := ⟨114⟩
/-- Go: kind.go:131 -/ def voidKeyword : Kind := ⟨115⟩
/-- Go: kind.go:132 -/ def whileKeyword : Kind := ⟨116⟩
/-- Go: kind.go:133 -/ def withKeyword : Kind := ⟨117⟩
-- Strict mode reserved words
/-- Go: kind.go:135 -/ def implementsKeyword : Kind := ⟨118⟩
/-- Go: kind.go:136 -/ def interfaceKeyword : Kind := ⟨119⟩
/-- Go: kind.go:137 -/ def letKeyword : Kind := ⟨120⟩
/-- Go: kind.go:138 -/ def packageKeyword : Kind := ⟨121⟩
/-- Go: kind.go:139 -/ def privateKeyword : Kind := ⟨122⟩
/-- Go: kind.go:140 -/ def protectedKeyword : Kind := ⟨123⟩
/-- Go: kind.go:141 -/ def publicKeyword : Kind := ⟨124⟩
/-- Go: kind.go:142 -/ def staticKeyword : Kind := ⟨125⟩
/-- Go: kind.go:143 -/ def yieldKeyword : Kind := ⟨126⟩
-- Contextual keywords
/-- Go: kind.go:145 -/ def abstractKeyword : Kind := ⟨127⟩
/-- Go: kind.go:146 -/ def accessorKeyword : Kind := ⟨128⟩
/-- Go: kind.go:147 -/ def asKeyword : Kind := ⟨129⟩
/-- Go: kind.go:148 -/ def assertsKeyword : Kind := ⟨130⟩
/-- Go: kind.go:149 -/ def assertKeyword : Kind := ⟨131⟩
/-- Go: kind.go:150 -/ def anyKeyword : Kind := ⟨132⟩
/-- Go: kind.go:151 -/ def asyncKeyword : Kind := ⟨133⟩
/-- Go: kind.go:152 -/ def awaitKeyword : Kind := ⟨134⟩
/-- Go: kind.go:153 -/ def booleanKeyword : Kind := ⟨135⟩
/-- Go: kind.go:154 -/ def constructorKeyword : Kind := ⟨136⟩
/-- Go: kind.go:155 -/ def declareKeyword : Kind := ⟨137⟩
/-- Go: kind.go:156 -/ def getKeyword : Kind := ⟨138⟩
/-- Go: kind.go:157 -/ def immediateKeyword : Kind := ⟨139⟩
/-- Go: kind.go:158 -/ def inferKeyword : Kind := ⟨140⟩
/-- Go: kind.go:159 -/ def intrinsicKeyword : Kind := ⟨141⟩
/-- Go: kind.go:160 -/ def isKeyword : Kind := ⟨142⟩
/-- Go: kind.go:161 -/ def keyOfKeyword : Kind := ⟨143⟩
/-- Go: kind.go:162 -/ def moduleKeyword : Kind := ⟨144⟩
/-- Go: kind.go:163 -/ def namespaceKeyword : Kind := ⟨145⟩
/-- Go: kind.go:164 -/ def neverKeyword : Kind := ⟨146⟩
/-- Go: kind.go:165 -/ def outKeyword : Kind := ⟨147⟩
/-- Go: kind.go:166 -/ def readonlyKeyword : Kind := ⟨148⟩
/-- Go: kind.go:167 -/ def requireKeyword : Kind := ⟨149⟩
/-- Go: kind.go:168 -/ def numberKeyword : Kind := ⟨150⟩
/-- Go: kind.go:169 -/ def objectKeyword : Kind := ⟨151⟩
/-- Go: kind.go:170 -/ def satisfiesKeyword : Kind := ⟨152⟩
/-- Go: kind.go:171 -/ def setKeyword : Kind := ⟨153⟩
/-- Go: kind.go:172 -/ def stringKeyword : Kind := ⟨154⟩
/-- Go: kind.go:173 -/ def symbolKeyword : Kind := ⟨155⟩
/-- Go: kind.go:174 -/ def typeKeyword : Kind := ⟨156⟩
/-- Go: kind.go:175 -/ def undefinedKeyword : Kind := ⟨157⟩
/-- Go: kind.go:176 -/ def uniqueKeyword : Kind := ⟨158⟩
/-- Go: kind.go:177 -/ def unknownKeyword : Kind := ⟨159⟩
/-- Go: kind.go:178 -/ def usingKeyword : Kind := ⟨160⟩
/-- Go: kind.go:179 -/ def fromKeyword : Kind := ⟨161⟩
/-- Go: kind.go:180 -/ def globalKeyword : Kind := ⟨162⟩
/-- Go: kind.go:181 -/ def bigIntKeyword : Kind := ⟨163⟩
/-- Go: kind.go:182 -/ def overrideKeyword : Kind := ⟨164⟩
/-- Go: kind.go:183 -/ def ofKeyword : Kind := ⟨165⟩
/-- Go: kind.go:184 -/ def deferKeyword : Kind := ⟨166⟩
-- Parse tree nodes
/-- Go: kind.go:187 -/ def qualifiedName : Kind := ⟨167⟩
/-- Go: kind.go:188 -/ def computedPropertyName : Kind := ⟨168⟩
-- Signature elements
/-- Go: kind.go:190 -/ def typeParameter : Kind := ⟨169⟩
/-- Go: kind.go:191 -/ def parameter : Kind := ⟨170⟩
/-- Go: kind.go:192 -/ def decorator : Kind := ⟨171⟩
-- TypeMember
/-- Go: kind.go:194 -/ def propertySignature : Kind := ⟨172⟩
/-- Go: kind.go:195 -/ def propertyDeclaration : Kind := ⟨173⟩
/-- Go: kind.go:196 -/ def methodSignature : Kind := ⟨174⟩
/-- Go: kind.go:197 -/ def methodDeclaration : Kind := ⟨175⟩
/-- Go: kind.go:198 -/ def classStaticBlockDeclaration : Kind := ⟨176⟩
/-- Go: kind.go:199 -/ def constructor : Kind := ⟨177⟩
/-- Go: kind.go:200 -/ def getAccessor : Kind := ⟨178⟩
/-- Go: kind.go:201 -/ def setAccessor : Kind := ⟨179⟩
/-- Go: kind.go:202 -/ def callSignature : Kind := ⟨180⟩
/-- Go: kind.go:203 -/ def constructSignature : Kind := ⟨181⟩
/-- Go: kind.go:204 -/ def indexSignature : Kind := ⟨182⟩
-- Type
/-- Go: kind.go:206 -/ def typePredicate : Kind := ⟨183⟩
/-- Go: kind.go:207 -/ def typeReference : Kind := ⟨184⟩
/-- Go: kind.go:208 -/ def functionType : Kind := ⟨185⟩
/-- Go: kind.go:209 -/ def constructorType : Kind := ⟨186⟩
/-- Go: kind.go:210 -/ def typeQuery : Kind := ⟨187⟩
/-- Go: kind.go:211 -/ def typeLiteral : Kind := ⟨188⟩
/-- Go: kind.go:212 -/ def arrayType : Kind := ⟨189⟩
/-- Go: kind.go:213 -/ def tupleType : Kind := ⟨190⟩
/-- Go: kind.go:214 -/ def optionalType : Kind := ⟨191⟩
/-- Go: kind.go:215 -/ def restType : Kind := ⟨192⟩
/-- Go: kind.go:216 -/ def unionType : Kind := ⟨193⟩
/-- Go: kind.go:217 -/ def intersectionType : Kind := ⟨194⟩
/-- Go: kind.go:218 -/ def conditionalType : Kind := ⟨195⟩
/-- Go: kind.go:219 -/ def inferType : Kind := ⟨196⟩
/-- Go: kind.go:220 -/ def parenthesizedType : Kind := ⟨197⟩
/-- Go: kind.go:221 -/ def thisType : Kind := ⟨198⟩
/-- Go: kind.go:222 -/ def typeOperator : Kind := ⟨199⟩
/-- Go: kind.go:223 -/ def indexedAccessType : Kind := ⟨200⟩
/-- Go: kind.go:224 -/ def mappedType : Kind := ⟨201⟩
/-- Go: kind.go:225 -/ def literalType : Kind := ⟨202⟩
/-- Go: kind.go:226 -/ def namedTupleMember : Kind := ⟨203⟩
/-- Go: kind.go:227 -/ def templateLiteralType : Kind := ⟨204⟩
/-- Go: kind.go:228 -/ def templateLiteralTypeSpan : Kind := ⟨205⟩
/-- Go: kind.go:229 -/ def importType : Kind := ⟨206⟩
-- Binding patterns
/-- Go: kind.go:231 -/ def objectBindingPattern : Kind := ⟨207⟩
/-- Go: kind.go:232 -/ def arrayBindingPattern : Kind := ⟨208⟩
/-- Go: kind.go:233 -/ def bindingElement : Kind := ⟨209⟩
-- Expression
/-- Go: kind.go:235 -/ def arrayLiteralExpression : Kind := ⟨210⟩
/-- Go: kind.go:236 -/ def objectLiteralExpression : Kind := ⟨211⟩
/-- Go: kind.go:237 -/ def propertyAccessExpression : Kind := ⟨212⟩
/-- Go: kind.go:238 -/ def elementAccessExpression : Kind := ⟨213⟩
/-- Go: kind.go:239 -/ def callExpression : Kind := ⟨214⟩
/-- Go: kind.go:240 -/ def newExpression : Kind := ⟨215⟩
/-- Go: kind.go:241 -/ def taggedTemplateExpression : Kind := ⟨216⟩
/-- Go: kind.go:242 -/ def typeAssertionExpression : Kind := ⟨217⟩
/-- Go: kind.go:243 -/ def parenthesizedExpression : Kind := ⟨218⟩
/-- Go: kind.go:244 -/ def functionExpression : Kind := ⟨219⟩
/-- Go: kind.go:245 -/ def arrowFunction : Kind := ⟨220⟩
/-- Go: kind.go:246 -/ def deleteExpression : Kind := ⟨221⟩
/-- Go: kind.go:247 -/ def typeOfExpression : Kind := ⟨222⟩
/-- Go: kind.go:248 -/ def voidExpression : Kind := ⟨223⟩
/-- Go: kind.go:249 -/ def awaitExpression : Kind := ⟨224⟩
/-- Go: kind.go:250 -/ def prefixUnaryExpression : Kind := ⟨225⟩
/-- Go: kind.go:251 -/ def postfixUnaryExpression : Kind := ⟨226⟩
/-- Go: kind.go:252 -/ def binaryExpression : Kind := ⟨227⟩
/-- Go: kind.go:253 -/ def conditionalExpression : Kind := ⟨228⟩
/-- Go: kind.go:254 -/ def templateExpression : Kind := ⟨229⟩
/-- Go: kind.go:255 -/ def yieldExpression : Kind := ⟨230⟩
/-- Go: kind.go:256 -/ def spreadElement : Kind := ⟨231⟩
/-- Go: kind.go:257 -/ def classExpression : Kind := ⟨232⟩
/-- Go: kind.go:258 -/ def omittedExpression : Kind := ⟨233⟩
/-- Go: kind.go:259 -/ def expressionWithTypeArguments : Kind := ⟨234⟩
/-- Go: kind.go:260 -/ def asExpression : Kind := ⟨235⟩
/-- Go: kind.go:261 -/ def nonNullExpression : Kind := ⟨236⟩
/-- Go: kind.go:262 -/ def metaProperty : Kind := ⟨237⟩
/-- Go: kind.go:263 -/ def syntheticExpression : Kind := ⟨238⟩
/-- Go: kind.go:264 -/ def satisfiesExpression : Kind := ⟨239⟩
-- Misc
/-- Go: kind.go:266 -/ def templateSpan : Kind := ⟨240⟩
/-- Go: kind.go:267 -/ def semicolonClassElement : Kind := ⟨241⟩
-- Element
/-- Go: kind.go:269 -/ def block : Kind := ⟨242⟩
/-- Go: kind.go:270 -/ def emptyStatement : Kind := ⟨243⟩
/-- Go: kind.go:271 -/ def variableStatement : Kind := ⟨244⟩
/-- Go: kind.go:272 -/ def expressionStatement : Kind := ⟨245⟩
/-- Go: kind.go:273 -/ def ifStatement : Kind := ⟨246⟩
/-- Go: kind.go:274 -/ def doStatement : Kind := ⟨247⟩
/-- Go: kind.go:275 -/ def whileStatement : Kind := ⟨248⟩
/-- Go: kind.go:276 -/ def forStatement : Kind := ⟨249⟩
/-- Go: kind.go:277 -/ def forInStatement : Kind := ⟨250⟩
/-- Go: kind.go:278 -/ def forOfStatement : Kind := ⟨251⟩
/-- Go: kind.go:279 -/ def continueStatement : Kind := ⟨252⟩
/-- Go: kind.go:280 -/ def breakStatement : Kind := ⟨253⟩
/-- Go: kind.go:281 -/ def returnStatement : Kind := ⟨254⟩
/-- Go: kind.go:282 -/ def withStatement : Kind := ⟨255⟩
/-- Go: kind.go:283 -/ def switchStatement : Kind := ⟨256⟩
/-- Go: kind.go:284 -/ def labeledStatement : Kind := ⟨257⟩
/-- Go: kind.go:285 -/ def throwStatement : Kind := ⟨258⟩
/-- Go: kind.go:286 -/ def tryStatement : Kind := ⟨259⟩
/-- Go: kind.go:287 -/ def debuggerStatement : Kind := ⟨260⟩
/-- Go: kind.go:288 -/ def variableDeclaration : Kind := ⟨261⟩
/-- Go: kind.go:289 -/ def variableDeclarationList : Kind := ⟨262⟩
/-- Go: kind.go:290 -/ def functionDeclaration : Kind := ⟨263⟩
/-- Go: kind.go:291 -/ def classDeclaration : Kind := ⟨264⟩
/-- Go: kind.go:292 -/ def interfaceDeclaration : Kind := ⟨265⟩
/-- Go: kind.go:293 -/ def typeAliasDeclaration : Kind := ⟨266⟩
/-- Go: kind.go:294 -/ def enumDeclaration : Kind := ⟨267⟩
/-- Go: kind.go:295 -/ def moduleDeclaration : Kind := ⟨268⟩
/-- Go: kind.go:296 -/ def moduleBlock : Kind := ⟨269⟩
/-- Go: kind.go:297 -/ def caseBlock : Kind := ⟨270⟩
/-- Go: kind.go:298 -/ def namespaceExportDeclaration : Kind := ⟨271⟩
/-- Go: kind.go:299 -/ def importEqualsDeclaration : Kind := ⟨272⟩
/-- Go: kind.go:300 -/ def importDeclaration : Kind := ⟨273⟩
/-- Go: kind.go:301 -/ def importClause : Kind := ⟨274⟩
/-- Go: kind.go:302 -/ def namespaceImport : Kind := ⟨275⟩
/-- Go: kind.go:303 -/ def namedImports : Kind := ⟨276⟩
/-- Go: kind.go:304 -/ def importSpecifier : Kind := ⟨277⟩
/-- Go: kind.go:305 -/ def exportAssignment : Kind := ⟨278⟩
/-- Go: kind.go:306 -/ def exportDeclaration : Kind := ⟨279⟩
/-- Go: kind.go:307 -/ def namedExports : Kind := ⟨280⟩
/-- Go: kind.go:308 -/ def namespaceExport : Kind := ⟨281⟩
/-- Go: kind.go:309 -/ def exportSpecifier : Kind := ⟨282⟩
/-- Go: kind.go:310 -/ def missingDeclaration : Kind := ⟨283⟩
-- Module references
/-- Go: kind.go:312 -/ def externalModuleReference : Kind := ⟨284⟩
-- JSX
/-- Go: kind.go:314 -/ def jsxElement : Kind := ⟨285⟩
/-- Go: kind.go:315 -/ def jsxSelfClosingElement : Kind := ⟨286⟩
/-- Go: kind.go:316 -/ def jsxOpeningElement : Kind := ⟨287⟩
/-- Go: kind.go:317 -/ def jsxClosingElement : Kind := ⟨288⟩
/-- Go: kind.go:318 -/ def jsxFragment : Kind := ⟨289⟩
/-- Go: kind.go:319 -/ def jsxOpeningFragment : Kind := ⟨290⟩
/-- Go: kind.go:320 -/ def jsxClosingFragment : Kind := ⟨291⟩
/-- Go: kind.go:321 -/ def jsxAttribute : Kind := ⟨292⟩
/-- Go: kind.go:322 -/ def jsxAttributes : Kind := ⟨293⟩
/-- Go: kind.go:323 -/ def jsxSpreadAttribute : Kind := ⟨294⟩
/-- Go: kind.go:324 -/ def jsxExpression : Kind := ⟨295⟩
/-- Go: kind.go:325 -/ def jsxNamespacedName : Kind := ⟨296⟩
-- Clauses
/-- Go: kind.go:327 -/ def caseClause : Kind := ⟨297⟩
/-- Go: kind.go:328 -/ def defaultClause : Kind := ⟨298⟩
/-- Go: kind.go:329 -/ def heritageClause : Kind := ⟨299⟩
/-- Go: kind.go:330 -/ def catchClause : Kind := ⟨300⟩
-- Import attributes
/-- Go: kind.go:332 -/ def importAttributes : Kind := ⟨301⟩
/-- Go: kind.go:333 -/ def importAttribute : Kind := ⟨302⟩
-- Property assignments
/-- Go: kind.go:335 -/ def propertyAssignment : Kind := ⟨303⟩
/-- Go: kind.go:336 -/ def shorthandPropertyAssignment : Kind := ⟨304⟩
/-- Go: kind.go:337 -/ def spreadAssignment : Kind := ⟨305⟩
-- Enum
/-- Go: kind.go:339 -/ def enumMember : Kind := ⟨306⟩
-- Top-level nodes
/-- Go: kind.go:341 -/ def sourceFile : Kind := ⟨307⟩
-- JSDoc nodes
/-- Go: kind.go:343 -/ def jsDocTypeExpression : Kind := ⟨308⟩
/-- Go: kind.go:344 -/ def jsDocNameReference : Kind := ⟨309⟩
/-- Go: kind.go:345 -/ def jsDocMemberName : Kind := ⟨310⟩
/-- Go: kind.go:346 -/ def jsDocAllType : Kind := ⟨311⟩
/-- Go: kind.go:347 -/ def jsDocNullableType : Kind := ⟨312⟩
/-- Go: kind.go:348 -/ def jsDocNonNullableType : Kind := ⟨313⟩
/-- Go: kind.go:349 -/ def jsDocOptionalType : Kind := ⟨314⟩
/-- Go: kind.go:350 -/ def jsDocVariadicType : Kind := ⟨315⟩
/-- Go: kind.go:351 -/ def jsDoc : Kind := ⟨316⟩
/-- Go: kind.go:352 -/ def jsDocText : Kind := ⟨317⟩
/-- Go: kind.go:353 -/ def jsDocTypeLiteral : Kind := ⟨318⟩
/-- Go: kind.go:354 -/ def jsDocSignature : Kind := ⟨319⟩
/-- Go: kind.go:355 -/ def jsDocLink : Kind := ⟨320⟩
/-- Go: kind.go:356 -/ def jsDocLinkCode : Kind := ⟨321⟩
/-- Go: kind.go:357 -/ def jsDocLinkPlain : Kind := ⟨322⟩
/-- Go: kind.go:358 -/ def jsDocTag : Kind := ⟨323⟩
/-- Go: kind.go:359 -/ def jsDocAugmentsTag : Kind := ⟨324⟩
/-- Go: kind.go:360 -/ def jsDocImplementsTag : Kind := ⟨325⟩
/-- Go: kind.go:361 -/ def jsDocDeprecatedTag : Kind := ⟨326⟩
/-- Go: kind.go:362 -/ def jsDocPublicTag : Kind := ⟨327⟩
/-- Go: kind.go:363 -/ def jsDocPrivateTag : Kind := ⟨328⟩
/-- Go: kind.go:364 -/ def jsDocProtectedTag : Kind := ⟨329⟩
/-- Go: kind.go:365 -/ def jsDocReadonlyTag : Kind := ⟨330⟩
/-- Go: kind.go:366 -/ def jsDocOverrideTag : Kind := ⟨331⟩
/-- Go: kind.go:367 -/ def jsDocCallbackTag : Kind := ⟨332⟩
/-- Go: kind.go:368 -/ def jsDocOverloadTag : Kind := ⟨333⟩
/-- Go: kind.go:369 -/ def jsDocParameterTag : Kind := ⟨334⟩
/-- Go: kind.go:370 -/ def jsDocReturnTag : Kind := ⟨335⟩
/-- Go: kind.go:371 -/ def jsDocThisTag : Kind := ⟨336⟩
/-- Go: kind.go:372 -/ def jsDocTypeTag : Kind := ⟨337⟩
/-- Go: kind.go:373 -/ def jsDocTemplateTag : Kind := ⟨338⟩
/-- Go: kind.go:374 -/ def jsDocTypedefTag : Kind := ⟨339⟩
/-- Go: kind.go:375 -/ def jsDocSeeTag : Kind := ⟨340⟩
/-- Go: kind.go:376 -/ def jsDocPropertyTag : Kind := ⟨341⟩
/-- Go: kind.go:377 -/ def jsDocSatisfiesTag : Kind := ⟨342⟩
/-- Go: kind.go:378 -/ def jsDocImportTag : Kind := ⟨343⟩
-- Synthesized list
/-- Go: kind.go:380 -/ def syntaxList : Kind := ⟨344⟩
-- Reparsed JS nodes
/-- Go: kind.go:382 -/ def jsTypeAliasDeclaration : Kind := ⟨345⟩
/-- Go: kind.go:383 -/ def jsExportAssignment : Kind := ⟨346⟩
/-- Go: kind.go:384 -/ def commonJSExport : Kind := ⟨347⟩
/-- Go: kind.go:385 -/ def jsImportDeclaration : Kind := ⟨348⟩
-- Transformation nodes
/-- Go: kind.go:387 -/ def notEmittedStatement : Kind := ⟨349⟩
/-- Go: kind.go:388 -/ def partiallyEmittedExpression : Kind := ⟨350⟩
/-- Go: kind.go:389 -/ def commaListExpression : Kind := ⟨351⟩
/-- Go: kind.go:390 -/ def syntheticReferenceExpression : Kind := ⟨352⟩
/-- Go: kind.go:391 -/ def notEmittedTypeElement : Kind := ⟨353⟩
-- Enum value count
/-- Go: kind.go:393 -/ def count : Kind := ⟨354⟩

-- Markers (Go: kind.go:395-429)
/-- Go: kind.go:395 -/ abbrev firstAssignment := equalsToken
/-- Go: kind.go:396 -/ abbrev lastAssignment := caretEqualsToken
/-- Go: kind.go:397 -/ abbrev firstCompoundAssignment := plusEqualsToken
/-- Go: kind.go:398 -/ abbrev lastCompoundAssignment := caretEqualsToken
/-- Go: kind.go:399 -/ abbrev firstReservedWord := breakKeyword
/-- Go: kind.go:400 -/ abbrev lastReservedWord := withKeyword
/-- Go: kind.go:401 -/ abbrev firstKeyword := breakKeyword
/-- Go: kind.go:402 -/ abbrev lastKeyword := deferKeyword
/-- Go: kind.go:403 -/ abbrev firstFutureReservedWord := implementsKeyword
/-- Go: kind.go:404 -/ abbrev lastFutureReservedWord := yieldKeyword
/-- Go: kind.go:405 -/ abbrev firstTypeNode := typePredicate
/-- Go: kind.go:406 -/ abbrev lastTypeNode := importType
/-- Go: kind.go:407 -/ abbrev firstPunctuation := openBraceToken
/-- Go: kind.go:408 -/ abbrev lastPunctuation := caretEqualsToken
/-- Go: kind.go:409 -/ abbrev firstToken := Kind.unknown
/-- Go: kind.go:410 -/ abbrev lastToken := lastKeyword
/-- Go: kind.go:411 -/ abbrev firstLiteralToken := numericLiteral
/-- Go: kind.go:412 -/ abbrev lastLiteralToken := noSubstitutionTemplateLiteral
/-- Go: kind.go:413 -/ abbrev firstTemplateToken := noSubstitutionTemplateLiteral
/-- Go: kind.go:414 -/ abbrev lastTemplateToken := templateTail
/-- Go: kind.go:415 -/ abbrev firstBinaryOperator := lessThanToken
/-- Go: kind.go:416 -/ abbrev lastBinaryOperator := caretEqualsToken
/-- Go: kind.go:417 -/ abbrev firstStatement := variableStatement
/-- Go: kind.go:418 -/ abbrev lastStatement := debuggerStatement
/-- Go: kind.go:419 -/ abbrev firstNode := qualifiedName
/-- Go: kind.go:420 -/ abbrev firstJSDocNode := jsDocTypeExpression
/-- Go: kind.go:421 -/ abbrev lastJSDocNode := jsDocImportTag
/-- Go: kind.go:422 -/ abbrev firstJSDocTagNode := jsDocTag
/-- Go: kind.go:423 -/ abbrev lastJSDocTagNode := jsDocImportTag
/-- Go: kind.go:424 -/ abbrev firstContextualKeyword := abstractKeyword
/-- Go: kind.go:425 -/ abbrev lastContextualKeyword := deferKeyword
/-- Go: kind.go:427 -/ abbrev firstTriviaToken := singleLineCommentTrivia
/-- Go: kind.go:428 -/ abbrev lastTriviaToken := conflictMarkerTrivia

-- Range-check helpers
def isKeywordKind (k : Kind) : Bool :=
  firstKeyword.val <= k.val && k.val <= lastKeyword.val

def isTokenKind (k : Kind) : Bool :=
  firstToken.val <= k.val && k.val <= lastToken.val

def isPunctuation (k : Kind) : Bool :=
  firstPunctuation.val <= k.val && k.val <= lastPunctuation.val

def isAssignment (k : Kind) : Bool :=
  firstAssignment.val <= k.val && k.val <= lastAssignment.val

def isReservedWord (k : Kind) : Bool :=
  firstReservedWord.val <= k.val && k.val <= lastReservedWord.val

def isContextualKeyword (k : Kind) : Bool :=
  firstContextualKeyword.val <= k.val && k.val <= lastContextualKeyword.val

def isLiteralToken (k : Kind) : Bool :=
  firstLiteralToken.val <= k.val && k.val <= lastLiteralToken.val

def isTemplateToken (k : Kind) : Bool :=
  firstTemplateToken.val <= k.val && k.val <= lastTemplateToken.val

def isTrivia (k : Kind) : Bool :=
  firstTriviaToken.val <= k.val && k.val <= lastTriviaToken.val

end Kind

end TSLean.Compiler
