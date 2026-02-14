-- TSLean.Ast.Flags: Bitflag types for AST nodes, symbols, modifiers, etc.
-- All flags use UInt32 with hex literal values to avoid Nat coercion issues.

namespace TSLean.Ast

/-! ## NodeFlags -/

structure NodeFlags where
  val : UInt32
  deriving BEq, Repr, Inhabited, Hashable

namespace NodeFlags
  instance : OrOp NodeFlags where or a b := ⟨a.val ||| b.val⟩
  instance : AndOp NodeFlags where and a b := ⟨a.val &&& b.val⟩
  def hasFlag (flags flag : NodeFlags) : Bool := (flags.val &&& flag.val) != 0

  def none               : NodeFlags := ⟨0⟩
  def let_               : NodeFlags := ⟨0x1⟩
  def const_             : NodeFlags := ⟨0x2⟩
  def using_             : NodeFlags := ⟨0x4⟩
  def nestedNamespace    : NodeFlags := ⟨0x8⟩
  def synthesized        : NodeFlags := ⟨0x10⟩
  def namespace_         : NodeFlags := ⟨0x20⟩
  def optionalChain      : NodeFlags := ⟨0x40⟩
  def exportContext       : NodeFlags := ⟨0x80⟩
  def containsThis       : NodeFlags := ⟨0x100⟩
  def hasImplicitReturn   : NodeFlags := ⟨0x200⟩
  def hasExplicitReturn   : NodeFlags := ⟨0x400⟩
  def globalAugmentation  : NodeFlags := ⟨0x800⟩
  def hasAsyncFunctions   : NodeFlags := ⟨0x1000⟩
  def disallowInContext   : NodeFlags := ⟨0x2000⟩
  def yieldContext         : NodeFlags := ⟨0x4000⟩
  def decoratorContext     : NodeFlags := ⟨0x8000⟩
  def awaitContext         : NodeFlags := ⟨0x10000⟩
  def disallowConditionalTypesContext : NodeFlags := ⟨0x20000⟩
  def thisNodeHasError     : NodeFlags := ⟨0x40000⟩
  def javascriptFile       : NodeFlags := ⟨0x80000⟩
  def thisNodeOrAnySubNodesHasError : NodeFlags := ⟨0x100000⟩
  def hasAggregatedChildData : NodeFlags := ⟨0x200000⟩
  def jsxNamespacedName    : NodeFlags := ⟨0x400000⟩

  def blockScoped : NodeFlags := let_ ||| const_ ||| using_
end NodeFlags

/-! ## ModifierFlags -/

structure ModifierFlags where
  val : UInt32
  deriving BEq, Repr, Inhabited, Hashable

namespace ModifierFlags
  instance : OrOp ModifierFlags where or a b := ⟨a.val ||| b.val⟩
  instance : AndOp ModifierFlags where and a b := ⟨a.val &&& b.val⟩
  def hasFlag (flags flag : ModifierFlags) : Bool := (flags.val &&& flag.val) != 0

  def none         : ModifierFlags := ⟨0⟩
  def public_      : ModifierFlags := ⟨0x1⟩
  def private_     : ModifierFlags := ⟨0x2⟩
  def protected_   : ModifierFlags := ⟨0x4⟩
  def readonly_    : ModifierFlags := ⟨0x8⟩
  def override_    : ModifierFlags := ⟨0x10⟩
  def export_      : ModifierFlags := ⟨0x20⟩
  def abstract_    : ModifierFlags := ⟨0x40⟩
  def ambient      : ModifierFlags := ⟨0x80⟩
  def static_      : ModifierFlags := ⟨0x100⟩
  def accessor     : ModifierFlags := ⟨0x200⟩
  def async_       : ModifierFlags := ⟨0x400⟩
  def default_     : ModifierFlags := ⟨0x800⟩
  def const_       : ModifierFlags := ⟨0x1000⟩
  def deprecated   : ModifierFlags := ⟨0x2000⟩
  def decorator    : ModifierFlags := ⟨0x4000⟩
  def in_          : ModifierFlags := ⟨0x8000⟩
  def out_         : ModifierFlags := ⟨0x10000⟩

  def accessibilityModifier : ModifierFlags := public_ ||| private_ ||| protected_
  def parameterPropertyModifier : ModifierFlags := accessibilityModifier ||| readonly_ ||| override_
  def nonPublicAccessibilityModifier : ModifierFlags := private_ ||| protected_
  def typeScriptModifier : ModifierFlags :=
    ambient ||| public_ ||| private_ ||| protected_ ||| readonly_ |||
    abstract_ ||| override_ ||| accessor ||| in_ ||| out_ ||| decorator
  def exportDefault : ModifierFlags := export_ ||| default_
  def all : ModifierFlags := ⟨0x1FFFF⟩
end ModifierFlags

/-! ## SymbolFlags -/

structure SymbolFlags where
  val : UInt32
  deriving BEq, Repr, Inhabited, Hashable

namespace SymbolFlags
  instance : OrOp SymbolFlags where or a b := ⟨a.val ||| b.val⟩
  instance : AndOp SymbolFlags where and a b := ⟨a.val &&& b.val⟩
  def hasFlag (flags flag : SymbolFlags) : Bool := (flags.val &&& flag.val) != 0

  def none                 : SymbolFlags := ⟨0⟩
  def functionScopedVariable : SymbolFlags := ⟨0x1⟩
  def blockScopedVariable : SymbolFlags := ⟨0x2⟩
  def property             : SymbolFlags := ⟨0x4⟩
  def enumMember           : SymbolFlags := ⟨0x8⟩
  def function_            : SymbolFlags := ⟨0x10⟩
  def class_               : SymbolFlags := ⟨0x20⟩
  def interface_           : SymbolFlags := ⟨0x40⟩
  def constEnum            : SymbolFlags := ⟨0x80⟩
  def regularEnum          : SymbolFlags := ⟨0x100⟩
  def valueModule          : SymbolFlags := ⟨0x200⟩
  def namespaceModule      : SymbolFlags := ⟨0x400⟩
  def typeLiteral          : SymbolFlags := ⟨0x800⟩
  def objectLiteral        : SymbolFlags := ⟨0x1000⟩
  def method               : SymbolFlags := ⟨0x2000⟩
  def constructor_         : SymbolFlags := ⟨0x4000⟩
  def getAccessor          : SymbolFlags := ⟨0x8000⟩
  def setAccessor          : SymbolFlags := ⟨0x10000⟩
  def signature            : SymbolFlags := ⟨0x20000⟩
  def typeParameter        : SymbolFlags := ⟨0x40000⟩
  def typeAlias            : SymbolFlags := ⟨0x80000⟩
  def exportValue          : SymbolFlags := ⟨0x100000⟩
  def alias                : SymbolFlags := ⟨0x200000⟩
  def prototype            : SymbolFlags := ⟨0x400000⟩
  def exportStar           : SymbolFlags := ⟨0x800000⟩
  def optional             : SymbolFlags := ⟨0x1000000⟩
  def transient            : SymbolFlags := ⟨0x2000000⟩
  def assignment           : SymbolFlags := ⟨0x4000000⟩
  def moduleExports        : SymbolFlags := ⟨0x8000000⟩

  def variable_ : SymbolFlags := functionScopedVariable ||| blockScopedVariable
  def value : SymbolFlags := variable_ ||| property ||| enumMember ||| objectLiteral |||
    function_ ||| class_ ||| regularEnum ||| valueModule ||| method ||| getAccessor |||
    setAccessor
  def type_ : SymbolFlags := class_ ||| interface_ ||| regularEnum ||| constEnum |||
    typeParameter ||| typeAlias ||| typeLiteral
  def namespace_ : SymbolFlags := valueModule ||| namespaceModule ||| regularEnum
  def accessor : SymbolFlags := getAccessor ||| setAccessor
  def enum_ : SymbolFlags := regularEnum ||| constEnum
  def module_ : SymbolFlags := valueModule ||| namespaceModule
end SymbolFlags

/-! ## TypeFlags -/

structure TypeFlags where
  val : UInt32
  deriving BEq, Repr, Inhabited, Hashable

namespace TypeFlags
  instance : OrOp TypeFlags where or a b := ⟨a.val ||| b.val⟩
  instance : AndOp TypeFlags where and a b := ⟨a.val &&& b.val⟩
  def hasFlag (flags flag : TypeFlags) : Bool := (flags.val &&& flag.val) != 0

  def none           : TypeFlags := ⟨0⟩
  def any            : TypeFlags := ⟨0x1⟩
  def unknown        : TypeFlags := ⟨0x2⟩
  def string_        : TypeFlags := ⟨0x4⟩
  def number_        : TypeFlags := ⟨0x8⟩
  def boolean_       : TypeFlags := ⟨0x10⟩
  def enum_          : TypeFlags := ⟨0x20⟩
  def bigInt         : TypeFlags := ⟨0x40⟩
  def stringLiteral  : TypeFlags := ⟨0x80⟩
  def numberLiteral  : TypeFlags := ⟨0x100⟩
  def booleanLiteral : TypeFlags := ⟨0x200⟩
  def enumLiteral    : TypeFlags := ⟨0x400⟩
  def bigIntLiteral  : TypeFlags := ⟨0x800⟩
  def esSymbol       : TypeFlags := ⟨0x1000⟩
  def uniqueSymbol   : TypeFlags := ⟨0x2000⟩
  def void_          : TypeFlags := ⟨0x4000⟩
  def undefined      : TypeFlags := ⟨0x8000⟩
  def null_          : TypeFlags := ⟨0x10000⟩
  def never          : TypeFlags := ⟨0x20000⟩
  def typeParameter  : TypeFlags := ⟨0x40000⟩
  def object_        : TypeFlags := ⟨0x80000⟩
  def union_         : TypeFlags := ⟨0x100000⟩
  def intersection   : TypeFlags := ⟨0x200000⟩
  def index          : TypeFlags := ⟨0x400000⟩
  def indexedAccess  : TypeFlags := ⟨0x800000⟩
  def conditional    : TypeFlags := ⟨0x1000000⟩
  def substitution   : TypeFlags := ⟨0x2000000⟩
  def nonPrimitive   : TypeFlags := ⟨0x4000000⟩
  def templateLiteral : TypeFlags := ⟨0x8000000⟩
  def stringMapping  : TypeFlags := ⟨0x10000000⟩

  def literal : TypeFlags := stringLiteral ||| numberLiteral ||| booleanLiteral |||
    bigIntLiteral
  def primitive : TypeFlags := string_ ||| number_ ||| boolean_ ||| bigInt ||| void_ |||
    undefined ||| null_ ||| esSymbol ||| uniqueSymbol ||| literal
  def unionOrIntersection : TypeFlags := union_ ||| intersection
  def structuredType : TypeFlags := object_ ||| union_ ||| intersection
  def narrowable : TypeFlags := ⟨0x1FFFFFFF⟩
end TypeFlags

/-! ## TokenFlags -/

structure TokenFlags where
  val : UInt32
  deriving BEq, Repr, Inhabited, Hashable

namespace TokenFlags
  instance : OrOp TokenFlags where or a b := ⟨a.val ||| b.val⟩
  instance : AndOp TokenFlags where and a b := ⟨a.val &&& b.val⟩
  def hasFlag (flags flag : TokenFlags) : Bool := (flags.val &&& flag.val) != 0

  def none                      : TokenFlags := ⟨0⟩
  def precedingLineBreak        : TokenFlags := ⟨0x1⟩
  def precedingJSDocComment     : TokenFlags := ⟨0x2⟩
  def unterminated              : TokenFlags := ⟨0x4⟩
  def extendedUnicodeEscape     : TokenFlags := ⟨0x8⟩
  def scientific                : TokenFlags := ⟨0x10⟩
  def octal                     : TokenFlags := ⟨0x20⟩
  def hexSpecifier              : TokenFlags := ⟨0x40⟩
  def binarySpecifier           : TokenFlags := ⟨0x80⟩
  def octalSpecifier            : TokenFlags := ⟨0x100⟩
  def containsSeparator         : TokenFlags := ⟨0x200⟩
  def binaryOrOctalSpecifier    : TokenFlags := binarySpecifier ||| octalSpecifier
  def numericLiteralFlags       : TokenFlags :=
    scientific ||| octal ||| hexSpecifier ||| binaryOrOctalSpecifier ||| containsSeparator
end TokenFlags

/-! ## FlowFlags -/

structure FlowFlags where
  val : UInt32
  deriving BEq, Repr, Inhabited, Hashable

namespace FlowFlags
  instance : OrOp FlowFlags where or a b := ⟨a.val ||| b.val⟩
  instance : AndOp FlowFlags where and a b := ⟨a.val &&& b.val⟩
  def hasFlag (flags flag : FlowFlags) : Bool := (flags.val &&& flag.val) != 0

  def none           : FlowFlags := ⟨0⟩
  def unreachable    : FlowFlags := ⟨0x1⟩
  def start          : FlowFlags := ⟨0x2⟩
  def branchLabel    : FlowFlags := ⟨0x4⟩
  def loopLabel      : FlowFlags := ⟨0x8⟩
  def assignment     : FlowFlags := ⟨0x10⟩
  def trueCondition  : FlowFlags := ⟨0x20⟩
  def falseCondition : FlowFlags := ⟨0x40⟩
  def switchClause   : FlowFlags := ⟨0x80⟩
  def arrayMutation  : FlowFlags := ⟨0x100⟩
  def call           : FlowFlags := ⟨0x200⟩
  def reduceLabel    : FlowFlags := ⟨0x400⟩
  def referenced     : FlowFlags := ⟨0x800⟩
  def shared         : FlowFlags := ⟨0x1000⟩

  def label : FlowFlags := branchLabel ||| loopLabel
  def condition : FlowFlags := trueCondition ||| falseCondition
end FlowFlags

/-! ## ObjectFlags -/

structure ObjectFlags where
  val : UInt32
  deriving BEq, Repr, Inhabited, Hashable

namespace ObjectFlags
  instance : OrOp ObjectFlags where or a b := ⟨a.val ||| b.val⟩
  instance : AndOp ObjectFlags where and a b := ⟨a.val &&& b.val⟩
  def hasFlag (flags flag : ObjectFlags) : Bool := (flags.val &&& flag.val) != 0

  def none                   : ObjectFlags := ⟨0⟩
  def class_                 : ObjectFlags := ⟨0x1⟩
  def interface_             : ObjectFlags := ⟨0x2⟩
  def reference              : ObjectFlags := ⟨0x4⟩
  def tuple                  : ObjectFlags := ⟨0x8⟩
  def anonymous              : ObjectFlags := ⟨0x10⟩
  def mapped                 : ObjectFlags := ⟨0x20⟩
  def instantiated           : ObjectFlags := ⟨0x40⟩
  def objectLiteral          : ObjectFlags := ⟨0x80⟩
  def evolvingArray          : ObjectFlags := ⟨0x100⟩
  def objectLiteralPatternWithComputedProperties : ObjectFlags := ⟨0x200⟩
  def reverseMapped          : ObjectFlags := ⟨0x400⟩
  def jsxAttributes          : ObjectFlags := ⟨0x800⟩
  def jsLiteral              : ObjectFlags := ⟨0x1000⟩
  def freshLiteral           : ObjectFlags := ⟨0x2000⟩
  def arrayLiteral           : ObjectFlags := ⟨0x4000⟩
  def classOrInterface : ObjectFlags := class_ ||| interface_
end ObjectFlags

end TSLean.Ast
