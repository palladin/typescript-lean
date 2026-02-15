/-
  TSLean.Compiler.Ast.NodeFlags — Node flags (bit flags).

  Based on Go: internal/ast/nodeflags.go (67 lines)
  Go type: NodeFlags (uint32) with 28 individual flags.
-/

namespace TSLean.Compiler

/-- Based on Go: internal/ast/nodeflags.go:3 (NodeFlags) -/
structure NodeFlags where
  val : UInt32
  deriving BEq, Repr, Inhabited, Hashable

namespace NodeFlags

-- Based on Go: internal/ast/nodeflags.go:5-46

/-- Go: nodeflags.go:6 -/ def none : NodeFlags := ⟨0⟩
/-- Go: nodeflags.go:7 — Variable declaration -/ def let_ : NodeFlags := ⟨(1 : UInt32) <<< (0 : UInt32)⟩
/-- Go: nodeflags.go:8 — Variable declaration -/ def const_ : NodeFlags := ⟨(1 : UInt32) <<< (1 : UInt32)⟩
/-- Go: nodeflags.go:9 — Variable declaration -/ def using_ : NodeFlags := ⟨(1 : UInt32) <<< (2 : UInt32)⟩
/-- Go: nodeflags.go:10 — Synthesized during parsing -/ def reparsed : NodeFlags := ⟨(1 : UInt32) <<< (3 : UInt32)⟩
/-- Go: nodeflags.go:11 — Synthesized during transformation -/ def synthesized : NodeFlags := ⟨(1 : UInt32) <<< (4 : UInt32)⟩
/-- Go: nodeflags.go:12 — Chained MemberExpression -/ def optionalChain : NodeFlags := ⟨(1 : UInt32) <<< (5 : UInt32)⟩
/-- Go: nodeflags.go:13 — Export context -/ def exportContext : NodeFlags := ⟨(1 : UInt32) <<< (6 : UInt32)⟩
/-- Go: nodeflags.go:14 — Interface contains "this" -/ def containsThis : NodeFlags := ⟨(1 : UInt32) <<< (7 : UInt32)⟩
/-- Go: nodeflags.go:15 — Implicit return -/ def hasImplicitReturn : NodeFlags := ⟨(1 : UInt32) <<< (8 : UInt32)⟩
/-- Go: nodeflags.go:16 — Explicit return -/ def hasExplicitReturn : NodeFlags := ⟨(1 : UInt32) <<< (9 : UInt32)⟩
/-- Go: nodeflags.go:17 — 'in' expressions disallowed -/ def disallowInContext : NodeFlags := ⟨(1 : UInt32) <<< (10 : UInt32)⟩
/-- Go: nodeflags.go:18 — Parsed in yield context -/ def yieldContext : NodeFlags := ⟨(1 : UInt32) <<< (11 : UInt32)⟩
/-- Go: nodeflags.go:19 — Parsed as decorator -/ def decoratorContext : NodeFlags := ⟨(1 : UInt32) <<< (12 : UInt32)⟩
/-- Go: nodeflags.go:20 — Parsed in await context -/ def awaitContext : NodeFlags := ⟨(1 : UInt32) <<< (13 : UInt32)⟩
/-- Go: nodeflags.go:21 — Conditional types disallowed -/ def disallowConditionalTypesContext : NodeFlags := ⟨(1 : UInt32) <<< (14 : UInt32)⟩
/-- Go: nodeflags.go:22 — Parser error on this node -/ def thisNodeHasError : NodeFlags := ⟨(1 : UInt32) <<< (15 : UInt32)⟩
/-- Go: nodeflags.go:23 — Parsed in JavaScript file -/ def javaScriptFile : NodeFlags := ⟨(1 : UInt32) <<< (16 : UInt32)⟩
/-- Go: nodeflags.go:24 — Error in subtree -/ def thisNodeOrAnySubNodesHasError : NodeFlags := ⟨(1 : UInt32) <<< (17 : UInt32)⟩
/-- Go: nodeflags.go:25 — Child data cached -/ def hasAggregatedChildData : NodeFlags := ⟨(1 : UInt32) <<< (18 : UInt32)⟩
/-- Go: nodeflags.go:36 — May contain dynamic import -/ def possiblyContainsDynamicImport : NodeFlags := ⟨(1 : UInt32) <<< (19 : UInt32)⟩
/-- Go: nodeflags.go:37 — May contain import.meta -/ def possiblyContainsImportMeta : NodeFlags := ⟨(1 : UInt32) <<< (20 : UInt32)⟩
/-- Go: nodeflags.go:39 — Has preceding JSDoc -/ def hasJSDoc : NodeFlags := ⟨(1 : UInt32) <<< (21 : UInt32)⟩
/-- Go: nodeflags.go:40 — Parsed inside JSDoc -/ def jsDoc : NodeFlags := ⟨(1 : UInt32) <<< (22 : UInt32)⟩
/-- Go: nodeflags.go:41 — Inside ambient context -/ def ambient : NodeFlags := ⟨(1 : UInt32) <<< (23 : UInt32)⟩
/-- Go: nodeflags.go:42 — In WithStatement -/ def inWithStatement : NodeFlags := ⟨(1 : UInt32) <<< (24 : UInt32)⟩
/-- Go: nodeflags.go:43 — Parsed in JSON file -/ def jsonFile : NodeFlags := ⟨(1 : UInt32) <<< (25 : UInt32)⟩
/-- Go: nodeflags.go:44 — @deprecated JSDoc tag -/ def deprecated : NodeFlags := ⟨(1 : UInt32) <<< (26 : UInt32)⟩
/-- Go: nodeflags.go:45 — Unreachable per binder -/ def unreachable : NodeFlags := ⟨(1 : UInt32) <<< (27 : UInt32)⟩

-- Composites (Go: nodeflags.go:47-66)

/-- Go: nodeflags.go:47 -/ def blockScoped : NodeFlags := ⟨let_.val ||| const_.val ||| using_.val⟩
/-- Go: nodeflags.go:48 -/ def constant : NodeFlags := ⟨const_.val ||| using_.val⟩
/-- Go: nodeflags.go:49 -/ def awaitUsing : NodeFlags := ⟨const_.val ||| using_.val⟩

/-- Go: nodeflags.go:51 -/ def reachabilityCheckFlags : NodeFlags := ⟨hasImplicitReturn.val ||| hasExplicitReturn.val⟩

-- Go: nodeflags.go:54 — Parsing context flags
def contextFlags : NodeFlags := ⟨disallowInContext.val ||| disallowConditionalTypesContext.val |||
  yieldContext.val ||| decoratorContext.val ||| awaitContext.val ||| javaScriptFile.val |||
  inWithStatement.val ||| ambient.val⟩

-- Go: nodeflags.go:57 — Exclude these when parsing a Type
def typeExcludesFlags : NodeFlags := ⟨yieldContext.val ||| awaitContext.val⟩

/-- Go: nodeflags.go:62 -/ def permanentlySetIncrementalFlags : NodeFlags :=
  ⟨possiblyContainsDynamicImport.val ||| possiblyContainsImportMeta.val⟩

-- Go: nodeflags.go:65 — Identifier extended unicode escape repurposes ContainsThis
def identifierHasExtendedUnicodeEscape : NodeFlags := containsThis

end NodeFlags

-- Bitwise operations
instance : OrOp NodeFlags where
  or a b := ⟨a.val ||| b.val⟩

instance : AndOp NodeFlags where
  and a b := ⟨a.val &&& b.val⟩

instance : Complement NodeFlags where
  complement a := ⟨~~~ a.val⟩

def NodeFlags.hasFlag (self flag : NodeFlags) : Bool :=
  (self.val &&& flag.val) != 0

end TSLean.Compiler
