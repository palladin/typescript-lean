# TypeScript Compiler: Information Flow Design

This document traces the flow of data through the TypeScript reference compiler,
from raw source text to emitted JavaScript. Each stage is described in terms of
its **input**, **output**, **key data structures**, and **responsibilities**.

It also covers the **TypeScript-Go native port** (codename "Corsa"), highlighting
structural and type-level differences relevant to a Lean4 port.

Reference sources:
- `reference/TypeScript/src/compiler/` (original TypeScript, in TS)
- `reference/typescript-go/internal/` (native Go port)

---

## Pipeline Overview

The pipeline is identical in both implementations:

```
  Source Text (string)
       │
       ▼
  ┌─────────┐
  │ Scanner  │  TS: scanner.ts (4,101 lines)   Go: scanner/scanner.go (2,632 lines)
  └────┬─────┘
       │  Token stream (on demand, pull-based)
       ▼
  ┌─────────┐
  │ Parser   │  TS: parser.ts (10,823 lines)   Go: parser/parser.go (6,582 lines)
  └────┬─────┘
       │  Unbound AST (SourceFile tree)
       ▼
  ┌─────────┐
  │ Binder   │  TS: binder.ts (3,913 lines)    Go: binder/binder.go (2,700 lines)
  └────┬─────┘
       │  AST + Symbols + Flow graph
       ▼
  ┌─────────┐
  │ Checker  │  TS: checker.ts (54,419 lines)   Go: checker/*.go (55,106 lines across 18 files)
  └────┬─────┘
       │  Fully typed AST + diagnostics
       ▼
  ┌──────────────┐
  │ Transformers │  TS: transformer.ts + transformers/*.ts   Go: transformers/**/*.go (44 files)
  └──────┬───────┘
       │  Lowered AST (target-appropriate JS)
       ▼
  ┌─────────┐
  │ Emitter  │  TS: emitter.ts (6,378 lines)   Go: compiler/emitter.go + printer/printer.go (6,566 lines)
  └────┬─────┘
       │
       ▼
  Output files (.js, .d.ts, .js.map)
```

The **Program** orchestrates this entire pipeline and manages
the set of source files, compiler options, and the host abstraction
for file system access.

---

## AST Node Representation: TS vs Go

Before diving into stages, the most fundamental difference between the two
implementations is how AST nodes are modeled. This affects every stage.

### TypeScript: Class hierarchy

Nodes use a class inheritance chain. Each `SyntaxKind` corresponds to a
specific subclass. Child properties are direct fields on the subclass:

```typescript
interface Node {
    kind: SyntaxKind       // discriminator (e.g., BinaryExpression)
    flags: NodeFlags       // context flags (Let, Const, Ambient, etc.)
    pos: number            // start position (inclusive of leading trivia)
    end: number            // end position
    parent: Node           // set later by binder
    // ... kind-specific child properties on subclasses
}
```

### Go: Single `Node` struct + interface dispatch

Go cannot use class inheritance. Instead, a **single `Node` struct** wraps
a `nodeData` interface that holds kind-specific data:

```go
type Node struct {
    Kind   Kind              // int16, equivalent to SyntaxKind
    Flags  NodeFlags         // uint32 bitset
    Loc    core.TextRange    // {Pos, End int}
    id     atomic.Uint64     // unique ID (lazily assigned)
    Parent *Node             // parent pointer
    data   nodeData          // interface — holds kind-specific fields
}
```

The `nodeData` interface is implemented by **230+ concrete structs**, one per
syntax kind. These structs use **Go struct embedding** (composition) instead
of class inheritance to mix in shared capabilities:

```go
// Example: FunctionDeclaration composes multiple base types
type FunctionDeclaration struct {
    StatementBase                // NodeBase + FlowNodeBase
    DeclarationBase              // Symbol storage
    ExportableBase               // LocalSymbol for exports
    ModifiersBase                // cached ModifierList
    FunctionLikeWithBodyBase     // TypeParameters, Parameters, ReturnType, Body
    compositeNodeBase            // caches SubtreeFacts
    name           *IdentifierNode
    ReturnFlowNode *FlowNode
}
```

### Key structural difference: Mixin composition vs inheritance

| Aspect | TypeScript | Go |
|--------|------------|-----|
| Node hierarchy | Class inheritance (`Node → Expression → BinaryExpr`) | Single `Node` + embedded `nodeData` interface |
| Kind-specific fields | Subclass properties | Fields on the concrete `nodeData` implementor |
| Polymorphism | `instanceof` / subclass method override | Interface method dispatch (`ForEachChild`, `VisitEachChild`) |
| Mixins / traits | Not available | Struct embedding (`DeclarationBase`, `FunctionLikeBase`, etc.) |
| Node creation | `new` + constructor | `NodeFactory` with **object pools** per kind (50+ pools) |
| Child storage | Direct fields + `NodeArray<T>` | `*Node` pointers + `*NodeList` (slice of `*Node`) |
| Type aliases | Subclass types | Go type aliases: `Statement = Node`, `Expression = Node`, etc. |

### NodeFactory

Both implementations use a factory for node creation, but the Go version adds
**object pooling** to minimize allocations:

```go
type NodeFactory struct {
    binaryExpressionPool  core.Pool[BinaryExpression]
    ifStatementPool       core.Pool[IfStatement]
    callExpressionPool    core.Pool[CallExpression]
    // ... 50+ pools for frequently allocated node types
    hooks  NodeFactoryHooks  // OnCreate, OnUpdate, OnClone callbacks
}
```

### SubtreeFacts (Go only)

The Go port adds a **`SubtreeFacts`** bitmask cached on composite nodes
(via `compositeNodeBase`) to quickly test whether a subtree contains certain
syntax (TypeScript constructs, JSX, decorators, specific ES features).
This avoids full subtree walks when deciding which transformers to apply.

---

## Stage 1: Scanner (Lexical Analysis)

**TS File:** `scanner.ts`
**Go File:** `scanner/scanner.go`
**Input:** Source text (`string`) + position
**Output:** One token at a time (pull-based via `Scan()`)

### What it does

The scanner is a **stateful, pull-based tokenizer**. The parser calls `Scan()`
to advance to the next token, reading the scanner's current state.

### Implementation difference

| Aspect | TypeScript | Go |
|--------|------------|-----|
| Shape | **Stateful closure** via `createScanner()` | **Struct** with embedded `ScannerState` |
| State capture | Manual object cloning | Value-semantic struct copy (`Mark()` / `Rewind()`) |
| Character decoding | JS string (UTF-16 code units) | Go string (UTF-8, `utf8.DecodeRune`) |
| Number caching | Inline maps | Three explicit maps: `numberCache`, `hexNumberCache`, `hexDigitCache` |

### Go scanner state

```go
type ScannerState struct {
    pos                       int
    fullStartPos              int
    tokenStart                int
    token                     ast.Kind        // equivalent to SyntaxKind
    tokenValue                string
    tokenFlags                ast.TokenFlags
    commentDirectives         []ast.CommentDirective
    skipJSDocLeadingAsterisks int
}

type Scanner struct {
    text             string
    languageVariant  core.LanguageVariant
    onError          ErrorCallback
    skipTrivia       bool
    JSDocParsingMode ast.JSDocParsingMode
    scriptKind       core.ScriptKind
    ScannerState                       // embedded (value semantics for mark/rewind)
    numberCache      map[string]string
    hexNumberCache   map[string]string
    hexDigitCache    map[string]string
}
```

The `ScannerState` is embedded directly — copying the struct captures all
mutable state, making `Mark()` / `Rewind()` trivial. In TypeScript, the
equivalent requires manually saving and restoring each field.

### Token representation

Tokens use `ast.Kind` (`int16`) — the same enum as AST node kinds. Keywords
are looked up via `textToKeyword` and `textToToken` maps at scanner init.

### Rescan methods

Both implementations expose the same set of rescan functions:

| Go Method | TS Equivalent |
|-----------|---------------|
| `ReScanGreaterToken()` | `reScanGreaterToken()` |
| `ReScanSlashToken()` | `reScanSlashToken()` |
| `ReScanTemplateToken()` | `reScanTemplateToken()` |
| `ReScanLessThanToken()` | `reScanLessThanToken()` |
| `ReScanQuestionToken()` | `reScanQuestionToken()` |
| `ReScanAsteriskEqualsToken()` | `reScanAsteriskEqualsToken()` |
| `ReScanHashToken()` | `reScanHashToken()` |
| `ReScanJsxToken()` | (inline in TS) |
| `ReScanJsxAttributeValue()` | (inline in TS) |

### Trivia and diagnostics

Identical approach: trivia is skipped when `skipTrivia` is true, occupying
`[fullStartPos, tokenStart)`. Errors reported via callback in both.

---

## Stage 2: Parser (Syntactic Analysis)

**TS File:** `parser.ts`
**Go File:** `parser/parser.go`
**Input:** Token stream from scanner
**Output:** `SourceFile` — the root AST node containing the full syntax tree

### What it does

A **recursive descent parser** that consumes tokens from the scanner and builds
a concrete syntax tree. Every syntactic construct in TypeScript/JavaScript has a
corresponding `parse*` function.

### Implementation difference

| Aspect | TypeScript | Go |
|--------|------------|-----|
| Shape | Module-level state + functions | `Parser` struct with methods |
| Scanner integration | Owns scanner via closure | `*scanner.Scanner` field |
| Node creation | `NodeFactory` from `factory/nodeFactory.ts` | `ast.NodeFactory` with object pools |
| State save/restore | Manual field snapshot | `ParserState` struct + `mark()` / `rewind()` |
| Identifier interning | `Map<string, string>` | `map[string]string` (identical purpose) |
| Diagnostics | Single `parseDiagnostics[]` | Three lists: parse, JS-specific, JSDoc |

### Go parser state

```go
type Parser struct {
    scanner         *scanner.Scanner
    factory         ast.NodeFactory
    sourceText      string
    token           ast.Kind
    contextFlags    ast.NodeFlags
    parsingContexts ParsingContexts       // bitmask of 26 parsing contexts
    hasParseError   bool
    identifiers     map[string]string     // identifier string interning
    nodeSlicePool   core.Pool[*ast.Node]  // pool for node slices
    jsdocCache      map[*ast.Node][]*ast.Node
    diagnostics     []*ast.Diagnostic
    jsDiagnostics   []*ast.Diagnostic
}
```

### Speculative parsing

Both use the same mark/rewind pattern. The Go version captures state explicitly:

```go
type ParserState struct {
    scannerState                scanner.ScannerState  // value copy
    contextFlags                ast.NodeFlags
    diagnosticsLen              int                   // truncate to rollback errors
    jsDiagnosticsLen            int
    hasParseError               bool
}

func (p *Parser) lookAhead(callback func(p *Parser) bool) bool {
    state := p.mark()
    result := callback(p)
    p.rewind(state)
    return result
}
```

Arrow function disambiguation uses `core.Tristate` (True/False/Unknown) for the
same three-way decision as TypeScript's `Tristate` enum.

### Error recovery

Identical strategy in both: `parseExpected()` reports but doesn't consume,
list parsing uses the 26-entry `ParsingContext` bitmask to bubble up through
enclosing contexts, and `createMissingNode()` inserts synthetic nodes.

### SourceFile output

```go
type SourceFile struct {
    fileName         string
    text             string
    Statements       *NodeList
    EndOfFileToken   *TokenNode
    diagnostics      []*Diagnostic        // parse errors
    jsDiagnostics    []*Diagnostic        // JS-specific errors (separate)
    jsdocDiagnostics []*Diagnostic        // JSDoc errors (separate)
    Identifiers      map[string]string
    imports          []*LiteralLikeNode
    Pragmas          []Pragma
    CommentDirectives []CommentDirective
    // ... binder-populated fields follow
    EndFlowNode      *FlowNode
    SymbolCount      int
}
```

**Difference**: Go separates diagnostics into three lists (parse, JS, JSDoc)
vs TypeScript's single `parseDiagnostics`. This enables more granular filtering.

**Difference**: Go sets `parent` pointers **during parsing** (before binding),
while TypeScript defers parent-setting to the binder. This is possible because
Go's factory hooks fire on node creation.

---

## Stage 3: Binder (Symbol & Scope Analysis)

**TS File:** `binder.ts`
**Go File:** `binder/binder.go`
**Input:** Unbound `SourceFile` AST
**Output:** Same AST, mutated with symbols and flow graph

### What it does

The binder walks the AST and performs:

1. **Create Symbols** — each named declaration gets a `Symbol` entry
2. **Build the flow control graph** — for control-flow-based type narrowing
3. **Set `parent` pointers** (TS only — Go does this during parsing)

### Symbol representation

**TypeScript:**
```typescript
interface Symbol {
    flags: SymbolFlags
    escapedName: string
    declarations: Declaration[]
    valueDeclaration: Declaration
    members?: SymbolTable          // Map<string, Symbol>
    exports?: SymbolTable
}
```

**Go:**
```go
type Symbol struct {
    Flags                        SymbolFlags
    CheckFlags                   CheckFlags      // checker-only flags (new)
    Name                         string
    Declarations                 []*Node
    ValueDeclaration             *Node
    Members                      SymbolTable     // map[string]*Symbol
    Exports                      SymbolTable
    Parent                       *Symbol         // parent symbol (new)
    ExportSymbol                 *Symbol         // linked export symbol (new)
    AssignmentDeclarationMembers collections.Set[*Node]
    GlobalExports                SymbolTable
}
```

**Differences**:
- Go's `Symbol` includes `Parent *Symbol` for navigating the symbol tree
  upward (TypeScript accesses this via the node's parent chain).
- Go's `Symbol` includes `CheckFlags` directly on the struct instead of
  in a separate link table. This avoids an extra lookup during checking.
- Go's `Symbol` has `ExportSymbol` for the dual local/export symbol
  pattern, linking the local symbol to its export counterpart.
- `SymbolTable` is `map[string]*Symbol` in Go (vs `Map<string, Symbol>` in TS).

### Scope chain

Containers hold a `locals` symbol table via `LocalsContainerBase`:

```go
type LocalsContainerBase struct {
    Locals        SymbolTable   // map[string]*Symbol
    NextContainer *Node         // linked list of containers in declaration order
}
```

**Difference**: Go adds an explicit `NextContainer` linked list connecting
containers in source order. TypeScript traverses the AST to find siblings.

Container classification uses a `ContainerFlags` bitmask:

| Flag | Meaning |
|------|---------|
| `IsContainer` | Basic scope container (class, enum, object literal) |
| `IsBlockScopedContainer` | Block scope (catch, for, block) |
| `IsControlFlowContainer` | Requires flow graph (functions, modules) |
| `IsFunctionLike` | Function/method/constructor |
| `HasLocals` | Eagerly initialize symbol table |
| `IsThisContainer` | Tracks `this` binding |

### Flow control graph

**TypeScript** — discriminated union of flow node types:
```typescript
type FlowNode =
    | FlowStart | FlowLabel | FlowAssignment
    | FlowCondition | FlowSwitchClause | FlowArrayMutation
    | FlowCall | FlowReduceLabel
```

**Go** — single struct with a `FlowFlags` discriminator:
```go
type FlowNode struct {
    Flags       FlowFlags      // bitmask: Start, BranchLabel, LoopLabel, Assignment, etc.
    Node        *Node          // associated AST node
    Antecedent  *FlowNode      // single predecessor
    Antecedents *FlowList      // multiple predecessors (for labels)
}

type FlowList struct {           // linked list of antecedents
    Flow *FlowNode
    Next *FlowList
}
```

**Difference**: TypeScript uses separate types for each flow kind. Go uses a
single `FlowNode` with flag-based discrimination and a linked list
(`FlowList`) for multiple antecedents, avoiding slice allocation.

### Binder pooling (Go only)

The Go binder is **object-pooled** — `Binder` instances are reused across
files via `sync.Pool`, and `FlowNode` / `FlowList` allocations use pooling
to reduce GC pressure.

### Declaration merging

Both implementations use the same merge rules: same-named `interface`,
`namespace`, and `enum` declarations merge into a single Symbol. Conflict
detection uses `excludes` flag masks. The Go version adds support for
`SymbolFlagsReplaceableByMethod` (JS constructor-declared properties that
can be replaced by prototype methods).

---

## Stage 4: Checker (Semantic Analysis & Type Checking)

**TS File:** `checker.ts` (54,419 lines — single file)
**Go Files:** `checker/*.go` (55,106 lines across 18 files)
**Input:** Bound AST with symbols and flow graph
**Output:** Type information on every expression + semantic diagnostics

### What it does

The checker is the **type system engine**. It:

1. **Resolves symbols** across scopes, modules, and declaration merging
2. **Infers types** for expressions, variables, return types
3. **Checks assignability** and reports type errors
4. **Performs control-flow narrowing** using the flow graph
5. **Resolves overloads** for function calls
6. **Checks generics** — type parameter inference, constraints, variance

### Go file decomposition

The monolithic `checker.ts` is split in Go:

| File | Lines | Responsibility |
|------|-------|----------------|
| `checker.go` | 31,291 | Core type checking, inference orchestration, caching |
| `relater.go` | 4,925 | Type relationship checking (assignability, subtyping) |
| `nodebuilderimpl.go` | 3,153 | Type serialization to syntax nodes |
| `flow.go` | 2,729 | Control-flow analysis and type narrowing |
| `grammarchecks.go` | 2,218 | Grammar/syntax validation |
| `utilities.go` | 1,740 | Helper functions |
| `inference.go` | 1,620 | Generic type parameter inference |
| `jsx.go` | 1,480 | JSX type checking |
| `types.go` | 1,270 | Type/Signature/Flags definitions |
| `emitresolver.go` | 1,210 | Emit-time symbol resolution |
| `services.go` | 1,065 | External API |
| `symbolaccessibility.go` | 759 | Symbol visibility checking |
| `printer.go` | 384 | Type stringification |
| `mapper.go` | 296 | Type parameter mapping |

### Key data structure: Type

**TypeScript:**
```typescript
interface Type {
    flags: TypeFlags
    symbol?: Symbol
}

interface UnionOrIntersectionType extends Type {
    types: Type[]
}

interface ObjectType extends Type {
    members?: SymbolTable
    callSignatures?: Signature[]
    constructSignatures?: Signature[]
}

interface TypeReference extends ObjectType {
    target: GenericType
    typeArguments: Type[]
}
```

**Go:**
```go
type Type struct {
    flags       TypeFlags       // uint32
    objectFlags ObjectFlags     // uint32 — additional flags for object types
    id          TypeId          // unique ID for caching
    symbol      *ast.Symbol
    alias       *TypeAlias
    checker     *Checker        // back-reference to owning checker
    data        TypeData        // interface — kind-specific data
}
```

**Differences**:
- Go's `Type` includes `objectFlags` directly on the struct (TypeScript stores
  this only on `ObjectType` subclasses). This avoids type-casting to check flags.
- Go's `Type` has a `checker` back-reference for lazy resolution.
- Go's `Type` has a unique `id` field for use as cache keys (TypeScript uses
  object identity).
- Go uses `TypeData` interface (discriminated union) instead of class
  hierarchy. Concrete types: `IntrinsicType`, `LiteralType`, `ObjectType`,
  `UnionType`, `IntersectionType`, `TypeParameter`, `ConditionalType`,
  `IndexType`, `IndexedAccessType`, `MappedType`, `TemplateLiteralType`, etc.

### Signature

**TypeScript:**
```typescript
interface Signature {
    declaration: SignatureDeclaration
    typeParameters?: TypeParameter[]
    parameters: Symbol[]
    resolvedReturnType?: Type
}
```

**Go:**
```go
type Signature struct {
    flags                SignatureFlags
    minArgumentCount     int32
    declaration          *ast.Node
    typeParameters       []*Type
    parameters           []*ast.Symbol
    thisParameter        *ast.Symbol
    resolvedReturnType   *Type
    resolvedTypePredicate *TypePredicate
    target               *Signature     // instantiation target
    mapper               *TypeMapper    // instantiation mapper
    composite            *CompositeSignature
}
```

**Difference**: Go's `Signature` stores `target` + `mapper` directly for
tracking generic instantiation chains. TypeScript uses separate link maps.

### StructuredType (Go)

```go
type StructuredType struct {
    members            ast.SymbolTable
    properties         []*ast.Symbol
    signatures         []*Signature    // call + construct in one flat array
    callSignatureCount int             // first N are call signatures
    indexInfos         []*IndexInfo
}
```

**Difference**: Go stores call and construct signatures in a **single flat
slice** split by `callSignatureCount`, avoiding two separate arrays.

### Caching strategy

**TypeScript**: Results are cached directly on nodes/symbols as ad-hoc
properties (e.g., `node.resolvedType`, `symbol.type`).

**Go**: Uses `core.LinkStore[K, V]` — a concurrent map keyed by pointer identity:

```go
nodeLinks          core.LinkStore[*ast.Node, NodeLinks]
valueSymbolLinks   core.LinkStore[*ast.Symbol, ValueSymbolLinks]
typeAliasLinks     core.LinkStore[*ast.Symbol, TypeAliasLinks]
```

This separates checker state from AST nodes, keeping the AST immutable from
the checker's perspective. It also enables **thread-safe** access (the Go
checker uses `sync.Mutex` for concurrent checking; TypeScript is single-threaded).

Additional caches include:
- `stringLiteralTypes`, `numberLiteralTypes` — interned literal types
- `unionTypes`, `intersectionTypes`, `tupleTypes` — structural type caches
- `narrowedTypes` — control-flow narrowing results
- `cachedTypes[CachedTypeKey]` — keyed by `(kind, typeId)` for apparent types,
  awaited types, widened types, etc.
- `flowLoopCache`, `flowTypeCache` — flow analysis convergence

### Control-flow narrowing

Both use the same backward-walk algorithm, but Go structures it differently:

```go
type FlowState struct {
    reference     *ast.Node
    declaredType  *Type
    initialType   *Type
    flowContainer *ast.Node
    refKey        CacheHashKey
    depth         int            // max 2000 to prevent stack overflow
}
```

**Difference**: Go uses an explicit `FlowState` struct (object-pooled) to
thread narrowing state, while TypeScript uses closure-captured variables.
The Go version also uses a `TypeFacts` bitmask for efficient union member
filtering during narrowing.

### Type relations

**TypeScript**: Inline in `checker.ts`.

**Go**: Extracted to `relater.go` (4,925 lines) with a dedicated `Relation`
struct holding sparse result caches:

```go
type Relation struct {
    results map[CacheHashKey]RelationComparisonResult
}
```

### Diagnostics

Both use the same `Diagnostic` structure. Go adds `DiagnosticsCollection` with
thread-safe accumulation and diagnostic chaining for compound errors.

---

## Stage 5: Transformers (AST-to-AST Lowering)

**TS File:** `transformer.ts` (orchestrator) + `transformers/*.ts`
**Go Files:** `transformers/**/*.go` (44 files across subdirectories)
**Input:** Checked AST + compiler options (target, module)
**Output:** Lowered AST suitable for the target runtime

### What they do

Transformers rewrite the AST to remove syntax that the target runtime doesn't
support.

### Implementation difference

| Aspect | TypeScript | Go |
|--------|------------|-----|
| Transformer shape | `(context) => (file) => file` closure | `Transformer` struct with `emitContext` + `factory` + `visitor` |
| Chaining | `compose()` | `Chain()` function |
| Context | `TransformationContext` | `EmitContext` (object-pooled via `sync.Pool`) |
| Hoisting | Implicit in context | Explicit `StartLexicalEnvironment()` / `EndLexicalEnvironment()` stacks |

### Go transformer pipeline

The Go port splits TypeScript's monolithic `transformTypeScript` into
**four separate transforms** for clarity:

| Go Transform | TS Equivalent |
|-------------|---------------|
| `MetadataTransformer` | Part of `transformTypeScript` |
| `TypeEraserTransformer` | Part of `transformTypeScript` |
| `ImportElisionTransformer` | Part of `transformTypeScript` |
| `RuntimeSyntaxTransformer` (enums, namespaces, param properties) | Part of `transformTypeScript` |
| `LegacyDecoratorsTransformer` | Part of `transformTypeScript` |
| `JSXTransformer` | `transformJsx` |
| `GetESTransformer()` (per-target chain: ES2016→ESNext) | `transformES2022–ES2015` |
| `UseStrictTransformer` | Inline in TS |
| Module transforms (ES, CommonJS, Implied) | `transformModule` |
| `ConstEnumInliningTransformer` | Inline in checker |
| `DeclarationTransformer` | `transformDeclarations` |

### Module transforms

Go uses three distinct module transformers where TypeScript has a single
configurable one:

| Go Transformer | When used |
|----------------|-----------|
| `ESModuleTransformer` | `--module preserve` |
| `ImpliedModuleTransformer` | ESNext, ES2022, Node16+, CommonJS |
| `CommonJSModuleTransformer` | Older module kinds |

### Visitor pattern

Same structural sharing approach. Go's `NodeVisitor` struct wraps the visit
function and factory:

```go
type NodeVisitor struct {
    Visit   func(node *Node) *Node
    Factory *NodeFactory
    Hooks   NodeVisitorHooks
}
```

Each concrete node type implements `VisitEachChild(*NodeVisitor) *Node`,
rebuilding the node only if a child changed (same as TypeScript's
`visitEachChild`).

### Emit helpers

Same approach: runtime helpers tracked as `EmitHelper` objects, emitted as
`tslib` imports or inlined.

---

## Stage 6: Emitter (Code Generation)

**TS File:** `emitter.ts`
**Go Files:** `compiler/emitter.go` (494 lines) + `printer/printer.go` (6,072 lines)
**Input:** Transformed AST
**Output:** `.js` files, `.d.ts` files, `.js.map` source maps

### What it does

The emitter is a **tree printer**. It walks the final AST and writes text to
an output stream via a `TextWriter`. It handles:

- **Formatting** — indentation, line breaks, semicolons
- **Comments** — preserving/synthesizing leading and trailing comments
- **Source maps** — tracking original positions for debugger mapping
- **Declaration emit** — producing `.d.ts` type declaration files

### Implementation difference

| Aspect | TypeScript | Go |
|--------|------------|-----|
| Architecture | Single `emitter.ts` | Split: `emitter.go` (orchestration) + `printer.go` (printing) |
| Emit context | Inline in emitter | `EmitContext` struct, object-pooled |
| Declaration emit | Part of transformer pipeline | Separate `DeclarationTransformer` (2,129 lines) |
| Source maps | `SourceMapGenerator` inline | Separate `sourcemap/generator.go` |
| EmitResolver | Checker implements interface | Same pattern |

### Two-stage emit (Go)

1. **JS emission**: Apply transformer pipeline → print via printer
2. **Declaration emission**: Apply `DeclarationTransformer` → print `.d.ts`

The `EmitContext` is pooled via `sync.Pool` to avoid allocation per file.

### Source maps

Both use Base64 VLQ-encoded `.js.map` files. Go's `sourcemap.Generator`
struct tracks the same state (last generated/source line/character, sources,
names, mappings builder).

---

## Orchestration: Program

**TS File:** `program.ts`
**Go File:** `execute/tsc/emit.go` + supporting files
**Input:** Compiler options + root file names + host
**Output:** Compiled output files + diagnostics

### What it does

`Program` is the top-level coordinator. Both implementations:

1. **Resolve the file set** — follow imports/references to discover source files
2. **Parse** each source file (scanner + parser)
3. **Create the type checker** (which triggers binding on demand)
4. **Provide diagnostic APIs** (syntactic, semantic, declaration)
5. **Run emit** — transforms + prints to output files

### Implementation difference

| Aspect | TypeScript | Go |
|--------|------------|-----|
| Host abstraction | `CompilerHost` interface | `EmitHost` interface (combines printer + declaration hosts) |
| Timing | Not tracked | `bindTime`, `checkTime`, `emitTime` tracked in `CompileTimes` |
| Cancellation | Not supported | `context.Context` for cancellation |
| Concurrency | Single-threaded | Mutex-protected checker, pooled binders |

---

## Diagnostic Flow Summary

Diagnostics are collected at multiple stages and unified by Program:

```
Scanner errors     →  attached to SourceFile.parseDiagnostics
Parser errors      →  attached to SourceFile.parseDiagnostics
Binder errors      →  stored in binder diagnostic list
Checker errors     →  returned by getSemanticDiagnostics()
Declaration errors →  returned by getDeclarationDiagnostics()
                         │
                         ▼
                   Program.getDiagnostics()
                   (unified, sorted by position)
```

**Go difference**: Parser produces three separate diagnostic lists (parse,
JS-specific, JSDoc) instead of one. Checker uses `DiagnosticsCollection`
with thread-safe accumulation.

Each diagnostic carries:

```typescript
interface Diagnostic {
    file: SourceFile
    start: number
    length: number
    messageText: string
    category: DiagnosticCategory  // Error, Warning, Suggestion, Message
    code: number
    relatedInformation?: DiagnosticRelatedInformation[]
}
```

The Go `Diagnostic` struct is equivalent, with support for diagnostic chaining
(linked `Diagnostic` nodes for compound error messages).

---

## Data Flow Summary Table

| Stage | Input | Output | TS Key Types | Go Key Types |
|-------|-------|--------|-------------|-------------|
| Scanner | `string` + position | Token (kind + value + flags) | `SyntaxKind`, `TokenFlags` | `ast.Kind` (int16), `ast.TokenFlags` |
| Parser | Token stream | `SourceFile` (AST) | `Node`, `NodeArray`, `NodeFlags` | `ast.Node` (single struct), `*NodeList`, `NodeFlags` |
| Binder | Unbound AST | AST + Symbols + Flow graph | `Symbol`, `SymbolTable`, `FlowNode` (union) | `ast.Symbol` (struct), `map[string]*Symbol`, `ast.FlowNode` (single struct + flags) |
| Checker | Bound AST | Typed AST + diagnostics | `Type` (class hierarchy), `Signature`, `Diagnostic` | `Type` (struct + `TypeData` interface), `Signature`, `Diagnostic` |
| Transformers | Typed AST | Lowered AST | Same `Node` types, rewritten | Same `Node` types, rewritten via `NodeVisitor` |
| Emitter | Lowered AST | `.js` / `.d.ts` / `.map` text | `TextWriter`, `SourceMapGenerator` | `EmitTextWriter`, `sourcemap.Generator` |

---

## Structural Differences Summary

| Concern | TypeScript (TS) | Go Port |
|---------|----------------|---------|
| **AST node model** | Class hierarchy with subclasses per kind | Single `Node` struct + `nodeData` interface + struct embedding |
| **Node creation** | `new` via factory | Object-pooled factory (50+ pools) |
| **Kind enum** | `SyntaxKind` (numeric enum) | `ast.Kind` (`int16`, `iota`) |
| **Scanner state** | Closure-captured mutable vars | Embedded `ScannerState` struct (value-semantic copy) |
| **Flow graph** | Discriminated union of types | Single `FlowNode` struct + `FlowFlags` + `FlowList` linked list |
| **Symbol extras** | Ad-hoc properties | `Parent`, `CheckFlags`, `ExportSymbol` on struct |
| **Container chain** | AST traversal | Explicit `NextContainer` linked list |
| **Type hierarchy** | `Type` → `ObjectType` → `InterfaceType` (classes) | Single `Type` struct + `TypeData` interface (composition) |
| **Type caching** | Properties on nodes/symbols | `LinkStore[K, V]` concurrent maps, keyed by pointer + ID |
| **Checker scope** | Single 54K-line file | 18 files totaling 55K lines |
| **Checker threading** | Single-threaded | `sync.Mutex`-protected, `context.Context` cancellation |
| **Transformer split** | Monolithic `transformTypeScript` | 5 separate transforms (metadata, type erasure, import elision, runtime syntax, legacy decorators) |
| **Memory management** | JS GC | Object pools for Scanner, Binder, EmitContext, FlowState, InferenceState, NodeFactory |
| **Diagnostics** | Single parse diagnostic list | Three lists (parse, JS, JSDoc) + thread-safe collection |
| **Parent pointers** | Set by binder | Set during parsing |
| **SubtreeFacts** | Not present | Cached bitmask on composite nodes for fast transformer filtering |

---

## Porting Notes

### Primary reference: the Go port

The Lean4 port should be based on the **Go implementation**, not the original
TypeScript. Go is a far better translation source for Lean4 because:

1. **No class inheritance** — Go already solved the "no subclasses" problem.
   Its single `Node` struct + `nodeData` interface maps directly to a Lean4
   inductive type, whereas TypeScript's deep class hierarchy would need to be
   dismantled first.

2. **Explicit state threading** — Go's `ScannerState` struct, `ParserState`
   struct, and `FlowState` struct make all mutable state visible as value
   types. These translate directly to Lean4 state monads or explicit parameter
   passing. TypeScript's closure-captured mutable variables are much harder
   to identify and extract.

3. **Side-table caching** — Go's `LinkStore[K, V]` pattern (checker data
   stored in separate maps keyed by node/symbol ID rather than mutated onto
   AST nodes) is exactly the approach a pure-FP port needs. TypeScript's
   ad-hoc property mutation (`node.symbol = ...`, `node.flowNode = ...`)
   would require inventing this pattern from scratch.

4. **Composition over inheritance** — Go's struct embedding (`DeclarationBase`,
   `FunctionLikeBase`, `LocalsContainerBase`, etc.) maps naturally to Lean4
   structure extension or typeclasses, while TypeScript's class hierarchy does
   not.

5. **Flat discriminated unions** — Go uses a single `FlowNode` struct with
   `FlowFlags` and a single `Type` struct with `TypeData` interface, rather
   than TypeScript's union-of-classes. These flat representations are trivial
   to encode as Lean4 inductive types.

6. **Decomposed checker** — the 55K-line checker is already split into 18
   focused files in Go (relations, inference, flow, grammar, JSX, etc.),
   providing a natural module structure for Lean4. TypeScript's monolithic
   54K-line `checker.ts` would need manual decomposition.

7. **Explicit memory management patterns** — Go's object pools and atomic IDs
   make allocation patterns visible. Lean4 uses **reference counting** (not
   garbage collection) — it is malloc-based with refcounts, and pure code can
   perform destructive in-place updates when objects are unshared ("functional
   but in-place" / FBIP). Go's pools identify hot allocation sites, which
   helps design Lean4 structures that minimize refcount overhead and maximize
   in-place reuse.

8. **Simpler concurrency story** — Go's `sync.Mutex` and `context.Context`
   are easily identified and stripped for a single-threaded Lean4 port.
   TypeScript's implicit single-threadedness means these concerns are invisible
   and could be accidentally re-introduced.

9. **Test infrastructure parity** — the Go test harness uses the same test
   format and baselines as TypeScript, so the Lean4 port can validate against
   the same baselines. The Go submodule diffing infrastructure provides a
   proven model for tracking conformance.

In summary: the Go port has already done the hard work of translating
TypeScript's OOP/closure patterns into a struct-and-interface style that is
one step away from pure functional. The Lean4 port should treat
`reference/typescript-go/internal/` as the primary source of truth.

### Key architectural observations

1. **The scanner is pull-based and stateful** — the parser calls `scan()` on
   demand. In a pure FP port, the scanner state must be threaded explicitly
   (or use a state monad). The Go port's `ScannerState` struct shows exactly
   which fields need threading.

2. **The AST is mutated in place** — the binder sets `symbol`, `flowNode` on
   existing nodes (TS also sets `parent`; Go sets it during parsing). A pure
   port needs either a separate side-table or up-front construction with all
   data. The Go port's `LinkStore` pattern (separate concurrent maps keyed by
   node pointer) is essentially the side-table approach and may be the best
   model for Lean4.

3. **The checker is lazy and caches aggressively** — types are computed on
   demand and memoized. The Go port uses `TypeId`-keyed maps and `LinkStore`
   rather than ad-hoc node properties. A Lean4 port could use `HashMap` with
   node/type IDs as keys.

4. **Transformers use structural sharing** — `visitEachChild` only creates new
   nodes when children change. This is natural in a persistent data structure
   setting. The Go port's `SubtreeFacts` optimization (skip transformers for
   subtrees that don't contain relevant syntax) could also be adopted.

5. **The 55K-line checker is the hard part** — it encodes the entire TypeScript
   type system. The Go port's file decomposition (18 files) provides a natural
   splitting guide: core checking, type relations, inference, flow analysis,
   grammar checks, JSX, etc.

6. **Single `Node` type vs hierarchy** — both Go and a Lean4 port avoid class
   inheritance. Go uses `nodeData` interface dispatch; Lean4 could use an
   inductive type with one constructor per `SyntaxKind`. The Go port's mixin
   embedding pattern (`DeclarationBase`, `FunctionLikeBase`, etc.) maps to
   Lean4 structure composition or typeclasses.

7. **Flow graph representation** — Go's single `FlowNode` struct with flag
   discrimination and linked-list antecedents is simpler than TypeScript's
   union of types. This flat representation is easier to port to Lean4
   (single inductive type with a `FlowFlags` field).

8. **Concurrency model** — the Go port adds thread-safety (`sync.Mutex`,
   `atomic`, `context.Context`) absent in TS. A Lean4 port targeting
   single-threaded execution can ignore this, simplifying the design.

---

## Test Infrastructure

Both implementations share the **same test file format** and **baseline comparison
approach**. The Go port is a faithful reimplementation of the TS harness using
Go idioms and `testing.T`.

### Test file format

A single `.ts` test file encodes compiler options, multi-file projects, and
symlinks using comment directives:

```typescript
// @target: es2015
// @strict: true, false
// @module: commonjs
// @Filename: helper.ts
export function foo(): number { return 1; }
// @Filename: main.ts
import { foo } from "./helper";
let x: string = foo();  // error: Type 'number' is not assignable to type 'string'
```

| Directive | Purpose |
|-----------|---------|
| `// @option: value` | Set a compiler option (e.g., `// @target: es2015`) |
| `// @option: val1, val2` | If in `varyBy` allowlist, expand to multiple test configurations |
| `// @Filename: path` | Start a new file unit within the test |
| `// @link: target -> symlink` | Create a symlink in the virtual filesystem |
| `// @currentDirectory: path` | Override the working directory |

Both parse these with the same regex: `^\/{2}\s*@(\w+)\s*:\s*([^\r\n]*)`.

### Test flow

```
  Test file on disk (e.g. tests/cases/compiler/myTest.ts)
       │
       ▼
  1. DISCOVER — enumerate *.ts files under tests/cases/{conformance,compiler}/
       │
       ▼
  2. PARSE SETTINGS — extractCompilerSettings() reads // @option lines
       │
       ▼
  3. EXPAND CONFIGURATIONS — options with comma-separated values in the
     varyBy allowlist (strict, target, module, etc.) produce separate sub-tests:
       myTest(strict=true).ts
       myTest(strict=false).ts
       │
       ▼
  4. SPLIT INTO UNITS — makeUnitsFromTest() splits on // @Filename directives,
     extracts // @link symlinks, detects tsconfig.json
       │
       ▼
  5. COMPILE — build a VFS with test files + lib.d.ts, create a Program,
     run full pipeline: Parse → Bind → Check → Emit
       │
       ├──→ CompilationResult
       │      .diagnostics    — all errors/warnings
       │      .program        — the compiled Program
       │      .emittedFiles   — map of filename → content (.js, .d.ts, .map)
       │
       ▼
  6. GENERATE BASELINES — produce text snapshots from the compilation result:
       │
       ├─ 6a. Errors         — format diagnostics as text          → .errors.txt
       ├─ 6b. JS Output      — concatenate emitted .js/.d.ts      → .js
       ├─ 6c. Types & Symbols — walk AST, print type/symbol at    → .types / .symbols
       │                        each expression
       ├─ 6d. Source Maps     — decode .js.map, record mappings    → .sourcemap.txt
       ├─ 6e. Module Resolve  — trace log (if @traceResolution)   → .trace.json
       ├─ 6f. Union Ordering  — (Go only) shuffle & re-sort to verify determinism
       └─ 6g. Parent Pointers — (Go only) walk AST, verify node.Parent consistency
       │
       ▼
  7. BASELINE COMPARE — for each baseline file:
       │
       ├─ Read reference from:  tests/baselines/reference/<suite>/myTest.errors.txt
       │
       ├─ MATCH    → pass ✓
       ├─ MISMATCH → write actual to tests/baselines/local/<suite>/myTest.errors.txt
       │              FAIL ✗ "Run baseline-accept if new is correct"
       └─ NEW      → write actual to local, FAIL ✗ "New baseline created"
```

### Test infrastructure files

**TypeScript:**

| File | Role |
|------|------|
| `src/testRunner/runner.ts` | Entry point — discovers runners, reads `test.config`, runs Mocha |
| `src/testRunner/compilerRunner.ts` | `CompilerBaselineRunner` for conformance + regression tests |
| `src/testRunner/fourslashRunner.ts` | Language service tests (completions, quickinfo, etc.) |
| `src/testRunner/transpileRunner.ts` | Single-file transpilation tests |
| `src/testRunner/projectsRunner.ts` | Multi-project/references tests |
| `src/harness/harnessIO.ts` | Core harness — `TestCaseParser`, `extractCompilerSettings()`, `makeUnitsFromTest()`, `Baseline` namespace |
| `src/harness/compilerImpl.ts` | `compileFiles()`, baseline generation for errors/JS/sourcemaps/types/symbols |
| `src/harness/fourslashImpl.ts` | Fourslash engine — parses markers, runs language service assertions |
| `src/harness/fakesHosts.ts` | Virtual `CompilerHost` / `System` backed by VFS |
| `src/harness/vfsUtil.ts` | In-memory filesystem for isolated test compilation |
| `src/harness/typeWriter.ts` | Walks AST to produce `.types` and `.symbols` baselines |
| `src/harness/sourceMapRecorder.ts` | Produces `.sourcemap.txt` baselines |

**Go:**

| File | Role |
|------|------|
| `testrunner/runner.go` | `Runner` interface — `EnumerateTestFiles()` + `RunTests(t)` |
| `testrunner/compiler_runner.go` | `CompilerBaselineRunner` — conformance + regression, 7 verifications per test |
| `testrunner/compiler_runner_test.go` | Entry — `TestLocal` (new tests), `TestSubmodule` (TS tests + diff) |
| `testrunner/test_case_parser.go` | `extractCompilerSettings()`, `makeUnitsFromTest()`, `ParseTestFilesAndSymlinks()` |
| `testutil/harnessutil/harnessutil.go` | `CompileFiles()`, `TestFile`, `HarnessOptions`, VFS setup |
| `testutil/baseline/baseline.go` | `Run()` — compare actual vs reference, write diffs, submodule diffing |
| `testutil/tsbaseline/error_baseline.go` | `DoErrorBaseline()` |
| `testutil/tsbaseline/js_emit_baseline.go` | `DoJSEmitBaseline()` |
| `testutil/tsbaseline/type_symbol_baseline.go` | `DoTypeAndSymbolBaseline()` |
| `testutil/tsbaseline/sourcemap_baseline.go` | `DoSourcemapBaseline()` |
| `testutil/tsbaseline/module_resolution_baseline.go` | `DoModuleResolutionBaseline()` |
| `fourslash/fourslash.go` | `FourslashTest` — drives a full LSP server for language service tests |

### Implementation differences

| Concern | TypeScript | Go |
|---------|------------|-----|
| **Test framework** | Mocha (`describe`/`it`) | Go `testing.T` (`t.Run`) |
| **Parallelism** | Optional sharding (`Parallel.Host`/`Worker`) | Native `t.Parallel()` per test |
| **Test file parsing** | Same regex, same logic | Direct port — identical format |
| **Fourslash** | In-process language service | Full **LSP server** via JSON-RPC |
| **Extra verifications** | — | Union ordering (sort stability), parent pointer integrity |
| **VFS** | Custom `vfs` module | Go `vfs` package + `fstest.MapFS` |
| **Configuration expansion** | `getFileBasedTestConfigurations()` | `GetFileBasedTestConfigurations()` with same `compilerVaryBy` allowlist |

### Go submodule diffing

When running `TestSubmodule`, the Go runner performs an additional comparison
against the **original TypeScript baselines** from the `_submodules/TypeScript/`
checkout:

```
  Go actual output
       │
       ├── compare → Go reference baselines (tests/baselines/reference/)
       │               → pass/fail as normal
       │
       └── compare → TS submodule baselines (_submodules/TypeScript/tests/baselines/reference/)
                       → produce .diff file (unified diff, line numbers stripped)
                       → stored in baselines/local/submodule/ or submoduleAccepted/
```

This tracks exactly where Go output diverges from the original TypeScript
compiler. Known-acceptable divergences are listed in `submoduleAccepted.txt`.

### Baseline file types

Each test produces up to six baseline files:

| Extension | Content | Produced by |
|-----------|---------|-------------|
| `.errors.txt` | Formatted diagnostics with source context | `DoErrorBaseline` / `doErrorBaseline` |
| `.js` | Concatenated emitted JavaScript + declarations | `DoJSEmitBaseline` / `doJsEmitBaseline` |
| `.types` | Type of every expression: `>expr : Type` | `DoTypeAndSymbolBaseline` / `doTypeAndSymbolBaseline` |
| `.symbols` | Symbol info for every declaration | Same as above |
| `.sourcemap.txt` | Decoded source map record | `DoSourcemapRecordBaseline` / `doSourceMapRecord` |
| `.trace.json` | Module resolution trace (if `@traceResolution`) | `DoModuleResolutionBaseline` |
