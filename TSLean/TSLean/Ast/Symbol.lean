-- TSLean.Ast.Symbol: Symbol, SymbolTable, SymbolStore
-- Symbols are the binder's output: each named entity in the program gets a Symbol.
-- Symbols reference AST nodes by NodeId (from NodeData), not by direct pointers.

import Std.Data.HashMap
import TSLean.Ast.NodeData
import TSLean.Ast.Flags

namespace TSLean.Ast

/-- Unique identifier for a symbol in the SymbolStore. -/
structure SymbolId where
  val : UInt32
  deriving BEq, Hashable, Repr, Inhabited, Ord

instance : ToString SymbolId where
  toString id := s!"SymbolId({id.val})"

/-- A symbol table maps escaped names to symbol IDs. -/
abbrev SymbolTable := Std.HashMap String SymbolId

/-- A symbol represents a named entity in the program (variable, function, class, etc.).
    Symbols are created by the binder and consumed by the checker. -/
structure Symbol where
  id               : SymbolId
  escapedName      : String
  flags            : SymbolFlags
  declarations     : Array NodeId
  valueDeclaration : Option NodeId
  members          : SymbolTable
  exports          : SymbolTable
  parent           : Option SymbolId
  deriving Inhabited

/-- The symbol store holds all symbols in a flat array indexed by SymbolId. -/
structure SymbolStore where
  symbols : Array Symbol
  nextId  : UInt32
  deriving Inhabited

namespace SymbolStore

def empty : SymbolStore := { symbols := #[], nextId := 0 }

def addSymbol (store : SymbolStore) (name : String) (flags : SymbolFlags) : SymbolStore × SymbolId :=
  let id : SymbolId := ⟨store.nextId⟩
  let sym : Symbol := {
    id := id
    escapedName := name
    flags := flags
    declarations := #[]
    valueDeclaration := none
    members := {}
    exports := {}
    parent := none
  }
  ({ symbols := store.symbols.push sym, nextId := store.nextId + 1 }, id)

def getSymbol (store : SymbolStore) (id : SymbolId) : Option Symbol :=
  store.symbols[id.val.toNat]?

end SymbolStore

end TSLean.Ast
