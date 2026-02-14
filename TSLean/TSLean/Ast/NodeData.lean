-- TSLean.Ast.NodeData: Node metadata types

import TSLean.Core.TextRange
import TSLean.Ast.Flags

namespace TSLean.Ast

/-- Unique identifier for an AST node. -/
structure NodeId where
  val : UInt32
  deriving BEq, Hashable, Repr, Inhabited, Ord

instance : ToString NodeId where
  toString id := s!"NodeId({id.val})"

/-- Common metadata shared by all AST nodes. -/
structure NodeData where
  id    : NodeId
  flags : NodeFlags
  range : TSLean.Core.TextRange
  deriving BEq, Repr, Inhabited

namespace NodeData

def pos (nd : NodeData) : UInt32 := nd.range.pos
def «end» (nd : NodeData) : UInt32 := nd.range.end

end NodeData

end TSLean.Ast
