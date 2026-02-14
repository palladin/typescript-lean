-- TSLean.Core.TextRange: Position and text range types

namespace TSLean.Core

/-- A position in source text (byte offset). -/
abbrev Pos := UInt32

/-- A range in source text [pos, end). -/
structure TextRange where
  pos : Pos
  «end» : Pos
  deriving BEq, Repr, Inhabited, Hashable

/-- Line and character (0-based). -/
structure LineAndCharacter where
  line : UInt32
  character : UInt32
  deriving BEq, Repr, Inhabited

namespace TextRange

def length (r : TextRange) : UInt32 := r.end - r.pos

def contains (r : TextRange) (p : Pos) : Bool := r.pos <= p && p < r.end

def overlaps (a b : TextRange) : Bool := a.pos < b.end && b.pos < a.end

end TextRange

end TSLean.Core
