-- TSLean.Diagnostics.Category: Diagnostic categories and types

namespace TSLean.Diagnostics

/-- Diagnostic severity categories, matching TypeScript's DiagnosticCategory. -/
inductive DiagnosticCategory where
  | warning
  | error
  | suggestion
  | message
  deriving BEq, Repr, Inhabited

/-- A diagnostic message template. -/
structure DiagnosticMessage where
  key : String
  category : DiagnosticCategory
  code : UInt32
  message : String
  deriving BEq, Repr, Inhabited

/-- A diagnostic instance with location information. -/
structure Diagnostic where
  file : Option UInt32  -- NodeId of the source file (Option NodeId)
  start : UInt32
  length : UInt32
  category : DiagnosticCategory
  code : UInt32
  messageText : String
  relatedInformation : Array Diagnostic
  deriving Inhabited

end TSLean.Diagnostics
