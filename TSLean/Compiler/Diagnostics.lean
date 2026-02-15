/-
  TSLean.Compiler.Diagnostics — Diagnostic messages for the parser.

  Based on Go: internal/ast/diagnostic.go, internal/diagnostics/
-/
import TSLean.Compiler.Core

namespace TSLean.Compiler

/-- Based on Go: internal/diagnostics/message.go -/
structure DiagnosticMessage where
  code : Int32
  message : String
  deriving BEq, Repr

/-- Based on Go: internal/ast/diagnostic.go -/
structure Diagnostic where
  loc : TextRange
  message : DiagnosticMessage
  args : Array String := #[]
  deriving Repr

-- Common diagnostic messages used by the parser.
-- Based on Go: internal/diagnostics/diagnostics.go
namespace Diagnostics

def X_0_expected : DiagnosticMessage := ⟨1005, "'{0}' expected."⟩
def declaration_or_statement_expected : DiagnosticMessage := ⟨1128, "Declaration or statement expected."⟩
def statement_expected : DiagnosticMessage := ⟨1129, "Statement expected."⟩
def case_or_default_expected : DiagnosticMessage := ⟨1130, "'case' or 'default' expected."⟩
def property_or_signature_expected : DiagnosticMessage := ⟨1131, "Property or signature expected."⟩
def expression_expected : DiagnosticMessage := ⟨1109, "Expression expected."⟩
def identifier_expected : DiagnosticMessage := ⟨1003, "Identifier expected."⟩
def variable_declaration_expected : DiagnosticMessage := ⟨1134, "Variable declaration expected."⟩
def parameter_declaration_expected : DiagnosticMessage := ⟨1138, "Parameter declaration expected."⟩
def type_parameter_declaration_expected : DiagnosticMessage := ⟨1139, "Type parameter declaration expected."⟩
def type_argument_expected : DiagnosticMessage := ⟨1140, "Type argument expected."⟩
def type_expected : DiagnosticMessage := ⟨1110, "Type expected."⟩
def unexpected_token : DiagnosticMessage := ⟨1012, "Unexpected token."⟩
def unexpected_token_constructor : DiagnosticMessage := ⟨1068, "Unexpected token. A constructor, method, accessor, or property was expected."⟩
def or_expected : DiagnosticMessage := ⟨1144, "'{' or ';' expected."⟩
def identifier_expected_reserved : DiagnosticMessage := ⟨1359, "Identifier expected. '{0}' is a reserved word that cannot be used here."⟩
def keywords_cannot_contain_escape : DiagnosticMessage := ⟨1260, "Keywords cannot contain escape characters."⟩
def declaration_expected : DiagnosticMessage := ⟨1146, "Declaration expected."⟩
def trailing_comma_not_allowed : DiagnosticMessage := ⟨1009, "Trailing comma not allowed."⟩
def asterisk_or_brace_expected : DiagnosticMessage := ⟨1136, "'*' or '{' expected."⟩
def import_require_string_literal : DiagnosticMessage := ⟨1141, "Import declaration in a namespace cannot reference a module."⟩
def export_or_import_expected : DiagnosticMessage := ⟨1142, "'{' or '*' or identifier expected."⟩
def enum_member_expected : DiagnosticMessage := ⟨1132, "Enum member expected."⟩
def private_identifiers_not_allowed : DiagnosticMessage := ⟨18016, "Private identifiers are not allowed outside class bodies."⟩
def private_identifiers_not_in_variables : DiagnosticMessage := ⟨18028, "Private identifiers are not allowed in variable declarations."⟩
def rest_parameter_cannot_be_optional : DiagnosticMessage := ⟨1047, "A rest parameter cannot be optional."⟩

end Diagnostics

end TSLean.Compiler
