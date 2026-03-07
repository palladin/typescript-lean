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
def unterminated_string_literal : DiagnosticMessage := ⟨1002, "Unterminated string literal."⟩
def invalid_use_of_0_in_strict_mode : DiagnosticMessage := ⟨1100, "Invalid use of '{0}' in strict mode."⟩
def with_statements_not_allowed_in_strict_mode : DiagnosticMessage := ⟨1101, "'with' statements are not allowed in strict mode."⟩
def continue_statement_only_within_iteration : DiagnosticMessage := ⟨1104, "A 'continue' statement can only be used within an enclosing iteration statement."⟩
def break_statement_only_within_iteration_or_switch : DiagnosticMessage := ⟨1105, "A 'break' statement can only be used within an enclosing iteration or switch statement."⟩
def unexpected_end_of_text : DiagnosticMessage := ⟨1126, "Unexpected end of text."⟩
def declaration_or_statement_expected : DiagnosticMessage := ⟨1128, "Declaration or statement expected."⟩
def statement_expected : DiagnosticMessage := ⟨1129, "Statement expected."⟩
def invalid_character : DiagnosticMessage := ⟨1127, "Invalid character."⟩
def case_or_default_expected : DiagnosticMessage := ⟨1130, "'case' or 'default' expected."⟩
def property_or_signature_expected : DiagnosticMessage := ⟨1131, "Property or signature expected."⟩
def expression_expected : DiagnosticMessage := ⟨1109, "Expression expected."⟩
def identifier_expected : DiagnosticMessage := ⟨1003, "Identifier expected."⟩
def statements_not_allowed_in_ambient_contexts : DiagnosticMessage := ⟨1036, "Statements are not allowed in ambient contexts."⟩
def ambient_enum_member_initializer_must_be_constant_expression : DiagnosticMessage := ⟨1066, "In ambient enum declarations member initializer must be constant expression."⟩
def variable_declaration_expected : DiagnosticMessage := ⟨1134, "Variable declaration expected."⟩
def argument_expression_expected : DiagnosticMessage := ⟨1135, "Argument expression expected."⟩
def parameter_declaration_expected : DiagnosticMessage := ⟨1138, "Parameter declaration expected."⟩
def type_parameter_declaration_expected : DiagnosticMessage := ⟨1139, "Type parameter declaration expected."⟩
def type_argument_expected : DiagnosticMessage := ⟨1140, "Type argument expected."⟩
def yield_expression_only_allowed_in_generator_body : DiagnosticMessage := ⟨1163, "A 'yield' expression is only allowed in a generator body."⟩
def initializers_not_allowed_in_ambient_contexts : DiagnosticMessage := ⟨1039, "Initializers are not allowed in ambient contexts."⟩
def type_expected : DiagnosticMessage := ⟨1110, "Type expected."⟩
def unterminated_regular_expression_literal : DiagnosticMessage := ⟨1161, "Unterminated regular expression literal."⟩
def object_member_cannot_be_declared_optional : DiagnosticMessage := ⟨1162, "An object member cannot be declared optional."⟩
def unexpected_token : DiagnosticMessage := ⟨1012, "Unexpected token."⟩
def modifier_must_precede_modifier : DiagnosticMessage := ⟨1029, "'{0}' modifier must precede '{1}' modifier."⟩
def unexpected_token_constructor : DiagnosticMessage := ⟨1068, "Unexpected token. A constructor, method, accessor, or property was expected."⟩
def property_assignment_expected : DiagnosticMessage := ⟨1136, "Property assignment expected."⟩
def expression_or_comma_expected : DiagnosticMessage := ⟨1137, "Expression or comma expected."⟩
def or_expected : DiagnosticMessage := ⟨1144, "'{' or ';' expected."⟩
def identifier_expected_reserved : DiagnosticMessage := ⟨1359, "Identifier expected. '{0}' is a reserved word that cannot be used here."⟩
def variable_declaration_name_not_allowed : DiagnosticMessage := ⟨1389, "'{0}' is not allowed as a variable declaration name."⟩
def parameter_name_not_allowed : DiagnosticMessage := ⟨1390, "'{0}' is not allowed as a parameter name."⟩
def function_type_parenthesized_union : DiagnosticMessage := ⟨1385, "Function type notation must be parenthesized when used in a union type."⟩
def constructor_type_parenthesized_union : DiagnosticMessage := ⟨1386, "Constructor type notation must be parenthesized when used in a union type."⟩
def function_type_parenthesized_intersection : DiagnosticMessage := ⟨1387, "Function type notation must be parenthesized when used in an intersection type."⟩
def constructor_type_parenthesized_intersection : DiagnosticMessage := ⟨1388, "Constructor type notation must be parenthesized when used in an intersection type."⟩
def keywords_cannot_contain_escape : DiagnosticMessage := ⟨1260, "Keywords cannot contain escape characters."⟩
def declaration_expected : DiagnosticMessage := ⟨1146, "Declaration expected."⟩
def trailing_comma_not_allowed : DiagnosticMessage := ⟨1009, "Trailing comma not allowed."⟩
def import_require_string_literal : DiagnosticMessage := ⟨1141, "Import declaration in a namespace cannot reference a module."⟩
def export_or_import_expected : DiagnosticMessage := ⟨1142, "'{' or '*' or identifier expected."⟩
def enum_member_expected : DiagnosticMessage := ⟨1132, "Enum member expected."⟩
def property_destructuring_pattern_expected : DiagnosticMessage := ⟨1180, "Property destructuring pattern expected."⟩
def array_element_destructuring_pattern_expected : DiagnosticMessage := ⟨1181, "Array element destructuring pattern expected."⟩
def unexpected_token_lbrace_expected : DiagnosticMessage := ⟨1179, "Unexpected token. '{' expected."⟩
def identifier_or_string_literal_expected : DiagnosticMessage := ⟨1478, "Identifier or string literal expected."⟩
def super_must_be_followed_by_an_argument_list_or_member_access : DiagnosticMessage := ⟨1034, "'super' must be followed by an argument list or member access."⟩
def private_identifiers_not_allowed : DiagnosticMessage := ⟨18016, "Private identifiers are not allowed outside class bodies."⟩
def private_identifiers_not_in_variables : DiagnosticMessage := ⟨18028, "Private identifiers are not allowed in variable declarations."⟩
def rest_parameter_cannot_be_optional : DiagnosticMessage := ⟨1047, "A rest parameter cannot be optional."⟩
def implementation_cannot_be_declared_in_ambient_contexts : DiagnosticMessage := ⟨1183, "An implementation cannot be declared in ambient contexts."⟩
def const_initializer_in_ambient_context_must_be_literal_or_enum_reference : DiagnosticMessage := ⟨1254, "A 'const' initializer in an ambient context must be a string or numeric literal or literal enum reference."⟩
def declarations_must_be_initialized : DiagnosticMessage := ⟨1155, "'{0}' declarations must be initialized."⟩
def with_statement_not_supported : DiagnosticMessage := ⟨2410, "The 'with' statement is not supported. All symbols in a 'with' block will have type 'any'."⟩
def unterminated_template_literal : DiagnosticMessage := ⟨1160, "Unterminated template literal."⟩

end Diagnostics

end TSLean.Compiler
