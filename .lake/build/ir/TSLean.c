// Lean compiler output
// Module: TSLean
// Imports: public import Init public import TSLean.Core.TextRange public import TSLean.Ast.SyntaxKind public import TSLean.Ast.Flags public import TSLean.Ast.NodeData public import TSLean.Ast.Ast public import TSLean.Ast.Symbol public import TSLean.Diagnostics.Category public import TSLean.Scanner.CharCodes public import TSLean.Scanner.Keywords public import TSLean.Scanner.Scanner public import TSLean.Parser.ParserContext public import TSLean.Parser.Parser
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_typescript_x2dlean_TSLean_Core_TextRange(uint8_t builtin);
lean_object* initialize_typescript_x2dlean_TSLean_Ast_SyntaxKind(uint8_t builtin);
lean_object* initialize_typescript_x2dlean_TSLean_Ast_Flags(uint8_t builtin);
lean_object* initialize_typescript_x2dlean_TSLean_Ast_NodeData(uint8_t builtin);
lean_object* initialize_typescript_x2dlean_TSLean_Ast_Ast(uint8_t builtin);
lean_object* initialize_typescript_x2dlean_TSLean_Ast_Symbol(uint8_t builtin);
lean_object* initialize_typescript_x2dlean_TSLean_Diagnostics_Category(uint8_t builtin);
lean_object* initialize_typescript_x2dlean_TSLean_Scanner_CharCodes(uint8_t builtin);
lean_object* initialize_typescript_x2dlean_TSLean_Scanner_Keywords(uint8_t builtin);
lean_object* initialize_typescript_x2dlean_TSLean_Scanner_Scanner(uint8_t builtin);
lean_object* initialize_typescript_x2dlean_TSLean_Parser_ParserContext(uint8_t builtin);
lean_object* initialize_typescript_x2dlean_TSLean_Parser_Parser(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_typescript_x2dlean_TSLean(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_typescript_x2dlean_TSLean_Core_TextRange(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_typescript_x2dlean_TSLean_Ast_SyntaxKind(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_typescript_x2dlean_TSLean_Ast_Flags(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_typescript_x2dlean_TSLean_Ast_NodeData(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_typescript_x2dlean_TSLean_Ast_Ast(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_typescript_x2dlean_TSLean_Ast_Symbol(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_typescript_x2dlean_TSLean_Diagnostics_Category(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_typescript_x2dlean_TSLean_Scanner_CharCodes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_typescript_x2dlean_TSLean_Scanner_Keywords(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_typescript_x2dlean_TSLean_Scanner_Scanner(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_typescript_x2dlean_TSLean_Parser_ParserContext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_typescript_x2dlean_TSLean_Parser_Parser(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
