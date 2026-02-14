-- TSLean: A Lean 4 port of the TypeScript compiler

import TSLean.Core.TextRange
import TSLean.Ast.SyntaxKind
import TSLean.Ast.Flags
import TSLean.Ast.NodeData
import TSLean.Ast.Ast
import TSLean.Ast.Symbol
import TSLean.Diagnostics.Category
import TSLean.Scanner.CharCodes
import TSLean.Scanner.Keywords
import TSLean.Scanner.Scanner
import TSLean.Parser.ParserContext
import TSLean.Parser.Parser
