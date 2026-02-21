/-
  Playground — #eval scratch pad for testing the scanner and parser.

  Open this file in VS Code and hover over #eval to see results.
  Edit `code` to try different TypeScript snippets.
-/
import TSLean.Compiler

open TSLean.Compiler

-- ============================================================
-- Change this string to test different TypeScript code
-- ============================================================

def code := "const x: number = 42;"
def code2 := "const /* hi */ x = 1;"

-- ============================================================
-- Scanner: see all tokens
-- ============================================================

def scanner := Scanner.new |>.setText code2

#eval scanner.scan.scan.state

-- ============================================================
-- Parser: see the full AST and diagnostics
-- ============================================================

def parseResult := parseSourceFile "test.ts" code2 ScriptKind.ts

#eval  parseResult.result |> ppTree |> IO.println
