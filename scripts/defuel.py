#!/usr/bin/env python3
"""Remove fuel pattern from Parser.lean — make all mutual defs partial."""
import re, sys

def transform_parser(text):
    # 1. Remove maxHeartbeats
    text = text.replace("set_option maxHeartbeats 800000\n\n", "")

    # 2. Update header comment
    text = text.replace(
        "  Recursion control: iterative constructs use `loop`, which decrements\n"
        "  `Parser.fuel` only when recursing (the `none` path). When fuel reaches\n"
        "  zero, `ParseError.fuelExhausted` is thrown.\n",
        "  Uses `partial` for all recursive functions — no fuel needed.\n"
    )

    # 3. Remove fuel-related comments
    text = text.replace("-- Every function takes `fuel : Nat` for termination proof.\n", "")
    text = text.replace("-- Fuel decrements only at mutual call boundaries (match fuel+1 → fuel).\n", "")
    text = text.replace("-- Self-recursive iteration uses `loopFold` (bounded by state fuel).\n", "")

    # 4. Change `mutual` to `partial mutual`
    text = text.replace("\nmutual\n", "\npartial mutual\n")

    # 5. Remove (fuel : Nat) from function signatures — various positions
    # Pattern: def funcName (fuel : Nat) :
    text = re.sub(r'def (\w+) \(fuel : Nat\) :', r'def \1 :', text)
    # Pattern: def funcName (fuel : Nat) (other args
    text = re.sub(r'def (\w+) \(fuel : Nat\) \(', r'def \1 (', text)
    # Also _fuel
    text = re.sub(r'def (\w+) \(_fuel : Nat\) :', r'def \1 :', text)

    # 6. Remove the 3-line fuel match pattern (with do)
    # match fuel with
    #   | 0 => throw ParseError.fuelExhausted
    #   | fuel + 1 => do
    text = re.sub(
        r'  match fuel with\n\s*\| 0 => throw ParseError\.fuelExhausted\n\s*\| fuel \+ 1 => do\n',
        '  do\n',
        text
    )

    # 7. Remove the 3-line fuel match pattern (without do — used for loopFold calls)
    # match fuel with
    #   | 0 => throw ParseError.fuelExhausted
    #   | fuel + 1 =>
    #     loopFold ...
    text = re.sub(
        r'  match fuel with\n\s*\| 0 => throw ParseError\.fuelExhausted\n\s*\| fuel \+ 1 =>\n',
        '',
        text
    )

    # 8. Remove ` fuel` from call sites
    # Match " fuel" when followed by newline, space+something, or closing paren etc.
    # Be careful not to match "fuel" in other contexts
    # Pattern: functionName fuel\n or functionName fuel) or functionName fuel arg
    text = re.sub(r'(\w) fuel\b', r'\1', text)

    # 9. Fix entry point - remove ExceptT
    text = text.replace(
        "  let action : ParserM Node := do nextToken; parseSourceFileWorker fuel",
        "  let action : ParserM Node := do nextToken; parseSourceFileWorker"
    )
    text = text.replace(
        "  let (result, p) := ExceptT.run action |>.run p",
        "  let (result, p) := action |>.run p"
    )
    text = text.replace(
        "  match result with\n"
        "  | .ok node => { sourceFile := node, diagnostics := p.diagnostics }\n"
        "  | .error .fuelExhausted =>\n"
        "    { sourceFile := Node.missing {} Kind.unknown\n"
        "    , diagnostics := p.diagnostics\n"
        "    , fuelExhausted := true }",
        "  { sourceFile := result, diagnostics := p.diagnostics }"
    )

    # 10. Fix parseSourceFile signature - remove fuel param
    text = re.sub(
        r'def parseSourceFile \(_fileName : String\) \(sourceText : String\)\n\s*\(scriptKind : ScriptKind\) \(fuel : Nat\) : ParseResult :=',
        'def parseSourceFile (_fileName : String) (sourceText : String)\n    (scriptKind : ScriptKind) : ParseResult :=',
        text
    )

    # 11. Fix Parser.initializeState - remove fuel param
    text = re.sub(
        r'def Parser\.initializeState \(sourceText : String\) \(scriptKind : ScriptKind\)\n\s*\(fuel : Nat\) : Parser :=',
        'def Parser.initializeState (sourceText : String) (scriptKind : ScriptKind) : Parser :=',
        text
    )

    # 12. Fix initializeState call
    text = text.replace(
        "  let p := Parser.initializeState sourceText scriptKind fuel",
        "  let p := Parser.initializeState sourceText scriptKind"
    )

    # 13. Remove fuel from Parser struct init
    text = text.replace("  , fuel := fuel }", "}")

    # 14. Add loopFold definition before mutual block
    loopfold_def = '''
/-- Partial loop combinator with accumulator.
    Returns when `f` yields `.inr result`, continues on `.inl next`. -/
partial def loopFold [Monad m] (init : α) (f : α → m (α ⊕ α)) : m α := do
  match ← f init with
  | .inl next => loopFold next f
  | .inr result => return result

'''
    text = text.replace(
        "\npartial mutual\n",
        loopfold_def + "partial mutual\n"
    )

    return text


if __name__ == "__main__":
    path = sys.argv[1]
    with open(path) as f:
        text = f.read()
    text = transform_parser(text)
    with open(path, 'w') as f:
        f.write(text)
    print(f"Transformed {path}")
