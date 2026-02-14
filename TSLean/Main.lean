import TSLean

def main (args : List String) : IO UInt32 := do
  match args with
  | [] =>
    IO.println "tslean: A Lean 4 port of the TypeScript compiler"
    IO.println "Usage: tslean <file.ts>"
    return 0
  | files =>
    for file in files do
      IO.println s!"TODO: compile {file}"
    return 0
