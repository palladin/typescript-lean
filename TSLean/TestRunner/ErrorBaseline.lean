/-
  TSLean.TestRunner.ErrorBaseline — Generate .errors.txt baseline files.

  Based on Go: internal/testutil/tsbaseline/error_baseline.go
  Generates error baselines in the same format as the TypeScript compiler test suite.
-/
import TSLean.Compiler

namespace TSLean.TestRunner

open TSLean.Compiler

/-- Convert Int32 position to Nat (clamping negatives to 0). -/
private def posToNat (p : Int32) : Nat :=
  if p < 0 then 0 else p.toInt.toNat

/-- Compute byte positions where each line starts.
    Based on Go: scanner.go (ComputeLineStarts) -/
def computeLineStarts (text : String) : Array Nat :=
  let bytes := text.toUTF8
  let rec go (i : Nat) (acc : Array Nat) : Array Nat :=
    if i >= bytes.size then acc
    else
      let b := bytes[i]!
      if b == 10 then -- '\n'
        go (i + 1) (acc.push (i + 1))
      else if b == 13 then -- '\r'
        if i + 1 < bytes.size && bytes[i + 1]! == 10 then
          go (i + 2) (acc.push (i + 2))
        else
          go (i + 1) (acc.push (i + 1))
      else
        go (i + 1) acc
  go 0 #[0]

/-- Convert a byte offset to (line, col), both 0-based.
    Based on Go: error_baseline.go (uses line starts for position mapping) -/
def positionToLineAndCol (lineStarts : Array Nat) (pos : Nat) : Nat × Nat :=
  -- Binary search for the line containing pos
  let rec go (lo hi : Nat) : Nat × Nat :=
    if lo + 1 >= hi then (lo, pos - lineStarts[lo]!)
    else
      let mid := (lo + hi) / 2
      if lineStarts[mid]! <= pos then go mid hi
      else go lo mid
  go 0 lineStarts.size

/-- Substitute `{0}`, `{1}`, etc. in a diagnostic message template.
    Based on Go: diagnostics formatting -/
def formatDiagnosticMessage (template : String) (args : Array String) : String :=
  let rec go (i : Nat) (result : String) : String :=
    if i >= args.size then result
    else go (i + 1) (result.replace s!"\{{i}}" args[i]!)
  go 0 template

/-- Get lines of source text. -/
private def getSourceLines (text : String) : Array String :=
  let lines := text.splitOn "\n"
  lines.toArray.map fun line =>
    if line.endsWith "\r" then (line.dropEnd 1).toString else line

/-- Generate the summary header — one line per diagnostic.
    Based on Go: error_baseline.go (FormatDiagnostics) -/
private def generateSummary (fileName : String) (lineStarts : Array Nat)
    (diags : Array Diagnostic) : String :=
  diags.foldl (init := "") fun acc diag =>
    let pos := posToNat diag.loc.pos
    let (line, col) := positionToLineAndCol lineStarts pos
    let msg := formatDiagnosticMessage diag.message.message diag.args
    acc ++ s!"{fileName}({line + 1},{col + 1}): error TS{diag.message.code}: {msg}\n"

/-- Generate squiggles and error messages for diagnostics on a given source line.
    Based on Go: error_baseline.go (iterateErrorBaseline, per-line error annotation) -/
private def annotateLine (lineStart lineEnd : Nat) (diags : Array Diagnostic) : String :=
  diags.foldl (init := "") fun acc diag =>
    let diagStart := posToNat diag.loc.pos
    let diagEnd := posToNat diag.loc.end_
    if diagStart >= lineStart && diagStart < lineEnd then
      let col := diagStart - lineStart
      let width := if diagEnd <= diagStart then 1
                   else if diagEnd <= lineEnd then diagEnd - diagStart
                   else lineEnd - diagStart
      let spaces := String.ofList (List.replicate (4 + col) ' ')
      let squiggles := String.ofList (List.replicate width '~')
      let msg := formatDiagnosticMessage diag.message.message diag.args
      acc ++ spaces ++ squiggles ++ "\n" ++
        s!"!!! error TS{diag.message.code}: {msg}\n"
    else acc

/-- Generate the annotated source section.
    Based on Go: error_baseline.go (iterateErrorBaseline, per-file section) -/
private def generateAnnotatedSource (sourceLines : Array String) (lineStarts : Array Nat)
    (textSize : Nat) (diags : Array Diagnostic) : String :=
  let rec go (lineIdx : Nat) (acc : String) : String :=
    if lineIdx >= sourceLines.size then acc
    else
      let line := sourceLines[lineIdx]!
      let lineStart := lineStarts[lineIdx]!
      let lineEnd := if lineIdx + 1 < lineStarts.size then lineStarts[lineIdx + 1]!
                     else textSize
      let acc := acc ++ "    " ++ line ++ "\n"
      let acc := acc ++ annotateLine lineStart lineEnd diags
      go (lineIdx + 1) acc
  go 0 ""

/-- Generate the `.errors.txt` baseline content.
    Based on Go: internal/testutil/tsbaseline/error_baseline.go (iterateErrorBaseline)

    Format:
    ```
    filename(line,col): error TScode: message

    ==== filename (N errors) ====
        <source line>
        ~~~~
    !!! error TScode: message
    ``` -/
def generateErrorBaseline (fileName : String) (sourceText : String)
    (diagnostics : Array Diagnostic) : String :=
  if diagnostics.size == 0 then ""
  else
    let lineStarts := computeLineStarts sourceText
    let sourceLines := getSourceLines sourceText
    let sortedDiags := diagnostics.qsort fun a b => a.loc.pos < b.loc.pos
    let summary := generateSummary fileName lineStarts sortedDiags
    let errCount := sortedDiags.size
    let plural := if errCount != 1 then "s" else ""
    let header := s!"==== {fileName} ({errCount} error{plural}) ====\n"
    let body := generateAnnotatedSource sourceLines lineStarts sourceText.toUTF8.size sortedDiags
    summary ++ "\n" ++ header ++ body

end TSLean.TestRunner
