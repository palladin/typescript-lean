-- TestParserMain: Test harness that runs TypeScript conformance tests
-- through our scanner/parser and reports results.

import TSLean
import TSLean.Parser.Parser

open TSLean.Parser
open TSLean.Ast
open TSLean.Diagnostics

-- ============================================================================
-- Helper: lowercase a string (Lean 4.27 compatible)
-- ============================================================================

private def String.toLowerAscii (s : String) : String :=
  s.map Char.toLower

-- ============================================================================
-- Test case parsing: extract // @ directives from test file headers
-- ============================================================================

structure TestDirectives where
  target : Array String := #[]
  module_ : Array String := #[]
  noEmit : Bool := false
  other : Array (String × String) := #[]

private def parseDirectives (content : String) : TestDirectives := Id.run do
  let mut dirs : TestDirectives := {}
  for line in content.splitOn "\n" do
    let line := line.trimAscii.toString
    if !line.startsWith "//" then break
    if line.startsWith "// @" then
      let rest := (line.drop 4).trimAscii.toString
      match rest.splitOn ":" with
      | [key, value] =>
        let key := key.trimAscii.toString.toLowerAscii
        let value := value.trimAscii.toString
        if key == "target" then
          dirs := { dirs with target := (value.splitOn ",").map (·.trimAscii.toString) |>.toArray }
        else if key == "module" then
          dirs := { dirs with module_ := (value.splitOn ",").map (·.trimAscii.toString) |>.toArray }
        else if key == "noemit" then
          dirs := { dirs with noEmit := value.toLowerAscii == "true" }
        else
          dirs := { dirs with other := dirs.other.push (key, value) }
      | _ => pure ()
  return dirs

-- ============================================================================
-- Error baseline generation
-- ============================================================================

/-- Build a line-start offset table for fast line/col lookups. -/
private def buildLineStarts (content : String) : Array Nat := Id.run do
  let mut starts : Array Nat := #[0]
  let mut i := 0
  for c in content.toList do
    i := i + 1
    if c == '\n' then starts := starts.push i
  return starts

private def posToLineCol (lineStarts : Array Nat) (pos : Nat) : Nat × Nat := Id.run do
  -- Binary search for the line
  let mut lo := 0
  let mut hi := lineStarts.size
  while lo + 1 < hi do
    let mid := (lo + hi) / 2
    if lineStarts[mid]! <= pos then lo := mid
    else hi := mid
  return (lo, pos - lineStarts[lo]!)

private def categoryStr (cat : DiagnosticCategory) : String :=
  match cat with
  | .error => "error"
  | .warning => "warning"
  | .suggestion => "suggestion"
  | .message => "message"

/-- Format diagnostics in TypeScript .errors.txt baseline format.
    Pre-computes line/col in one pass for efficiency. -/
private def formatErrorBaseline (fileName : String) (content : String)
    (diagnostics : Array Diagnostic) : String := Id.run do
  let lineStarts := buildLineStarts content
  let lines := content.splitOn "\n"
  let errorCount := diagnostics.filter (·.category == .error) |>.size
  let mut parts : Array String := #[]

  -- Pre-compute line/col for each diagnostic
  let diagInfo := diagnostics.map fun diag =>
    let (line, col) := posToLineCol lineStarts diag.start.toNat
    (diag, line, col)

  -- Header lines
  for (diag, line, col) in diagInfo do
    parts := parts.push s!"{fileName}({line + 1},{col + 1}): {categoryStr diag.category} TS{diag.code}: {diag.messageText}\n"

  parts := parts.push "\n\n"
  parts := parts.push s!"==== {fileName} ({errorCount} errors) ====\n"

  -- Source lines with annotations
  let mut lineIdx := 0
  for line in lines do
    parts := parts.push s!"    {line}\n"
    for (diag, diagLine, col) in diagInfo do
      if diagLine == lineIdx then
        let len := diag.length.toNat
        let padding := String.ofList (List.replicate (col + 4) ' ')
        let squiggles := String.ofList (List.replicate (max len 1) '~')
        parts := parts.push (padding ++ squiggles ++ "\n")
        parts := parts.push s!"!!! {categoryStr diag.category} TS{diag.code}: {diag.messageText}\n"
    lineIdx := lineIdx + 1

  return String.join parts.toList

-- ============================================================================
-- Baseline comparison: count errors in reference .errors.txt
-- ============================================================================

/-- Count the number of "!!! error" lines in a reference baseline.
    This gives us the total error count from the official tsc. -/
def countRefErrors (baseline : String) : Nat := Id.run do
  let mut count := 0
  for line in baseline.splitOn "\n" do
    let trimmed := line.trimAscii.toString
    if trimmed.startsWith "!!! error" then
      count := count + 1
  return count

-- ============================================================================
-- Test runner
-- ============================================================================

structure TestResult where
  testName : String
  parsed : Bool
  crashed : Bool
  errorCount : Nat
  errorMessage : Option String

inductive TestMode where
  | parseOnly
  | errorBaseline
  deriving BEq

def runSingleTest (testName : String) (content : String) : IO TestResult := do
  match parseSourceFile testName content with
  | .ok (_, diagnostics) =>
    return {
      testName
      parsed := true
      crashed := false
      errorCount := diagnostics.size
      errorMessage := none
    }
  | .error msg =>
    return {
      testName
      parsed := false
      crashed := true
      errorCount := 0
      errorMessage := some msg
    }

partial def findTsFiles (dir : System.FilePath) : IO (Array System.FilePath) := do
  let mut files : Array System.FilePath := #[]
  let entries ← dir.readDir
  for entry in entries do
    if ← entry.path.isDir then
      let subFiles ← findTsFiles entry.path
      files := files ++ subFiles
    else
      let ext := entry.path.extension.getD ""
      if ext == "ts" || ext == "tsx" then
        files := files.push entry.path
  return files

/-- Get the test name: filename minus .ts/.tsx extension. -/
def testNameFromPath (path : System.FilePath) : String :=
  let name := path.fileName.getD ""
  if name.endsWith ".tsx" then (name.dropEnd 4).toString
  else if name.endsWith ".ts" then (name.dropEnd 3).toString
  else name

-- ============================================================================
-- Main entry point
-- ============================================================================

def main (args : List String) : IO UInt32 := do
  let mode := if args.contains "--errors" then TestMode.errorBaseline else TestMode.parseOnly

  let tsTestBase : System.FilePath := "testdata/TypeScript/tests"
  let scannerTests := tsTestBase / "cases" / "conformance" / "scanner"
  let parserTests := tsTestBase / "cases" / "conformance" / "parser"
  let compilerTests := tsTestBase / "cases" / "compiler"
  let refBaselineDir := tsTestBase / "baselines" / "reference"

  unless ← scannerTests.pathExists do
    IO.eprintln "Error: TypeScript test files not found."
    IO.eprintln "Run: bash scripts/fetch-tests.sh"
    return 1

  let filterArg := args.filter (· != "--errors") |>.filter (· != "--verbose")
  let verbose := args.contains "--verbose"

  let testDirs ← if filterArg.isEmpty then do
    pure #[scannerTests, parserTests]
  else
    let mut dirs : Array System.FilePath := #[]
    for arg in filterArg do
      if arg == "scanner" then dirs := dirs.push scannerTests
      else if arg == "parser" then dirs := dirs.push parserTests
      else if arg == "compiler" then dirs := dirs.push compilerTests
      else if arg == "all" then dirs := dirs ++ #[scannerTests, parserTests, compilerTests]
      else if !arg.startsWith "--" then
        dirs := dirs.push (tsTestBase / "cases" / arg)
    pure dirs

  let mut allFiles : Array System.FilePath := #[]
  for dir in testDirs do
    if ← dir.pathExists then
      let files ← findTsFiles dir
      allFiles := allFiles ++ files

  IO.println s!"Found {allFiles.size} test files"
  if mode == .errorBaseline then
    IO.println "Mode: error baseline comparison"
  IO.println ""

  -- Run tests
  let mut passed := 0
  let mut failed := 0
  let mut crashed := 0
  let mut totalDiags := 0
  let mut crashMessages : Array (String × String) := #[]
  let mut testIdx := 0
  let total := allFiles.size

  -- Baseline stats
  let mut errorCountMatch := 0
  let mut errorCountMismatch := 0
  let mut cleanMatch := 0
  let mut falsePositive := 0
  let mut falseMissing := 0
  let mut mismatchDetails : Array (String × Nat × Nat) := #[]

  for file in allFiles do
    testIdx := testIdx + 1
    let testName := testNameFromPath file
    IO.print s!"\r  [{testIdx}/{total}] {testName}                              "
    (← IO.getStdout).flush
    let contentResult ← try
      pure (some (← IO.FS.readFile file))
    catch _ =>
      pure none
    let some content := contentResult | do
      -- Skip non-UTF-8 files
      if verbose then IO.println s!"\n  SKIP   {testName}: non-UTF-8"
      continue
    let result ← runSingleTest testName content

    if result.crashed then
      crashed := crashed + 1
      let msg := result.errorMessage.getD "unknown"
      crashMessages := crashMessages.push (testName, msg)
      if verbose then
        IO.println s!"\n  CRASH  {testName}: {msg}"
    else if result.parsed then
      passed := passed + 1
      totalDiags := totalDiags + result.errorCount
      if verbose && result.errorCount > 0 && mode != .errorBaseline then
        IO.println s!"\n  PARSE  {testName} ({result.errorCount} diagnostics)"
    else
      failed := failed + 1
      if verbose then
        IO.println s!"\n  FAIL   {testName}"

    -- Baseline comparison
    if mode == .errorBaseline && result.parsed then
      let refPath := refBaselineDir / s!"{testName}.errors.txt"
      let refExists ← refPath.pathExists
      if refExists then
        let refContent ← IO.FS.readFile refPath
        let refCount := countRefErrors refContent
        if result.errorCount == 0 && refCount > 0 then
          falseMissing := falseMissing + 1
          if verbose then
            IO.println s!"\n  MISS   {testName}: ref={refCount} ours=0"
        else if result.errorCount == refCount then
          errorCountMatch := errorCountMatch + 1
        else
          errorCountMismatch := errorCountMismatch + 1
          if mismatchDetails.size < 20 then
            mismatchDetails := mismatchDetails.push (testName, refCount, result.errorCount)
          if verbose then
            IO.println s!"\n  DIFF   {testName}: ref={refCount} ours={result.errorCount}"
      else
        if result.errorCount == 0 then
          cleanMatch := cleanMatch + 1
        else
          falsePositive := falsePositive + 1
          if verbose then
            IO.println s!"\n  EXTRA  {testName}: we emit {result.errorCount}, ref clean"

      -- Write our baseline
      match parseSourceFile testName content with
      | .ok (_, diagnostics) =>
        if diagnostics.size > 0 then
          let baseline := formatErrorBaseline (testName ++ ".ts") content diagnostics
          let outDir : System.FilePath := "testdata" / "baselines" / "local"
          IO.FS.createDirAll outDir
          IO.FS.writeFile (outDir / s!"{testName}.errors.txt") baseline
      | .error _ => pure ()

  -- Summary
  IO.println ""
  IO.println ""
  IO.println "============================================"
  IO.println s!"  Total:   {allFiles.size}"
  IO.println s!"  Parsed:  {passed} ({passed * 100 / max allFiles.size 1}%)"
  IO.println s!"  Crashed: {crashed}"
  IO.println s!"  Diagnostics emitted: {totalDiags}"
  IO.println "============================================"

  if mode == .errorBaseline then
    IO.println ""
    IO.println "Baseline comparison (error count):"
    IO.println s!"  Exact match:     {errorCountMatch}"
    IO.println s!"  Count mismatch:  {errorCountMismatch}"
    IO.println s!"  Clean match:     {cleanMatch} (both agree: 0 errors)"
    IO.println s!"  False positive:  {falsePositive} (we emit errors, ref clean)"
    IO.println s!"  Missing errors:  {falseMissing} (ref has errors, we have 0)"
    let totalCompared := errorCountMatch + errorCountMismatch + cleanMatch + falsePositive + falseMissing
    if totalCompared > 0 then
      let accuracy := (errorCountMatch + cleanMatch) * 100 / totalCompared
      IO.println s!"  Accuracy:        {accuracy}%"

    if mismatchDetails.size > 0 then
      IO.println ""
      IO.println "Sample mismatches (ref vs ours):"
      for (name, refN, ourN) in mismatchDetails do
        IO.println s!"  {name}: ref={refN} ours={ourN}"

  if crashMessages.size > 0 then
    IO.println ""
    IO.println "First crash messages:"
    let showCount := min crashMessages.size 10
    for i in [:showCount] do
      let (name, msg) := crashMessages[i]!
      IO.println s!"  {name}: {msg}"
    if crashMessages.size > 10 then
      IO.println s!"  ... and {crashMessages.size - 10} more"

  if crashed > 0 then return 1
  return 0
