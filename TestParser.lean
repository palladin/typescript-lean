/-
  Test runner for the TSLean parser — mirrors the Go port's test infrastructure.

  Based on Go: internal/testrunner/compiler_runner.go
  Discovers .ts test files, parses them, generates .errors.txt baselines,
  and compares against reference baselines.

  Usage:
    lake exe test_parser                          -- run all compiler tests
    lake exe test_parser --accept                  -- accept local baselines as reference
    lake exe test_parser path/to/test.ts           -- run a specific test
-/
import TSLean.Compiler
import TSLean.TestRunner

open TSLean.Compiler
open TSLean.TestRunner
open System (FilePath)

/-- Default path to Go port's test cases. -/
def testCasesDir : FilePath := "reference/typescript-go/testdata/tests/cases/compiler"

/-- Path to our reference baselines. -/
def referenceBaselineDir : FilePath := "testdata/baselines/reference/compiler"

/-- Path to locally generated baselines. -/
def localBaselineDir : FilePath := "testdata/baselines/local/compiler"

/-- Get the test name from a file path (strip directory and extension). -/
def testNameFromPath (path : String) : String :=
  let fileName := (path.splitOn "/").getLast!
  if fileName.endsWith ".tsx" then fileName.dropEnd 4 |>.toString
  else if fileName.endsWith ".ts" then fileName.dropEnd 3 |>.toString
  else fileName

/-- Read a file, returning empty string if it doesn't exist. -/
def readFileOrEmpty (path : FilePath) : IO String := do
  try
    return (← IO.FS.readFile path)
  catch _ =>
    return ""

/-- Concatenate baselines for multi-file tests. -/
private def concatBaselines (sources : Array (String × String))
    (diagnostics : Array Diagnostic) : String :=
  sources.foldl (init := "") fun acc (name, src) =>
    acc ++ generateErrorBaseline name src diagnostics

/-- Result of running a single test. -/
inductive TestResult where
  | pass : TestResult
  | fail (expected actual : String) : TestResult
  | new_ (baseline : String) : TestResult

/-- Run a single test file.
    Based on Go: compiler_runner.go (runSingleConfigTest) -/
def runTest (testFilePath : String) : IO (String × TestResult) := do
  let testName := testNameFromPath testFilePath
  let content ← IO.FS.readFile testFilePath

  -- Parse test case directives (strips // @ lines from content)
  let testCase := parseTestFile testName content

  -- Parse each unit and collect results
  let parsed := testCase.units.map fun unit =>
    let result := parseSourceFile unit.name unit.content ScriptKind.ts
    (unit.name, unit.content, result)

  let allDiagnostics := parsed.foldl (init := #[]) fun acc (_, _, result) =>
    acc ++ result.diagnostics

  let allSources := parsed.map fun (name, content, _) => (name, content)

  -- Generate error baseline
  let baseline := if allSources.size == 1 then
    let (name, src) := allSources[0]!
    generateErrorBaseline name src allDiagnostics
  else
    concatBaselines allSources allDiagnostics

  -- Write local baseline (write even if empty, for comparison)
  let localPath : FilePath := s!"{localBaselineDir}/{testName}.errors.txt"
  IO.FS.writeFile localPath baseline

  -- Compare with reference baseline
  let refPath : FilePath := s!"{referenceBaselineDir}/{testName}.errors.txt"
  let reference ← readFileOrEmpty refPath

  let result := if baseline == reference then
    TestResult.pass
  else if reference == "" && !(baseline == "") then
    TestResult.new_ baseline
  else
    TestResult.fail reference baseline

  return (testName, result)

/-- Accept local baselines as reference (copy local → reference).
    Based on Go: baseline management -/
def acceptBaselines : IO Unit := do
  IO.FS.createDirAll referenceBaselineDir
  let entries ← try
    System.FilePath.readDir localBaselineDir
  catch _ =>
    IO.println "No local baselines to accept."
    return


  let mut count : Nat := 0
  for entry in entries do
    let name := entry.fileName
    if name.endsWith ".errors.txt" then
      let src : FilePath := s!"{localBaselineDir}/{name}"
      let dst : FilePath := s!"{referenceBaselineDir}/{name}"
      let content ← IO.FS.readFile src
      IO.FS.writeFile dst content
      count := count + 1

  IO.println s!"Accepted {count} baselines."

/-- Discover all .ts test files in a directory.
    Based on Go: compiler_runner.go (EnumerateFiles) -/
def discoverTestFiles (dir : FilePath) : IO (Array String) := do
  let entries ← try
    System.FilePath.readDir dir
  catch _ =>
    IO.println s!"Test directory not found: {dir}"
    return #[]
  let files := entries.filter fun entry =>
    entry.fileName.endsWith ".ts" || entry.fileName.endsWith ".tsx"
  let paths := files.map fun entry => s!"{dir}/{entry.fileName}"
  -- Sort for deterministic order
  return paths.qsort (· < ·)

/-- Main entry point.
    Based on Go: compiler_runner.go (RunTests) -/
def main (args : List String) : IO UInt32 := do
  match args with
  | ["--accept"] =>
    acceptBaselines
    return 0
  | [path] =>
    if path.startsWith "--" then
      IO.println s!"Unknown option: {path}"
      IO.println "Usage: test_parser [--accept | path/to/test.ts]"
      return 1
    -- Run single test
    IO.FS.createDirAll localBaselineDir
    let (name, result) ← runTest path
    match result with
    | .pass => IO.println s!"PASS: {name}"; return 0
    | .new_ baseline =>
      IO.println s!"NEW:  {name}"
      IO.println "  (no reference baseline — run with --accept to accept)"
      IO.println baseline
      return 1
    | .fail _expected actual =>
      IO.println s!"FAIL: {name}"
      IO.println "  Actual (local):"
      IO.println actual
      return 1
  | _ =>
    -- Run all tests
    IO.FS.createDirAll localBaselineDir
    let testFiles ← discoverTestFiles testCasesDir
    if testFiles.size == 0 then
      IO.println s!"No test files found in {testCasesDir}"
      return 1

    let mut passCount : Nat := 0
    let mut failCount : Nat := 0
    let mut newCount : Nat := 0
    let mut failures : Array String := #[]

    let total := testFiles.size
    for testFile in testFiles do
      let idx := passCount + failCount + newCount + 1
      let name := testNameFromPath testFile
      IO.println s!"[{idx}/{total}] Parsing {name}..."
      let stdout ← IO.getStdout
      stdout.flush
      let (name, result) ← runTest testFile
      match result with
      | .pass =>
        IO.println s!"[{idx}/{total}] PASS: {name}"
        passCount := passCount + 1
      | .new_ _ =>
        IO.println s!"[{idx}/{total}] NEW:  {name}"
        newCount := newCount + 1
      | .fail _ _ =>
        IO.println s!"[{idx}/{total}] FAIL: {name}"
        failCount := failCount + 1
        failures := failures.push name

    -- Print summary
    IO.println ""
    IO.println "=== Test Summary ==="
    IO.println s!"  Total:  {testFiles.size}"
    IO.println s!"  Pass:   {passCount}"
    IO.println s!"  Fail:   {failCount}"
    IO.println s!"  New:    {newCount}"

    if failCount > 0 then
      IO.println ""
      IO.println "Failed tests:"
      for name in failures do
        IO.println s!"  - {name}"

    if newCount > 0 then
      IO.println ""
      IO.println s!"{newCount} new baseline(s) — run with --accept to accept."

    return if failCount > 0 then 1 else 0
