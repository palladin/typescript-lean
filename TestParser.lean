/-
  Test runner for the TSLean parser — validates against the Go port's baselines.

  Compares only parse errors (TS1xxx) since we test the parser, not the
  full compiler. Type errors (TS2xxx), semantic errors (TS7xxx), etc.
  in the Go baselines are ignored.

  Usage:
    lake exe test_parser                          -- run all compiler tests
    lake exe test_parser path/to/test.ts          -- run a specific test
-/
import TSLean.Compiler
import TSLean.TestRunner

open TSLean.Compiler
open TSLean.TestRunner
open System (FilePath)

/-- Default path to Go port's test cases. -/
def testCasesDir : FilePath := "reference/typescript-go/testdata/tests/cases/compiler"

/-- Path to Go port's reference baselines (ground truth). -/
def goBaselineDir : FilePath := "reference/typescript-go/testdata/baselines/reference/compiler"

/-- Path to locally generated baselines (for inspection). -/
def localBaselineDir : FilePath := "testdata/baselines/local/compiler"

/-- Get the test name from a file path (strip directory and extension). -/
def testNameFromPath (path : String) : String :=
  let fileName := (path.splitOn "/").getLast!
  if fileName.endsWith ".tsx" then fileName.dropEnd 4 |>.toString
  else if fileName.endsWith ".ts" then fileName.dropEnd 3 |>.toString
  else fileName

/-- Infer ScriptKind from a unit filename. -/
def scriptKindFromFileName (fileName : String) : ScriptKind :=
  if fileName.endsWith ".tsx" then ScriptKind.tsx
  else if fileName.endsWith ".ts" then ScriptKind.ts
  else if fileName.endsWith ".jsx" then ScriptKind.jsx
  else if fileName.endsWith ".js" then ScriptKind.js
  else if fileName.endsWith ".json" then ScriptKind.json
  else ScriptKind.ts

/-- Read a file, returning empty string if it doesn't exist. -/
def readFileOrEmpty (path : FilePath) : IO String := do
  try
    return (← IO.FS.readFile path)
  catch _ =>
    return ""

/-- Check if a string contains a substring. -/
def hasSubstr (s sub : String) : Bool :=
  (s.splitOn sub).length > 1

/-- Extract parse error summary lines (parser diagnostics) from a baseline.
    Summary lines appear at the top before the first "====" section.
    Format: `filename(line,col): error TS1xxx: message` -/
def extractParseErrorSummary (baseline : String) : Array String :=
  let isParserDiagnosticLine (line : String) : Bool :=
    match line.splitOn "error TS" with
    | _ :: codeAndMsg :: _ =>
      let codeDigits := (codeAndMsg.splitOn ":").head!
      match codeDigits.toNat? with
      | some code =>
        code >= 1000 && code < 1200 &&
        -- TS1118/TS1119 are non-parser duplicate member checks.
        code != 1118 && code != 1119
      | none => false
    | _ => false
  let lines := baseline.splitOn "\n"
  let (_, summary) := lines.foldl (init := (false, #[])) fun (done, acc) line =>
    if done then
      (true, acc)
    else if line.startsWith "====" then
      (true, acc)
    else if isParserDiagnosticLine line then
      (false, acc.push line)
    else
      (false, acc)
  summary

/-- Normalize diagnostic summary line by dropping location prefix.
    E.g. `file.ts(1,2): error TS1005: ';' expected.` -> `error TS1005: ';' expected.` -/
def normalizeDiagnosticSummaryLine (line : String) : String :=
  let normalized :=
    match line.splitOn "): " with
    | _ :: rest =>
      if rest.isEmpty then line else "): ".intercalate rest
    | _ => line
  normalized.trimAscii.toString

/-- Concatenate baselines for multi-file tests. -/
private def concatBaselines (sources : Array (String × String))
    (diagnostics : Array Diagnostic) : String :=
  sources.foldl (init := "") fun acc (name, src) =>
    acc ++ generateErrorBaseline name src diagnostics

/-- Result of running a single test. -/
inductive TestResult where
  | pass : TestResult
  | fail (goParseErrors ourParseErrors : Array String) : TestResult

/-- Run a single test file. Compare parse errors only against Go port. -/
def runTest (testFilePath : String) : IO (String × TestResult) := do
  let testName := testNameFromPath testFilePath
  let initialUnitName := (testFilePath.splitOn "/").getLast!
  let content ← IO.FS.readFile testFilePath

  -- Parse test case directives (strips // @ lines from content)
  let testCase := parseTestFile initialUnitName content
  let hasNamedUnits := testCase.units.any fun unit => hasSubstr unit.name "."
  let hasMultipleUnits := testCase.units.size > 1

  -- Filter out non-TypeScript units (JSON files, etc.)
  let tsUnits := testCase.units.filter fun unit =>
    (unit.name.endsWith ".ts" || unit.name.endsWith ".tsx" ||
     unit.name.endsWith ".mts" || unit.name.endsWith ".cts" ||
     unit.name.endsWith ".js" || unit.name.endsWith ".jsx" ||
     unit.name.endsWith ".mjs" || unit.name.endsWith ".cjs" ||
    -- Keep extensionless initial unit only for single-file tests
    (!hasNamedUnits && !hasSubstr unit.name "."))
    && !(hasMultipleUnits && unit.name == initialUnitName)
    && unit.content.trimAscii.toString != "content not parsed"

  -- Parse each unit and collect results
  let parsed := tsUnits.map fun unit =>
    let scriptKind := scriptKindFromFileName unit.name
    let result := parseSourceFile unit.name unit.content scriptKind
    (unit.name, unit.content, result)

  let allDiagnostics := parsed.foldl (init := #[]) fun acc (_, _, result) =>
    acc ++ result.diagnostics

  let allSources := parsed.map fun (name, content, _) => (name, content)

  -- Generate our error baseline
  let baseline := if allSources.size == 1 then
    let (name, src) := allSources[0]!
    generateErrorBaseline name src allDiagnostics
  else
    concatBaselines allSources allDiagnostics

  -- Write local baseline for inspection
  let localPath : FilePath := s!"{localBaselineDir}/{testName}.errors.txt"
  IO.FS.writeFile localPath baseline

  -- Load Go port's baseline and extract parse errors only
  let goPath : FilePath := s!"{goBaselineDir}/{testName}.errors.txt"
  let goBaseline ← readFileOrEmpty goPath
  let goParseErrors := extractParseErrorSummary goBaseline
  let ourParseErrors := extractParseErrorSummary baseline
  let goNormalized := goParseErrors.map normalizeDiagnosticSummaryLine
  let ourNormalized := ourParseErrors.map normalizeDiagnosticSummaryLine

  -- Compare parse errors only
  let result := if goNormalized == ourNormalized then
    TestResult.pass
  else
    TestResult.fail goParseErrors ourParseErrors

  return (testName, result)

/-- Discover all .ts test files in a directory. -/
def discoverTestFiles (dir : FilePath) : IO (Array String) := do
  let entries ← try
    System.FilePath.readDir dir
  catch _ =>
    IO.println s!"Test directory not found: {dir}"
    return #[]
  let files := entries.filter fun entry =>
    entry.fileName.endsWith ".ts" || entry.fileName.endsWith ".tsx"
  let paths := files.map fun entry => s!"{dir}/{entry.fileName}"
  return paths.qsort (· < ·)

/-- Main entry point. -/
def main (args : List String) : IO UInt32 := do
  match args with
  | [path] =>
    if path.startsWith "--" then
      IO.println s!"Unknown option: {path}"
      IO.println "Usage: test_parser [path/to/test.ts]"
      return 1
    -- Run single test
    IO.FS.createDirAll localBaselineDir
    let (name, result) ← runTest path
    match result with
    | .pass => IO.println s!"PASS: {name}"; return 0
    | .fail goErrs ourErrs =>
      IO.println s!"FAIL: {name}"
      IO.println s!"  Go parse errors ({goErrs.size}):"
      for e in goErrs do IO.println s!"    {e}"
      IO.println s!"  Our parse errors ({ourErrs.size}):"
      for e in ourErrs do IO.println s!"    {e}"
      return 1
  | _ =>
    -- Run all tests
    IO.FS.createDirAll localBaselineDir
    let testFiles ← discoverTestFiles testCasesDir
    if testFiles.size == 0 then
      IO.println s!"No test files found in {testCasesDir}"
      return 1

    let total := testFiles.size
    let rec runAll
        (remaining : List String)
        (idx passCount failCount spuriousCount missingCount mismatchCount : Nat)
        (failures : Array String)
        : IO (Nat × Nat × Nat × Nat × Nat × Array String) := do
      match remaining with
      | [] =>
        return (passCount, failCount, spuriousCount, missingCount, mismatchCount, failures)
      | testFile :: rest =>
        let name := testNameFromPath testFile
        let stdout ← IO.getStdout
        IO.print s!"[{idx}/{total}] {name}... "
        stdout.flush
        let (name, result) ← runTest testFile
        match result with
        | .pass =>
          IO.println "PASS"
          runAll rest (idx + 1) (passCount + 1) failCount spuriousCount missingCount mismatchCount failures
        | .fail goErrs ourErrs =>
          if goErrs.size == 0 && ourErrs.size > 0 then
            IO.println s!"FAIL (spurious: {ourErrs.size} false parse errors)"
            runAll rest (idx + 1) passCount (failCount + 1) (spuriousCount + 1) missingCount mismatchCount (failures.push name)
          else if goErrs.size > 0 && ourErrs.size == 0 then
            IO.println s!"FAIL (missing: {goErrs.size} parse errors not reported)"
            runAll rest (idx + 1) passCount (failCount + 1) spuriousCount (missingCount + 1) mismatchCount (failures.push name)
          else
            IO.println s!"FAIL (mismatch: go={goErrs.size} ours={ourErrs.size})"
            runAll rest (idx + 1) passCount (failCount + 1) spuriousCount missingCount (mismatchCount + 1) (failures.push name)

    let (passCount, failCount, spuriousCount, missingCount, mismatchCount, failures) ←
      runAll testFiles.toList 1 0 0 0 0 0 #[]

    -- Print summary
    IO.println ""
    IO.println "=== Test Summary (parse errors vs Go port) ==="
    IO.println s!"  Total:    {testFiles.size}"
    IO.println s!"  Pass:     {passCount} ({passCount * 100 / testFiles.size}%)"
    IO.println s!"  Fail:     {failCount}"
    if failCount > 0 then
      IO.println s!"    Spurious: {spuriousCount} (we emit parse errors, Go doesn't)"
      IO.println s!"    Missing:  {missingCount} (Go has parse errors, we don't)"
      IO.println s!"    Mismatch: {mismatchCount} (both emit but different)"

    if failures.size > 0 && failures.size <= 20 then
      IO.println ""
      IO.println "Failed tests:"
      for name in failures do
        IO.println s!"  - {name}"

    return if failCount > 0 then 1 else 0
