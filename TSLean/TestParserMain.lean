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

/-- Format diagnostics in TypeScript .errors.txt baseline format. -/
private def formatErrorBaseline (fileName : String) (content : String)
    (diagnostics : Array Diagnostic) : String := Id.run do
  let lines := content.splitOn "\n"
  let errorCount := diagnostics.filter (·.category == .error) |>.size
  let mut output := ""

  -- File header with error count
  output := output ++ s!"==== {fileName} ({errorCount} errors) ====\n"

  -- For each source line, output it and any diagnostics that point to it
  let mut lineIdx := 0
  for line in lines do
    output := output ++ s!"    {line}\n"
    -- Find diagnostics on this line
    for diag in diagnostics do
      let diagLine := getLineOfPos content diag.start.toNat
      if diagLine == lineIdx then
        let col := getColumnOfPos content diag.start.toNat
        let len := diag.length.toNat
        let padding := String.ofList (List.replicate (col + 4) ' ')
        let squiggles := String.ofList (List.replicate (max len 1) '~')
        output := output ++ padding ++ squiggles ++ "\n"
        let cat := match diag.category with
          | .error => "error"
          | .warning => "warning"
          | .suggestion => "suggestion"
          | .message => "message"
        output := output ++ s!"!!! {cat} TS{diag.code}: {diag.messageText}\n"
    lineIdx := lineIdx + 1

  return output
where
  getLineOfPos (content : String) (pos : Nat) : Nat := Id.run do
    let mut line := 0
    let mut i := 0
    for c in content.toList do
      if i >= pos then return line
      if c == '\n' then line := line + 1
      i := i + 1
    return line
  getColumnOfPos (content : String) (pos : Nat) : Nat := Id.run do
    let mut col := 0
    let mut i := 0
    for c in content.toList do
      if i >= pos then return col
      if c == '\n' then col := 0
      else col := col + 1
      i := i + 1
    return col

-- ============================================================================
-- Test runner
-- ============================================================================

structure TestResult where
  testName : String
  parsed : Bool      -- parsed without Except error (may have diagnostics)
  crashed : Bool     -- Except.error was returned
  errorCount : Nat   -- number of diagnostics
  errorMessage : Option String  -- crash message if any

inductive TestMode where
  | parseOnly       -- just check if parsing succeeds
  | errorBaseline   -- generate and compare .errors.txt
  deriving BEq

/-- Run a single test: parse the file and return the result. -/
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

/-- Discover all .ts files recursively in a directory. -/
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

/-- Get just the test name from a file path (without directory and extension). -/
def testNameFromPath (path : System.FilePath) : String :=
  let name := path.fileName.getD ""
  match name.splitOn "." with
  | [] => name
  | parts => parts.head!

-- ============================================================================
-- Main entry point
-- ============================================================================

def main (args : List String) : IO UInt32 := do
  let mode := if args.contains "--errors" then TestMode.errorBaseline else TestMode.parseOnly

  -- Determine test directories
  let tsTestBase : System.FilePath := "testdata/TypeScript/tests"
  let scannerTests := tsTestBase / "cases" / "conformance" / "scanner"
  let parserTests := tsTestBase / "cases" / "conformance" / "parser"

  -- Check test files exist
  unless ← scannerTests.pathExists do
    IO.eprintln "Error: TypeScript test files not found."
    IO.eprintln "Run: bash scripts/fetch-tests.sh"
    return 1

  -- Find all test files
  let filterArg := args.filter (· != "--errors") |>.filter (· != "--verbose")
  let verbose := args.contains "--verbose"

  let testDirs ← if filterArg.isEmpty then do
    -- Default: run scanner + parser conformance
    pure #[scannerTests, parserTests]
  else
    -- Filter by category
    let mut dirs : Array System.FilePath := #[]
    for arg in filterArg do
      if arg == "scanner" then dirs := dirs.push scannerTests
      else if arg == "parser" then dirs := dirs.push parserTests
      else if !arg.startsWith "--" then
        -- Treat as a specific subdirectory
        dirs := dirs.push (tsTestBase / "cases" / "conformance" / arg)
    pure dirs

  let mut allFiles : Array System.FilePath := #[]
  for dir in testDirs do
    if ← dir.pathExists then
      let files ← findTsFiles dir
      allFiles := allFiles ++ files

  IO.println s!"Found {allFiles.size} test files"
  IO.println ""

  -- Run tests
  let mut passed := 0
  let mut failed := 0
  let mut crashed := 0
  let mut totalDiags := 0
  let mut crashMessages : Array (String × String) := #[]
  let mut testIdx := 0
  let total := allFiles.size

  for file in allFiles do
    testIdx := testIdx + 1
    let content ← IO.FS.readFile file
    let testName := testNameFromPath file
    IO.print s!"\r  [{testIdx}/{total}] {testName}                              "
    (← IO.getStdout).flush
    let result ← runSingleTest testName content

    if result.crashed then
      crashed := crashed + 1
      let msg := result.errorMessage.getD "unknown"
      crashMessages := crashMessages.push (testName, msg)
      if verbose then
        IO.println s!"  CRASH  {testName}: {msg}"
    else if result.parsed then
      passed := passed + 1
      totalDiags := totalDiags + result.errorCount
      if verbose && result.errorCount > 0 then
        IO.println s!"  PARSE  {testName} ({result.errorCount} diagnostics)"
    else
      failed := failed + 1
      if verbose then
        IO.println s!"  FAIL   {testName}"

    -- Progress every 50 tests
    if testIdx % 50 == 0 || testIdx == total then
      let pct := testIdx * 100 / max total 1
      IO.print s!"\r  [{testIdx}/{total}] {pct}% | passed:{passed} crashed:{crashed}    "
      (← IO.getStdout).flush

    -- Generate error baseline if requested
    if mode == .errorBaseline && result.parsed then
      match parseSourceFile testName content with
      | .ok (_, diagnostics) =>
        if diagnostics.size > 0 then
          let baseline := formatErrorBaseline testName content diagnostics
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

  -- Show first few crash messages
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
