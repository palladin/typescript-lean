/-
  TSLean.TestRunner.TestCaseParser — Parse test file directives.

  Based on Go: internal/testrunner/test_case_parser.go
  Parses `// @option: value` directives from test .ts files and splits
  multi-file tests by `// @filename:` directives.
-/

namespace TSLean.TestRunner

/-- A single compilation unit extracted from a test file.
    Based on Go: test_case_parser.go (testUnit struct) -/
structure TestUnit where
  name : String
  content : String
  deriving Repr

/-- Parsed test case content.
    Based on Go: test_case_parser.go (testCaseContent struct) -/
structure TestCaseContent where
  units : Array TestUnit
  options : Array (String × String)
  deriving Repr

/-- Check if a line is a `// @option: value` directive.
    Based on Go: test_case_parser.go (optionRegex) -/
private def parseDirectiveLine (line : String) : Option (String × String) :=
  let trimmed := line.trimAsciiStart.toString
  if trimmed.startsWith "//" then
    let afterSlash := (trimmed.drop 2).trimAsciiStart.toString
    if afterSlash.startsWith "@" then
      let afterAt := (afterSlash.drop 1).toString
      -- Find the colon separator
      match afterAt.splitOn ":" with
      | [] => none
      | [_] => none
      | name :: rest =>
        let optName := name.trimAscii.toString.toLower
        let optValue := (String.intercalate ":" rest).trimAscii.toString
        if optName == "" then none
        else some (optName, optValue)
    else none
  else none

/-- Accumulator for test file parsing. -/
private structure ParseAcc where
  options : Array (String × String) := #[]
  units : Array TestUnit := #[]
  currentName : String
  currentLines : Array String := #[]

/-- Parse a test file into units and compiler options.
    Based on Go: test_case_parser.go (ParseTestFilesAndSymlinksWithOptions)

    Strips `// @` directive lines from content.
    Splits multi-file tests by `// @filename:` directives. -/
def parseTestFile (fileName : String) (content : String) : TestCaseContent :=
  let lines := content.splitOn "\n"
  let init : ParseAcc := { currentName := fileName }
  let acc := lines.foldl (init := init) fun (acc : ParseAcc) line =>
    match parseDirectiveLine line with
    | some (name, value) =>
      if name == "filename" then
        -- Save current unit and start new one
        let units := if acc.currentLines.size > 0 || acc.units.size == 0 then
          acc.units.push { name := acc.currentName, content := "\n".intercalate acc.currentLines.toList }
        else acc.units
        { options := acc.options, units := units, currentName := value.trimAscii.toString, currentLines := #[] }
      else
        { options := acc.options.push (name, value), units := acc.units
          currentName := acc.currentName, currentLines := acc.currentLines }
    | none =>
      { options := acc.options, units := acc.units
        currentName := acc.currentName, currentLines := acc.currentLines.push line }
  -- Save final unit
  let finalUnits := acc.units.push { name := acc.currentName, content := "\n".intercalate acc.currentLines.toList }
  { units := finalUnits, options := acc.options }

end TSLean.TestRunner
