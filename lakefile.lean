import Lake
open Lake DSL

package «typescript-lean» where
  version := v!"0.1.0"
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

@[default_target]
lean_lib TSLean where
  srcDir := "TSLean"
  roots := #[`TSLean]

lean_exe tslean where
  srcDir := "TSLean"
  root := `Main
