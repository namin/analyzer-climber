import Lake
open Lake DSL

package «analyzer-climber» where
  leanOptions := #[⟨`autoImplicit, false⟩]

@[default_target]
lean_lib «AnalyzerClimber» where
  srcDir := "."
