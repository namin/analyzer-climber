import AnalyzerClimber.Examples

/-!
# AnalyzerClimber.Audit — pinned axiom footprint

`lake build` fails if any of these theorems' axiom dependencies change. Standard
axioms only (`propext`, `Quot.sound`); no `sorry`, no `Classical.choice`, no
`native_decide` anywhere in the development. The whole-program soundness theorem
`analyze_sound`, the trivially-sound `topClamp_sound`, and the structural
`install_preserves_soundness`/`preciseClamp_refines_top` are the lightest;
nothing here reaches beyond `propext`/`Quot.sound`.
-/

namespace AnalyzerClimber

/-- info: 'AnalyzerClimber.AbsVal.safeForLen_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms AbsVal.safeForLen_sound

/-- info: 'AnalyzerClimber.clampIndex_between' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms clampIndex_between

/-- info: 'AnalyzerClimber.analyze_sound' does not depend on any axioms -/
#guard_msgs in #print axioms analyze_sound

/-- info: 'AnalyzerClimber.install_preserves_soundness' depends on axioms: [propext] -/
#guard_msgs in #print axioms install_preserves_soundness

/-- info: 'AnalyzerClimber.offByOneClamp_unsound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms offByOneClamp_unsound

/-- info: 'AnalyzerClimber.topClamp_sound' does not depend on any axioms -/
#guard_msgs in #print axioms topClamp_sound

/-- info: 'AnalyzerClimber.preciseClamp_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms preciseClamp_sound

/-- info: 'AnalyzerClimber.preciseClamp_refines_top' depends on axioms: [propext] -/
#guard_msgs in #print axioms preciseClamp_refines_top

/-- info: 'AnalyzerClimber.verified_client_safe' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms verified_client_safe

/-- info: 'AnalyzerClimber.mainClient_safe_after' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms mainClient_safe_after

end AnalyzerClimber
