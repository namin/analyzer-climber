import AnalyzerClimber.Examples

/-!
# AnalyzerClimber.Demo — the demo transcript

Run with:

```
lake env lean AnalyzerClimber/Demo.lean
```

The `#eval` prints a readable before/after transcript and the `#guard`s assert
the learning curve `0 / N → 0 / N → N / N`.
-/

namespace AnalyzerClimber

/-- A compact demo transcript of the whole story. -/
def demoReport : String :=
  let n := clients.length
  String.intercalate "\n"
    [ "Analyzer Climber demo",
      "---------------------",
      "baseline analyzer:",
      s!"  verified clients: {score (Analyzer.base sem)} / {n}",
      "",
      "candidate: off-by-one clamp summary  [lo, hi-1]",
      "  status: rejected",
      "  reason: theorem offByOneClamp_unsound (soundness proposition is false)",
      "",
      "candidate: top clamp summary  ⊤",
      "  status: admitted (sound)",
      s!"  verified clients: {score analyzerWithTopClamp} / {n}",
      "",
      "candidate: precise clamp summary  [lo, hi]",
      "  status: admitted (sound)",
      s!"  verified clients: {score analyzerWithPreciseClamp} / {n}",
      "",
      "after admission:",
      "  original client verifies",
      "  later clients verify with no new proposals",
      "",
      "The program did not change. The verifier learned what clampIndex means." ]

#eval IO.println demoReport

/-! ### Executable assertions repeated here for a self-contained transcript -/

#guard score (Analyzer.base sem) == 0
#guard score analyzerWithTopClamp == 0
#guard score analyzerWithPreciseClamp == clients.length
#guard checkClient? analyzerWithPreciseClamp mainClient == true

end AnalyzerClimber
