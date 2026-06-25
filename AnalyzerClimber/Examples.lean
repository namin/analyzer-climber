import AnalyzerClimber.Clamp

/-!
# AnalyzerClimber.Examples — clients, scoring, and runtime safety

A *client* models `return items[index]` for an array of length `len`. The
verifier checks only that `index` is always in bounds. `score` counts how many
clients an analyzer can verify — the number that makes *learning* visible:

```
baseline:            0 / 12 clients verified
sound but useless:   0 / 12 clients verified
sound and precise:  12 / 12 clients verified
```

The payoff is `verified_client_safe`: a passing Boolean check implies a real
runtime fact — the concrete index is in bounds for *every* input.
-/

namespace AnalyzerClimber

open AbsVal

/-- A client of an array of length `len`, indexing it by `index`.
Models `return items[index]` where `items.length = len`. -/
structure Client where
  name  : String
  len   : Nat
  index : Expr

/-- The all-`⊤` abstract environment: the analyzer knows nothing about inputs
such as `userInput`. Usefulness must come from the function summary, not from
assumptions about the input. -/
def topEnv : String → AbsVal := fun _ => AbsVal.top

/-- Verify a client: does the analyzer prove its index is `< len`? -/
def checkClient? (an : Analyzer sem) (c : Client) : Bool :=
  safeForLen? (analyze an topEnv c.index) c.len

/-- Convenience constructors for readable clients. -/
def userInput : Expr := Expr.var "userInput"
def lit (n : Nat) : Expr := Expr.const n
def clampCall (x lo hi : Expr) : Expr := Expr.call3 FnName.clampIndex x lo hi

/-- The headline client:
`clampIndex(userInput, 0, 9)` indexing a length-10 array. -/
def mainClient : Client :=
  { name  := "clampIndex(userInput,0,9) into length-10 array"
    len   := 10
    index := clampCall userInput (lit 0) (lit 9) }

/-- Later clients that arrive after the summary is admitted. None of them
require a new proposal; the durable summary verifies them all. The last is a
nested clamp, demonstrating compositional reuse. -/
def laterClients : List Client :=
  [ { name := "len 1,   clampIndex(userInput,0,0)",
      len := 1,   index := clampCall userInput (lit 0) (lit 0) },
    { name := "len 2,   clampIndex(userInput,0,1)",
      len := 2,   index := clampCall userInput (lit 0) (lit 1) },
    { name := "len 4,   clampIndex(userInput,1,3)",
      len := 4,   index := clampCall userInput (lit 1) (lit 3) },
    { name := "len 5,   clampIndex(userInput,0,4)",
      len := 5,   index := clampCall userInput (lit 0) (lit 4) },
    { name := "len 8,   clampIndex(userInput,2,7)",
      len := 8,   index := clampCall userInput (lit 2) (lit 7) },
    { name := "len 10,  clampIndex(userInput,0,9)",
      len := 10,  index := clampCall userInput (lit 0) (lit 9) },
    { name := "len 16,  clampIndex(userInput,3,15)",
      len := 16,  index := clampCall userInput (lit 3) (lit 15) },
    { name := "len 50,  clampIndex(userInput,20,49)",
      len := 50,  index := clampCall userInput (lit 20) (lit 49) },
    { name := "len 64,  clampIndex(userInput,0,63)",
      len := 64,  index := clampCall userInput (lit 0) (lit 63) },
    { name := "len 100, clampIndex(userInput,10,99)",
      len := 100, index := clampCall userInput (lit 10) (lit 99) },
    { name := "len 21,  clampIndex(clampIndex(userInput,0,99),10,20)",
      len := 21,
      index := clampCall (clampCall userInput (lit 0) (lit 99)) (lit 10) (lit 20) } ]

/-- All demo clients: the headline client plus the later arrivals. -/
def clients : List Client := mainClient :: laterClients

/-- How many clients an analyzer can verify. -/
def score (an : Analyzer sem) : Nat :=
  clients.foldl (fun acc c => if checkClient? an c then acc + 1 else acc) 0

/-! ### Executable checks: the learning curve

The baseline and the (sound but useless) top summary verify nothing; the
precise summary verifies every client. -/

#guard checkClient? (Analyzer.base sem) mainClient == false
#guard checkClient? analyzerWithTopClamp mainClient == false
#guard checkClient? analyzerWithPreciseClamp mainClient == true

#guard score (Analyzer.base sem) == 0
#guard score analyzerWithTopClamp == 0
#guard score analyzerWithPreciseClamp == clients.length

/-! ### From a passing check to a real runtime guarantee -/

/-- **The payoff theorem.** If the analyzer verifies a client, then for *every*
runtime environment the concrete index is genuinely `< len`: a real
array-index-safety fact, not merely a green check. -/
theorem verified_client_safe {an : Analyzer sem} {c : Client}
    (hcheck : checkClient? an c = true) (env : String → Nat) :
    eval sem env c.index < c.len := by
  have hsafe : safeForLen? (analyze an topEnv c.index) c.len = true := hcheck
  have hcontains : (analyze an topEnv c.index).contains (eval sem env c.index) :=
    analyze_sound an (aenv := topEnv) (env := env) (fun _ => True.intro) c.index
  exact safeForLen_sound hsafe hcontains

/-- The headline client is safe for every input, once the precise summary is
admitted: `clampIndex(userInput, 0, 9)` never indexes out of a length-10 array. -/
theorem mainClient_safe_after (env : String → Nat) :
    eval sem env mainClient.index < mainClient.len :=
  verified_client_safe (an := analyzerWithPreciseClamp) (c := mainClient)
    (by decide) env

end AnalyzerClimber
