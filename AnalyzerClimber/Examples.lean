import AnalyzerClimber.Clamp

/-!
# AnalyzerClimber.Examples — clients, scoring, and runtime safety

A *client* models `return items[index]` for an array of length `len`. The
verifier checks only that `index` is always in bounds. `score` counts how many
clients an analyzer can verify — the number that makes *learning* visible:

```
baseline:            0 / 13 clients verified
sound but useless:   0 / 13 clients verified
sound and precise:  13 / 13 clients verified
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

/-- A *compositional* client: the outer `clampIndex`'s bounds are themselves
`clampIndex` calls. The outer summary can only fire once the inner summaries
have refined `clampIndex(otherInput,0,0)` to the exact `[0,0]` and
`clampIndex(thirdInput,9,9)` to the exact `[9,9]`. With `clampIndex` unknown
(or merely `⊤`) the inner calls stay `⊤`, the outer bounds are unknown, and the
access does not verify — so this client verifies *only* after the precise
summary is admitted, and it needs the summary used compositionally. -/
def nestedClient : Client :=
  { name  := "len 10,  clampIndex(userInput, clampIndex(otherInput,0,0), clampIndex(thirdInput,9,9))"
    len   := 10
    index := clampCall userInput
               (clampCall (Expr.var "otherInput") (lit 0) (lit 0))
               (clampCall (Expr.var "thirdInput") (lit 9) (lit 9)) }

/-- Later clients that arrive after the summary is admitted. None of them
require a new proposal; the durable summary verifies them all. The last two are
nested clamps, demonstrating compositional reuse. -/
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
      index := clampCall (clampCall userInput (lit 0) (lit 99)) (lit 10) (lit 20) },
    nestedClient ]

/-- All demo clients: the headline client plus the later arrivals. -/
def clients : List Client := mainClient :: laterClients

/-- How many clients an analyzer can verify. -/
def score (an : Analyzer sem) : Nat :=
  clients.foldl (fun acc c => if checkClient? an c then acc + 1 else acc) 0

/-! ### The learning curve, as named theorems

The baseline and the (sound but useless) top summary verify nothing; the precise
summary verifies every client. Each fact is checked by reduction at build time
(`by decide`, no `native_decide`), so the names below are citable on slides. -/

/-- Before: the unknown `clampIndex` leaves the headline client unverified. -/
theorem mainClient_not_verified_before :
    checkClient? (Analyzer.base sem) mainClient = false := by decide
/-- With the top summary admitted: still unverified — sound but useless. -/
theorem mainClient_not_verified_with_top :
    checkClient? analyzerWithTopClamp mainClient = false := by decide
/-- After the precise summary is admitted: the headline client verifies. -/
theorem mainClient_verified_after :
    checkClient? analyzerWithPreciseClamp mainClient = true := by decide

/-- Before: no client verifies. -/
theorem score_before : score (Analyzer.base sem) = 0 := by decide
/-- With top admitted: still no client verifies. -/
theorem score_with_top : score analyzerWithTopClamp = 0 := by decide
/-- After precise admitted: every client verifies. -/
theorem score_after : score analyzerWithPreciseClamp = clients.length := by decide

/-- The compositional client needs the summary used at depth: unverified under
the unknown `clampIndex`… -/
theorem nestedClient_not_verified_before :
    checkClient? (Analyzer.base sem) nestedClient = false := by decide
/-- …and verified once the precise summary is admitted and reused compositionally. -/
theorem nestedClient_verified_after :
    checkClient? analyzerWithPreciseClamp nestedClient = true := by decide

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
