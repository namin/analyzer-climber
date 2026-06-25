/-!
# AnalyzerClimber.Syntax — a tiny expression language and its meaning

A deliberately minimal language: constants, variables, and ternary function
calls. Only one library function is interesting, `clampIndex`; `unknown`
stands for any function whose code the analyzer cannot see.

`clampIndexConcrete` is the *real* runtime behavior of `clampIndex`. The whole
artifact is about an analyzer that does not initially know this function, then
learns a certified summary of it. The concrete fact `clampIndex_between` is the
ground truth that justifies the eventually-admitted precise summary.
-/

namespace AnalyzerClimber

/-- Library function names. `clampIndex` is the one with interesting
semantics; `unknown` models a function the analyzer cannot see into. -/
inductive FnName where
  | clampIndex
  | unknown
deriving DecidableEq

/-- Ternary-call expression language. Only ternary calls are needed; this is
deliberate, not a limitation we plan to lift. -/
inductive Expr where
  | const : Nat → Expr
  | var   : String → Expr
  | call3 : FnName → Expr → Expr → Expr → Expr

/-- A concrete environment maps variables to natural numbers. -/
abbrev Env := String → Nat

/-- The real behavior of `clampIndex(x, lo, hi)`: clamp `x` into `[lo, hi]`. -/
def clampIndexConcrete (x lo hi : Nat) : Nat :=
  if x < lo then lo
  else if hi < x then hi
  else x

/-- Concrete semantics of each function name. `unknown` is modelled as the
constant `0`; its exact value is irrelevant — the point is that the analyzer
has no certified summary for it. -/
def sem : FnName → Nat → Nat → Nat → Nat
  | .clampIndex => clampIndexConcrete
  | .unknown    => fun _ _ _ => 0

/-- Concrete evaluation of an expression under a function semantics and an
environment. -/
def eval (sem : FnName → Nat → Nat → Nat → Nat) (env : Env) : Expr → Nat
  | .const n        => n
  | .var x          => env x
  | .call3 fn a b c => sem fn (eval sem env a) (eval sem env b) (eval sem env c)

/-- **The concrete semantic fact.** Whenever `lo ≤ hi`, clamping lands inside
`[lo, hi]` regardless of `x`. This single lemma is exactly what makes the
precise abstract transformer sound. -/
theorem clampIndex_between {x lo hi : Nat} (h : lo ≤ hi) :
    lo ≤ clampIndexConcrete x lo hi ∧ clampIndexConcrete x lo hi ≤ hi := by
  unfold clampIndexConcrete
  -- Split the conjunction by hand so `omega` only ever faces a single
  -- inequality: that keeps the proof free of `Classical.choice`.
  split
  · exact ⟨by omega, by omega⟩
  · split
    · exact ⟨by omega, by omega⟩
    · exact ⟨by omega, by omega⟩

end AnalyzerClimber
