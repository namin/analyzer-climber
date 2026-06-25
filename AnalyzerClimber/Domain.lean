/-!
# AnalyzerClimber.Domain — a tiny numeric abstract domain

The analyzer reasons about program values with two abstract values:

* `top`            — no information at all (the value could be anything);
* `interval lo hi` — the value is known to lie in `[lo, hi]`.

Everything is over `Nat`, so there are no negative-index distractions.
`contains` is the concretization (which concrete numbers an abstract value
admits) and is the *meaning* against which every analyzer claim is checked.
-/

namespace AnalyzerClimber

/-- An abstract numeric value: either no information (`top`) or a finite
interval `[lo, hi]` carrying a proof that it is well-formed. -/
inductive AbsVal where
  | top
  | interval (lo hi : Nat) (h : lo ≤ hi)

namespace AbsVal

/-- Concretization: the concrete naturals that an abstract value admits.
`top` admits everything; an interval admits exactly its members. -/
def contains : AbsVal → Nat → Prop
  | top,              _ => True
  | interval lo hi _, x => lo ≤ x ∧ x ≤ hi

/-- `a` refines `b` when everything `a` admits, `b` also admits — i.e. `a`
is at least as precise (carries at least as much information) as `b`. -/
def refines (a b : AbsVal) : Prop :=
  ∀ x, a.contains x → b.contains x

/-- Recognize a singleton interval `[n, n]` and report its sole value. -/
def exact? : AbsVal → Option Nat
  | top              => none
  | interval lo hi _ => if lo = hi then some lo else none

/-- The known upper bound, if any. -/
def upperBound? : AbsVal → Option Nat
  | top              => none
  | interval _ hi _  => some hi

/-- Executable bounds check: `true` exactly when the analyzer has enough
interval information to know that *every* value the abstract value admits is
`< len`. `top` carries no upper bound, so it is never safe. -/
def safeForLen? : AbsVal → Nat → Bool
  | top,              _   => false
  | interval _ hi _,  len => decide (hi < len)

/-- **Soundness of the bounds check.** If `safeForLen? a len` succeeds and `x`
is admitted by `a`, then `x` is genuinely in bounds. This is what lets a
Boolean analyzer result imply a real array-index safety fact. -/
theorem safeForLen_sound {a : AbsVal} {len x : Nat}
    (hsafe : a.safeForLen? len = true) (hc : a.contains x) : x < len := by
  cases a with
  | top => simp [safeForLen?] at hsafe
  | interval lo hi hwf =>
      simp only [safeForLen?, decide_eq_true_eq] at hsafe
      have hx : lo ≤ x ∧ x ≤ hi := hc
      omega

/-- `top` admits every concrete value. -/
theorem contains_top (x : Nat) : AbsVal.top.contains x := True.intro

/-- Anything refines `top`: `top` is the least precise abstract value. -/
theorem refines_top (a : AbsVal) : a.refines AbsVal.top :=
  fun x _ => contains_top x

/-- A singleton recognized by `exact?` pins the concrete value exactly. -/
theorem exact?_eq_some {a : AbsVal} {n y : Nat}
    (h : a.exact? = some n) (hc : a.contains y) : y = n := by
  cases a with
  | top => simp [exact?] at h
  | interval lo hi hwf =>
      simp only [exact?] at h
      by_cases he : lo = hi
      · rw [if_pos he] at h
        injection h with hn
        have hy : lo ≤ y ∧ y ≤ hi := hc
        omega
      · rw [if_neg he] at h
        simp at h

end AbsVal
end AnalyzerClimber
