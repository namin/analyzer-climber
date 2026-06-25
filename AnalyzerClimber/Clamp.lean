import AnalyzerClimber.Certified

/-!
# AnalyzerClimber.Clamp — three candidate summaries for `clampIndex`

A meta-level proposer offers abstract transformers for `clampIndex`. The gate
admits only those that carry a Lean soundness proof. Three candidates:

1. **off-by-one** `[lo, hi-1]` — *rejected*: we prove its soundness
   proposition is false, so no `CertifiedTransfer` can be built.
2. **top** `⊤` — *admitted* but useless: sound, yet it lets nothing verify.
3. **precise** `[lo, hi]` when the bounds are known exact constants —
   *admitted* and useful: sound, and clients using `clampIndex` now verify.

No broken file ever enters the build: the rejected candidate appears only as
the subject of an unsoundness theorem, never as a certified transfer.
-/

namespace AnalyzerClimber

open AbsVal

/-! ## 1. Rejected candidate: off-by-one -/

/-- The off-by-one summary: when both bounds are known exact constants and `hi`
is a successor, it claims the result lies in `[lo, hi-1]`. This is the classic
fencepost mistake. -/
def offByOneClampTransfer : Transfer := fun _ alo ahi =>
  match alo.exact?, ahi.exact? with
  | some lo, some (Nat.succ hp) =>
      if h : lo ≤ hp then AbsVal.interval lo hp h else AbsVal.top
  | _, _ => AbsVal.top

/-- Concrete witness of the example in the spec: `clamp(_, [0,0], [9,9])`
is claimed to be `[0, 8]`. -/
example :
    offByOneClampTransfer AbsVal.top
        (AbsVal.interval 0 0 (by omega)) (AbsVal.interval 9 9 (by omega))
      = AbsVal.interval 0 8 (by omega) := by
  rfl

/-- **Kernel rejection.** The off-by-one summary is *not* sound: with
`x = 9, lo = 0, hi = 9` the concrete `clampIndex 9 0 9 = 9`, but the summary
claims the result is in `[0, 8]`. The soundness proposition is therefore false,
so the gate's constructor cannot be satisfied. -/
theorem offByOneClamp_unsound :
    ¬ TransferSound sem FnName.clampIndex offByOneClampTransfer := by
  intro hsound
  have hc := hsound 9 0 9 AbsVal.top
      (AbsVal.interval 0 0 (by omega)) (AbsVal.interval 9 9 (by omega))
      True.intro ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
  -- hc : contains (offByOneClampTransfer ⊤ [0,0] [9,9]) (clampIndex 9 0 9)
  --    = contains [0,8] 9 = (0 ≤ 9 ∧ 9 ≤ 8), whose right half is false.
  have h89 : (9 : Nat) ≤ 8 := hc.2
  omega

/-! ## 2. Admitted but useless candidate: top -/

/-- The top summary: it claims nothing. Trivially sound. -/
def topClampTransfer : Transfer := fun _ _ _ => AbsVal.top

theorem topClamp_sound : TransferSound sem FnName.clampIndex topClampTransfer := by
  intro x y z ax ay az _ _ _
  exact True.intro

/-- Certified package for the top summary — admissible because sound. -/
def topClampCertified : CertifiedTransfer sem FnName.clampIndex :=
  ⟨topClampTransfer, topClamp_sound⟩

/-- The analyzer after admitting the top summary. -/
def analyzerWithTopClamp : Analyzer sem :=
  (Analyzer.base sem).install topClampCertified

/-! ## 3. Admitted and useful candidate: precise -/

/-- The precise summary: when both clamp bounds are known exact constants
`lo ≤ hi`, the result lies in `[lo, hi]` *regardless of `x`*. That last point
is exactly why it is useful: the index value may be entirely unknown (`⊤`). -/
def preciseClampTransfer : Transfer := fun _ alo ahi =>
  match alo.exact?, ahi.exact? with
  | some lo, some hi =>
      if h : lo ≤ hi then AbsVal.interval lo hi h else AbsVal.top
  | _, _ => AbsVal.top

theorem preciseClamp_sound : TransferSound sem FnName.clampIndex preciseClampTransfer := by
  intro x y z ax ay az _ hy hz
  show (preciseClampTransfer ax ay az).contains (clampIndexConcrete x y z)
  unfold preciseClampTransfer
  cases hay : ay.exact? with
  | none => exact True.intro
  | some lo =>
      cases haz : az.exact? with
      | none => exact True.intro
      | some hi =>
          have hyl : y = lo := exact?_eq_some hay hy
          have hzh : z = hi := exact?_eq_some haz hz
          subst hyl; subst hzh
          show (if h : y ≤ z then AbsVal.interval y z h else AbsVal.top).contains
              (clampIndexConcrete x y z)
          by_cases hle : y ≤ z
          · rw [dif_pos hle]
            exact clampIndex_between hle
          · rw [dif_neg hle]
            exact True.intro

/-- Certified package for the precise summary. -/
def preciseClampCertified : CertifiedTransfer sem FnName.clampIndex :=
  ⟨preciseClampTransfer, preciseClamp_sound⟩

/-- The analyzer after admitting the precise summary. -/
def analyzerWithPreciseClamp : Analyzer sem :=
  (Analyzer.base sem).install preciseClampCertified

/-- The precise transformer is never less sound than top: whatever it claims,
top would also admit. It simply carries strictly more information when exact
bounds are known. -/
theorem preciseClamp_refines_top (ax alo ahi : AbsVal) :
    (preciseClampTransfer ax alo ahi).refines (topClampTransfer ax alo ahi) :=
  fun _ _ => True.intro

end AnalyzerClimber
