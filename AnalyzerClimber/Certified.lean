import AnalyzerClimber.Domain
import AnalyzerClimber.Syntax

/-!
# AnalyzerClimber.Certified — proof-carrying transfer functions

A *transfer function* is an abstract interpretation of a concrete function: it
maps abstract arguments to an abstract result. It is **sound** when it always
over-approximates the concrete function.

The central design point: a transfer function may only enter the analyzer as a
`CertifiedTransfer`, a transfer bundled with a Lean proof of its soundness. The
constructor *is* the gate — there is no way to build the bundle without the
proof. `analyze_sound` then propagates per-function soundness to whole-program
soundness.
-/

namespace AnalyzerClimber

open AbsVal

/-- An abstract transfer function for a ternary call. -/
abbrev Transfer := AbsVal → AbsVal → AbsVal → AbsVal

/-- Soundness of a transfer for `fn`: on any concrete arguments admitted by the
abstract arguments, the abstract result admits the concrete result. -/
def TransferSound (sem : FnName → Nat → Nat → Nat → Nat) (fn : FnName)
    (transfer : Transfer) : Prop :=
  ∀ x y z ax ay az,
    ax.contains x → ay.contains y → az.contains z →
    (transfer ax ay az).contains (sem fn x y z)

/-- A proof-carrying transfer function. The `sound` field is the gate:
you cannot construct this without a soundness proof. -/
structure CertifiedTransfer (sem : FnName → Nat → Nat → Nat → Nat) (fn : FnName) where
  transfer : Transfer
  sound    : TransferSound sem fn transfer

/-- An analyzer: a transfer function per name, together with a proof that every
one of them is sound. -/
structure Analyzer (sem : FnName → Nat → Nat → Nat → Nat) where
  transferFor   : FnName → Transfer
  transferSound : ∀ fn, TransferSound sem fn (transferFor fn)

/-- The maximally-imprecise transfer: it claims nothing (`top`). -/
def topTransfer : Transfer := fun _ _ _ => AbsVal.top

theorem topTransfer_sound (sem : FnName → Nat → Nat → Nat → Nat) (fn : FnName) :
    TransferSound sem fn topTransfer := by
  intro x y z ax ay az _ _ _
  exact True.intro

/-- The base analyzer maps every function to `top`: sound, but it knows
nothing. This is where every story starts. -/
def Analyzer.base (sem : FnName → Nat → Nat → Nat → Nat) : Analyzer sem where
  transferFor   := fun _ => topTransfer
  transferSound := fun fn => topTransfer_sound sem fn

/-- **The admission event.** Installing a certified transfer overrides exactly
one function name and preserves every other. A speculative semantic summary
becomes durable analyzer knowledge *only because it carries a proof*: the
resulting `Analyzer` is again total and again sound, with no new assumptions. -/
def Analyzer.install {sem : FnName → Nat → Nat → Nat → Nat} {fn : FnName}
    (an : Analyzer sem) (cert : CertifiedTransfer sem fn) : Analyzer sem where
  transferFor   := fun g => if g = fn then cert.transfer else an.transferFor g
  transferSound := fun g => by
    by_cases h : g = fn
    · subst h; simpa using cert.sound
    · simpa [h] using an.transferSound g

/-- Installation preserves soundness — a direct projection of the field, but a
convenient name to cite: after admission the whole analyzer is still sound. -/
theorem install_preserves_soundness {sem : FnName → Nat → Nat → Nat → Nat}
    {fn : FnName} (an : Analyzer sem) (cert : CertifiedTransfer sem fn) :
    ∀ g, TransferSound sem g ((an.install cert).transferFor g) :=
  (an.install cert).transferSound

/-- Installation overrides the targeted name with the new transfer. -/
theorem install_transferFor_self {sem : FnName → Nat → Nat → Nat → Nat}
    {fn : FnName} (an : Analyzer sem) (cert : CertifiedTransfer sem fn) :
    (an.install cert).transferFor fn = cert.transfer := by
  simp [Analyzer.install]

/-- Installation leaves every other name untouched. -/
theorem install_transferFor_other {sem : FnName → Nat → Nat → Nat → Nat}
    {fn g : FnName} (an : Analyzer sem) (cert : CertifiedTransfer sem fn)
    (h : g ≠ fn) : (an.install cert).transferFor g = an.transferFor g := by
  simp [Analyzer.install, h]

/-- Abstractly interpret an expression. Constants become singleton intervals,
variables read the abstract environment, and calls dispatch to the analyzer's
certified transfer. -/
def analyze {sem : FnName → Nat → Nat → Nat → Nat} (an : Analyzer sem)
    (aenv : String → AbsVal) : Expr → AbsVal
  | .const n        => AbsVal.interval n n (Nat.le_refl n)
  | .var x          => aenv x
  | .call3 fn a b c =>
      an.transferFor fn (analyze an aenv a) (analyze an aenv b) (analyze an aenv c)

/-- **Whole-program soundness.** If every variable's abstract value admits its
concrete value, then the analyzer's abstract result admits the concrete result
of the whole expression. This is the theorem that lifts certified per-function
summaries to a sound analysis. -/
theorem analyze_sound {sem : FnName → Nat → Nat → Nat → Nat} (an : Analyzer sem)
    {aenv : String → AbsVal} {env : Env}
    (henv : ∀ name, (aenv name).contains (env name)) :
    ∀ e, (analyze an aenv e).contains (eval sem env e) := by
  intro e
  induction e with
  | const n => exact ⟨Nat.le_refl n, Nat.le_refl n⟩
  | var x => exact henv x
  | call3 fn a b c iha ihb ihc =>
      exact an.transferSound fn _ _ _ _ _ _ iha ihb ihc

/-! ### Accepted histories compose

An installable item is a function name paired with a certified transfer for it.
Installing a whole history yields, again, a sound analyzer — durable knowledge
that accumulates. -/

/-- A name together with a certified transfer ready to be installed. -/
def Installable (sem : FnName → Nat → Nat → Nat → Nat) :=
  Σ fn : FnName, CertifiedTransfer sem fn

/-- Install a list of certified transfers in order. -/
def installAll {sem : FnName → Nat → Nat → Nat → Nat} :
    Analyzer sem → List (Installable sem) → Analyzer sem
  | an, []                  => an
  | an, ⟨_, cert⟩ :: rest   => installAll (an.install cert) rest

/-- Installing any accepted history keeps the analyzer sound. -/
theorem installed_histories_sound {sem : FnName → Nat → Nat → Nat → Nat}
    (an : Analyzer sem) (hist : List (Installable sem)) :
    ∀ fn, TransferSound sem fn ((installAll an hist).transferFor fn) :=
  (installAll an hist).transferSound

end AnalyzerClimber
