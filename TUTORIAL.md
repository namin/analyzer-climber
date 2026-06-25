# Tutorial: teaching a verifier what a function means

A guided read of the seven files under `AnalyzerClimber/`. By the end you'll
understand, from ~650 lines of Lean, how a verifier that *cannot* prove an array
access safe — because it does not know what a library function does — comes to
prove it, **without the program changing**: it learns a certified summary of the
function, and the proof is the price of admission.

No Lean expertise required to follow the prose; every snippet is copied from the
compiled, axiom-audited source.

---

## 0. The puzzle

Here is the program. `items` has length 10; `userInput` is arbitrary.

```ts
const j = clampIndex(userInput, 0, items.length - 1);   // = clampIndex(userInput, 0, 9)
return items[j];                                          // safe iff 0 ≤ j < 10
```

A bounds checker wants to prove `j < 10`. But `clampIndex` is a library
function: the analyzer has no idea what it returns. So it must assume the worst —
`j` could be anything — and the proof **fails**.

The fix is *not* to change the program. It is to teach the analyzer what
`clampIndex` means, in a way the kernel will believe. That is the whole artifact:

```
baseline:            0 / 13 clients verified
sound but useless:   0 / 13 clients verified
sound and precise:  13 / 13 clients verified
```

Three numbers. Speculation is cheap, soundness is necessary, usefulness is a
separate thing — and once admitted, the knowledge is durable.

---

## 1. The domain: what the analyzer can say (`Domain.lean`)

The analyzer reasons with two abstract values: it knows *nothing*, or it knows a
range.

```lean
inductive AbsVal where
  | top
  | interval (lo hi : Nat) (h : lo ≤ hi)
```

Everything is over `Nat` — no negatives, so no negative-index distractions. The
*meaning* of an abstract value is the set of concrete numbers it admits, given by
`contains`. This is the yardstick every later claim is measured against:

```lean
def contains : AbsVal → Nat → Prop
  | top,              _ => True                 -- ⊤ admits everything
  | interval lo hi _, x => lo ≤ x ∧ x ≤ hi      -- an interval admits its members
```

The one executable question the bounds checker asks is *"is every value here below
the array length?"*. Only an interval can answer yes; `top` never can:

```lean
def safeForLen? : AbsVal → Nat → Bool
  | top,              _   => false
  | interval _ hi _,  len => decide (hi < len)
```

And the lemma that makes the Boolean trustworthy — a green check is a real fact:

```lean
theorem safeForLen_sound {a : AbsVal} {len x : Nat}
    (hsafe : a.safeForLen? len = true) (hc : a.contains x) : x < len
```

Read it aloud: *if the check passes and `x` is one of the values, then `x` is
genuinely in bounds.* Nothing downstream is allowed to lie about this.

---

## 2. The function and its ground truth (`Syntax.lean`)

A deliberately tiny language: constants, variables, ternary calls. One function
name is interesting (`clampIndex`); `unknown` stands for anything the analyzer
cannot see into. The *real* runtime behavior of `clampIndex` is:

```lean
def clampIndexConcrete (x lo hi : Nat) : Nat :=
  if x < lo then lo
  else if hi < x then hi
  else x
```

The single semantic fact this artifact turns on — clamping always lands inside
the window, *whatever `x` is*:

```lean
theorem clampIndex_between {x lo hi : Nat} (h : lo ≤ hi) :
    lo ≤ clampIndexConcrete x lo hi ∧ clampIndexConcrete x lo hi ≤ hi
```

Keep this theorem in view. It is the entire reason the useful summary, two
sections from now, is *allowed* to exist. The analyzer never gets to invent it;
it has to be proved against the real `clampIndexConcrete`.

---

## 3. The gate: a transfer function with a proof attached (`Certified.lean`)

An abstract *transfer function* is the analyzer's summary of a concrete function:
abstract arguments in, abstract result out.

```lean
abbrev Transfer := AbsVal → AbsVal → AbsVal → AbsVal
```

A transfer is **sound** when it never under-claims — the abstract result always
admits the real result, for every concrete input the abstract inputs admit:

```lean
def TransferSound (sem : FnName → Nat → Nat → Nat → Nat) (fn : FnName)
    (transfer : Transfer) : Prop :=
  ∀ x y z ax ay az,
    ax.contains x → ay.contains y → az.contains z →
    (transfer ax ay az).contains (sem fn x y z)
```

Now the design move on which everything rests. A transfer may only enter the
analyzer **bundled with a proof of its own soundness**. The bundle's constructor
*is* the gate — you cannot make one without the proof:

```lean
structure CertifiedTransfer (sem) (fn : FnName) where
  transfer : Transfer
  sound    : TransferSound sem fn transfer
```

An `Analyzer` is one transfer per name, plus a proof they are all sound. The base
analyzer knows nothing — every function maps to `top`:

```lean
def Analyzer.base (sem) : Analyzer sem where
  transferFor   := fun _ => topTransfer        -- ⊤ for everything
  transferSound := fun fn => topTransfer_sound sem fn
```

**Admission** overrides exactly one name and keeps the rest. This is the gate
crossing — the moment a speculative summary becomes durable analyzer knowledge:

```lean
def Analyzer.install (an : Analyzer sem) (cert : CertifiedTransfer sem fn) :
    Analyzer sem where
  transferFor   := fun g => if g = fn then cert.transfer else an.transferFor g
  transferSound := fun g => by
    by_cases h : g = fn
    · subst h; simpa using cert.sound          -- the new transfer: its proof
    · simpa [h] using an.transferSound g        -- every other name: untouched
```

Note there is no new assumption anywhere: the result is again a total, *sound*
analyzer, because both halves of the `if` carry a proof. The payoff lemma lifts
per-function soundness to the whole program by induction on the expression:

```lean
theorem analyze_sound (an : Analyzer sem)
    (henv : ∀ name, (aenv name).contains (env name)) :
    ∀ e, (analyze an aenv e).contains (eval sem env e)
```

If every installed transfer is sound, the analysis of any expression is sound.
(This one depends on *no axioms at all* — see `Audit.lean`.)

---

## 4. Three candidates walk up to the gate (`Clamp.lean`)

A meta-level proposes summaries for `clampIndex`. The gate admits only the ones
that can prove themselves. Watch all three.

### 4.1 Off-by-one — rejected

The classic fencepost mistake: claim the result is in `[lo, hi-1]`.

```lean
def offByOneClampTransfer : Transfer := fun _ alo ahi =>
  match alo.exact?, ahi.exact? with
  | some lo, some (Nat.succ hp) =>
      if h : lo ≤ hp then AbsVal.interval lo hp h else AbsVal.top
  | _, _ => AbsVal.top
```

It looks plausible — and it is *wrong*. With `x = 9, lo = 0, hi = 9` the real
`clampIndex 9 0 9 = 9`, but the summary claims `[0, 8]`, and `9 ∉ [0, 8]`. So its
soundness proposition is **false**, and we prove exactly that:

```lean
theorem offByOneClamp_unsound :
    ¬ TransferSound sem FnName.clampIndex offByOneClampTransfer := by
  intro hsound
  have hc := hsound 9 0 9 AbsVal.top
      (AbsVal.interval 0 0 (by omega)) (AbsVal.interval 9 9 (by omega))
      True.intro ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
  have h89 : (9 : Nat) ≤ 8 := hc.2          -- the summary's own claim, absurd
  omega
```

This is the kernel-rejection slide. The off-by-one transfer is **never built into
a `CertifiedTransfer`** — there is no broken file in the build, only a theorem
saying the broken candidate cannot pass. The gate is not a linter you can argue
with; passing it *is* exhibiting a proof, and here no proof exists.

### 4.2 Top — admitted but useless

Claim nothing at all. Trivially sound (`⊤` admits everything), so it sails
through the gate:

```lean
def topClampTransfer : Transfer := fun _ _ _ => AbsVal.top

theorem topClamp_sound : TransferSound sem FnName.clampIndex topClampTransfer := by
  intro x y z ax ay az _ _ _
  exact True.intro

def analyzerWithTopClamp : Analyzer sem :=
  (Analyzer.base sem).install topClampCertified
```

Admissible — and worthless. The bounds checker still sees `⊤` and still cannot
prove `j < 10`. **Soundness is necessary but not sufficient.** That is a separate
slide from the rejection, and it matters: a gate that only checks soundness will
happily admit knowledge that buys you nothing.

### 4.3 Precise — admitted and useful

When both clamp bounds are known exact constants with `lo ≤ hi`, the result is in
`[lo, hi]` — *regardless of `x`*. That last clause is the whole point: the index
value may be entirely unknown (`⊤`), and the summary still pins the range.

```lean
def preciseClampTransfer : Transfer := fun _ alo ahi =>
  match alo.exact?, ahi.exact? with
  | some lo, some hi =>
      if h : lo ≤ hi then AbsVal.interval lo hi h else AbsVal.top
  | _, _ => AbsVal.top
```

Its soundness proof is short, because the real work was done back in §2 — it just
hands the obligation to `clampIndex_between`:

```lean
theorem preciseClamp_sound : TransferSound sem FnName.clampIndex preciseClampTransfer := by
  intro x y z ax ay az _ hy hz
  ...
  by_cases hle : y ≤ z
  · rw [dif_pos hle]
    exact clampIndex_between hle          -- ← the ground truth, cashed in
  · rw [dif_neg hle]
    exact True.intro
```

And a small slide-ready comparison: the precise transfer is never *less* sound
than top — it simply carries more information when exact bounds are known.

```lean
theorem preciseClamp_refines_top (ax alo ahi : AbsVal) :
    (preciseClampTransfer ax alo ahi).refines (topClampTransfer ax alo ahi)
```

---

## 5. Making learning visible: the score (`Examples.lean`)

A *client* is `return items[index]` for an array of length `len`. Verifying it is
one line — does the analyzer prove the index below the length, with *no*
assumptions about inputs (`topEnv` says every variable is `⊤`)?

```lean
def checkClient? (an : Analyzer sem) (c : Client) : Bool :=
  safeForLen? (analyze an topEnv c.index) c.len
```

`score` just counts the clients an analyzer can verify, over a fixed list of 13
(the headline client plus twelve later arrivals, two of them *nested* clamps to
show the summary composes). The three numbers on the slide are named theorems,
each proved by reduction at build time (`by decide`, no `native_decide`):

```lean
theorem score_before   : score (Analyzer.base sem)      = 0             := by decide
theorem score_with_top : score analyzerWithTopClamp     = 0             := by decide
theorem score_after    : score analyzerWithPreciseClamp = clients.length := by decide
```

This is what makes the artifact *feel like learning* rather than verification: the
same fixed suite, the same unchanged programs, a number that climbs from 0 to 13
the instant a certified summary is installed — and stays there for every later
client, with no new proposal. One client is *compositional*
(`nestedClient`): its outer clamp's bounds are themselves clamp calls, so the
summary has to fire at depth to make those bounds exact — it verifies only after
admission (`nestedClient_not_verified_before` / `nestedClient_verified_after`).

### The payoff: a green check is a runtime guarantee

The number is satisfying, but here is the part that matters. A passing check is
not a Boolean — it *implies a real fact about every run*:

```lean
theorem verified_client_safe {an : Analyzer sem} {c : Client}
    (hcheck : checkClient? an c = true) (env : String → Nat) :
    eval sem env c.index < c.len
```

Its proof is three steps you've now met: `analyze_sound` (the analysis is sound) ∘
`safeForLen_sound` (the check means what it says), with `topEnv` standing in for
"we assumed nothing about the input." Instantiated at the headline client:

```lean
theorem mainClient_safe_after (env : String → Nat) :
    eval sem env mainClient.index < mainClient.len :=
  verified_client_safe (an := analyzerWithPreciseClamp) (c := mainClient)
    (by decide) env
```

For **every** `userInput`, `clampIndex(userInput, 0, 9)` indexes a length-10 array
in bounds. Not "the checker is happy" — the access is safe.

---

## 6. The receipts (`Audit.lean`)

`lake build` fails if any cited theorem's axiom dependencies drift. Every one of
them uses standard axioms only — `propext`, `Quot.sound`, or none — with **no
`sorry`, no `Classical.choice`, no `native_decide`**:

```lean
/-- info: 'AnalyzerClimber.analyze_sound' does not depend on any axioms -/
#guard_msgs in #print axioms analyze_sound

/-- info: 'AnalyzerClimber.verified_client_safe' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms verified_client_safe
```

One mechanical note worth stealing: in this toolchain `omega` quietly pulls in
`Classical.choice` *when its goal is a conjunction*. Every `∧` goal in the
development is therefore split by hand — `exact ⟨by omega, by omega⟩` — so each
`omega` faces a single inequality and the footprint stays clean. (Compare the two
shapes in `Syntax.lean`'s `clampIndex_between`.)

---

## The shape of the argument, in one breath

> The program does not change. A meta-level proposes a summary for an unknown
> function. The gate admits it only if it carries a soundness proof: the broken
> one (`offByOneClamp_unsound`) has no proof to give; the empty one
> (`topClamp_sound`) has a proof but no content; the right one
> (`preciseClamp_sound`) has both. `analyze_sound` then turns the admitted summary
> into whole-program soundness, and `verified_client_safe` turns a passing check
> into a runtime guarantee — for the original client and every later one. The
> verifier learned what `clampIndex` means.

---

## Run it

```sh
lake build                                # builds + runs every #guard / #guard_msgs
lake env lean AnalyzerClimber/Demo.lean   # prints the transcript
./scripts/demo.sh                         # both
```

---

## Exercises

1. **A second function.** Add `min3 : Nat → Nat → Nat → Nat` to `sem`, prove
   `min3_le` (its result is `≤` each argument), and certify a transfer that turns
   three intervals into a sound interval for the minimum. Install it alongside the
   clamp summary — `installAll` (in `Certified.lean`) and
   `installed_histories_sound` already say accepted histories compose.

2. **A sharper clamp.** The precise transfer demands *exact* `lo`/`hi`. Generalize
   it to accept interval bounds `alo = [a, b]`, `ahi = [c, d]` and return the best
   sound interval. What is the result, and where does `clampIndex_between` need
   strengthening?

3. **A subtler bad candidate.** Propose a transfer that is wrong only on an edge
   case (e.g. correct unless `lo = hi`). Find the witness, and prove the analogue
   of `offByOneClamp_unsound`. How small can the counterexample be?

4. **Lower bounds too.** `safeForLen?` only checks the upper end. Add a client
   shape that needs `lo ≤ index` (e.g. indexing from an offset) and extend
   `safeForLen_sound`'s analogue. Which existing proofs survive unchanged?

5. **Make `unknown` interesting.** Right now `analyze` of an `unknown` call is
   `⊤`. Give `unknown` a real semantics and a certified summary, and add a client
   that only verifies once *both* summaries are installed — a two-step learning
   curve, `0 → k → 12`.
```
