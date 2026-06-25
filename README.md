# Analyzer Climber

A tiny, slide-friendly Lean 4 artifact about **proof-carrying semantic learning**:
an analyzer that cannot prove an array access safe — because it does not know what
a library function means — and then *learns* a certified summary of that function,
after which the access (and many later ones) verify.

```
const j = clampIndex(userInput, 0, items.length - 1);
return items[j];
```

## One-line idea

The program does not change; the verifier learns a certified semantic summary for
a library function it previously treated as unknown.

## The before/after

- **Before.** `clampIndex` is unknown, so the analyzer returns `⊤` for it and
  cannot prove array safety. The bounds check fails.
- **Proposal.** A meta-level proposes an abstract transformer for `clampIndex`
  (a "semantic summary" / abstract transfer function).
- **Gate.** Lean requires a *proof* that the transformer safely over-approximates
  the concrete function. The bundle `CertifiedTransfer` cannot be built without it.
- **After.** The transformer is installed, and future clients using `clampIndex`
  verify without rediscovering the summary. Admitted knowledge is durable.

## The three candidates

| Candidate   | Claims                         | Verdict   | Why                                            |
|-------------|--------------------------------|-----------|------------------------------------------------|
| off-by-one  | result ∈ `[lo, hi-1]`          | rejected  | `offByOneClamp_unsound`: soundness is *false*  |
| top         | result ∈ `⊤`                   | admitted  | sound, but lets nothing verify                 |
| precise     | result ∈ `[lo, hi]`            | admitted  | sound *and* useful — every client verifies     |

The off-by-one candidate is **never** added to the build as a transfer function.
It appears only as the subject of an unsoundness theorem — the gate cannot be
crossed because the soundness proposition itself is false. The concrete
counterexample is `offByOne_counterexample`: it *proposes* `clampIndex(_,0,9) ∈
[0,8]`, yet the *actual* `clampIndex(9,0,9) = 9`.

On the headline bounds the top/precise gap is one line each:
`topClamp_0_9_is_top` (`⊤`) versus `preciseClamp_0_9_is_interval` (`[0,9]`).

## The learning curve

`score` counts how many client programs an analyzer can verify. That single number
is what makes *learning* visible:

```
baseline (clampIndex unknown):   0 / 13 clients verified
sound but useless (⊤):           0 / 13 clients verified
sound and precise ([lo,hi]):    13 / 13 clients verified
```

Speculation is cheap, soundness is necessary, usefulness is separate — and once
admitted, the knowledge is durable and reused. One of the 13 is *compositional*
(`nestedClient`): the outer clamp's bounds are themselves clamp calls, so the
summary must fire at depth to make them exact — it verifies only after admission
(`nestedClient_not_verified_before` / `nestedClient_verified_after`).

## How to run

```sh
lake build                              # builds everything, runs all #guard/#guard_msgs checks
lake env lean AnalyzerClimber/Demo.lean # prints the demo transcript
```

`scripts/demo.sh` runs both.

## Main theorem / definition names to cite on slides

| Name                                 | What it says                                                        |
|--------------------------------------|---------------------------------------------------------------------|
| `TransferSound`                      | a transfer over-approximates the concrete function                  |
| `CertifiedTransfer` / `Analyzer.install` | the gate: a transfer enters only bundled with a soundness proof |
| `analyze_sound`                      | whole-program soundness from per-function soundness                 |
| `clampIndex_between`                 | the concrete fact: clamping lands in `[lo, hi]`                     |
| `offByOneClamp_unsound`              | the rejected candidate's soundness proposition is false             |
| `topClamp_sound`                     | the top candidate is sound (but useless)                            |
| `preciseClamp_sound`                 | the precise candidate is sound                                      |
| `preciseClamp_refines_top`           | precise is never less sound than top — just more informative        |
| `offByOne_counterexample`            | concrete witness: proposes `[0,8]`, but `clampIndex(9,0,9)=9`       |
| `topClamp_0_9_is_top` / `preciseClamp_0_9_is_interval` | the headline-bounds contrast: `⊤` vs `[0,9]`      |
| `score_before` / `score_with_top` / `score_after` | the curve `0 → 0 → 13`, checked by reduction          |
| `mainClient_not_verified_before` / `…_with_top` / `mainClient_verified_after` | per-client before/after |
| `nestedClient_not_verified_before` / `nestedClient_verified_after` | compositional reuse needs admission     |
| `verified_client_safe`               | a passing check implies a real runtime in-bounds index              |
| `mainClient_safe_after`              | the headline client is safe for every input after admission         |

## What this proves

- Every installed transfer function is sound relative to the concrete semantics.
- The analyzer remains sound after installing certified transfers
  (`install_preserves_soundness`), and accepted histories compose
  (`installed_histories_sound`).
- If the analyzer verifies a client's bounds check, then the concrete runtime
  index is in bounds — for *every* input (`verified_client_safe`).
- Installing the precise clamp summary strictly increases the number of clients
  verified: `0 → 13` (`score_before`, `score_with_top`, `score_after` in
  `Examples.lean`), including one compositional client.

The axiom footprint of every cited theorem is pinned in `Audit.lean`: standard
axioms only (`propext`, `Quot.sound`, or none) — no `sorry`, no `Classical.choice`,
no `native_decide`.

## What this does not prove

- It is not a production TypeScript analyzer.
- It does not parse real JavaScript/TypeScript.
- It models natural-number indices only (no negatives — a deliberate
  simplification to avoid negative-index distractions).
- It does not call an actual LLM; the three candidates stand in for meta-level
  proposals.
- It demonstrates proof-carrying admission and durable reuse, not full autonomous
  discovery.

## Slide

```
Old analyzer:
  clampIndex ↦ ⊤
  0/13 clients verified

Bad proposal:
  [lo, hi - 1]
  rejected by Lean        proposes clampIndex(_,0,9) ∈ [0,8],
                          but clampIndex(9,0,9) = 9
                          (offByOne_counterexample, offByOneClamp_unsound)

Useless proposal:
  ⊤
  admitted (sound), still 0/13

Useful proposal:
  [lo, hi]
  admitted (sound), 13/13
  incl. nested clampIndex(_, clampIndex(_,0,0), clampIndex(_,9,9))

Payoff:
  from ⊤ to proof:
  the program wasn't rewritten; it was understood.
```

## File map

```
AnalyzerClimber/
  Domain.lean      AbsVal (⊤ / intervals), contains, safeForLen?, safeForLen_sound
  Syntax.lean      Expr, clampIndexConcrete, eval, clampIndex_between
  Certified.lean   TransferSound, CertifiedTransfer, Analyzer(.base/.install), analyze_sound
  Clamp.lean       the three candidates + their (un)soundness theorems
  Examples.lean    clients, score, verified_client_safe, mainClient_safe_after
  Demo.lean        the printed transcript + #guard checks
  Audit.lean       pinned axiom footprints
```
