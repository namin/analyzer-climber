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
crossed because the soundness proposition itself is false.

## The learning curve

`score` counts how many client programs an analyzer can verify. That single number
is what makes *learning* visible:

```
baseline:            0 / 12 clients verified
sound but useless:   0 / 12 clients verified
sound and precise:  12 / 12 clients verified
```

Speculation is cheap, soundness is necessary, usefulness is separate — and once
admitted, the knowledge is durable and reused.

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
  verified: `0 → 12` (see the `#guard`s in `Examples.lean`).

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
  0/12 clients verified

Bad proposal:
  [lo, hi - 1]
  rejected by Lean        (offByOneClamp_unsound)

Useless proposal:
  ⊤
  admitted, still 0/12

Useful proposal:
  [lo, hi]
  admitted, 12/12

Payoff:
  The verifier learned what clampIndex means.
  The program did not change.
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
