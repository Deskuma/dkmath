# PRIM-L034 — Parity-Safe Active World / Totient-Surplus Lean Judgment

Date: 2026-08-25
Branch: `wip/number-theory-primitive-structure-260822-v2`
Environment: Lean / Mathlib v4.32.2

## 0. Goal

Build directly on PRIM-L033. Do not reprove L029--L033 results and do not introduce a generic graph library.

The key observation to judge in Lean is that the even/odd anchor split can be normalized away by restricting to **anchor-coprime seats whose complete point is odd**.

For such seats prime `2` cannot occur in the actual old support. Since L032 proves that every nontrivial fresh collision has exactly one endpoint owning old prime `2`, a parity-safe active family should have **no fresh-collision exception for any anchor**.

At the same time, compare the cardinality of the parity-safe candidate seat universe with the exact active prime world. The target is to expose a genuine candidate-seat surplus while also proving by a concrete false beam that the full candidate universe is not automatically a pairwise-disjoint provider.

Do not claim Legendre's conjecture. Stop after the finite Lean judgment.

## 1. Suggested module

Add a focused module, for example:

```text
DkMath/NumberTheory/Legendre/ParitySafeActiveCapacity.lean
```

Minimal imports should normally be:

```lean
import DkMath.NumberTheory.Legendre.ActivePrimeCapacity
```

plus only what Lean actually requires.

Add the module to `DkMath/NumberTheory/Legendre.lean`.

Do not change existing public theorem statements.

## 2. Parity-safe candidate seats

Introduce a finite set of anchor-coprime shell offsets whose complete point is odd. A suggested shape is:

```lean
noncomputable def squareAnchorOddPointCoprimeOffsets (n : ℕ) : Finset ℕ := by
  classical
  exact (squareAnchorCoprimeOffsets n).filter
    (fun r => Odd (n ^ 2 + r))
```

The exact spelling may be adjusted to fit Mathlib APIs, but preserve the semantics.

Prove exact membership:

```text
r ∈ squareAnchorOddPointCoprimeOffsets n
↔
r ∈ squareAnchorCoprimeOffsets n ∧ Odd (n^2+r)
```

and expose the `SquareOffset` / `Nat.Coprime n r` consequences through thin lemmas if useful.

## 3. Remove prime `2` from the active world

Define the parity-safe active prime world by removing `2` from the L033 nondivisor world, for example:

```lean
noncomputable def squareAnchorOddActivePrimes (n : ℕ) : Finset ℕ :=
  (squareAnchorNondivisorPrimes n).erase 2
```

Prove exact membership, preferably in the form

```text
q ∈ squareAnchorOddActivePrimes n
↔
Nat.Prime q ∧ q ≤ n ∧ ¬ q ∣ n ∧ q ≠ 2
```

or an equivalent proposition with the same mathematical content.

For a parity-safe seat, prove that its active support is contained in this smaller world. In particular prove directly that

```text
Odd (n^2+r)
→ 2 ∉ squareOffsetPrimeSupport n r
```

and the corresponding nondivisor-support version for anchor-coprime seats.

Do not rely on anchor parity for this theorem.

## 4. Universal fresh-collision elimination

Define a parity-safe active family predicate, for example:

```lean
def PairwiseParitySafeActiveOldSupportDisjointSquareSeatFamily
    (n : ℕ) (R : Finset ℕ) : Prop :=
  (∀ r ∈ R, r ∈ squareAnchorOddPointCoprimeOffsets n) ∧
    (R : Set ℕ).PairwiseDisjoint
      (fun r => squareOffsetAnchorNondivisorSupport n r)
```

Prove the bridge to the L033/L029 old-support family interfaces as needed.

Then prove the central parity-normalization theorem:

```text
PairwiseParitySafeActiveOldSupportDisjointSquareSeatFamily n R
→ PairwiseCoprimeSquareSeatFamily n R
```

with **no `Even n` assumption**.

Expected proof path:

```text
non-coprime pair
  -> L032 fresh collision
  -> exactly one endpoint owns old prime 2
  -> both complete points are odd
  -> prime 2 divides neither endpoint
  -> contradiction
```

This theorem is the main replacement for the even-only L033 elimination theorem.

## 5. Parity-safe active capacity

Under full cover, count only the smaller world `squareAnchorOddActivePrimes n`.

Prove a theorem of the form

```text
SquareOffsetsFullyCovered n
→ PairwiseParitySafeActiveOldSupportDisjointSquareSeatFamily n R
→ R.card ≤ (squareAnchorOddActivePrimes n).card
```

and the strict obstruction / Frontier consumer:

```text
(squareAnchorOddActivePrimes n).card < R.card
→ PairwiseParitySafeActiveOldSupportDisjointSquareSeatFamily n R
→ ¬ SquareOffsetsFullyCovered n
```

and

```text
0 < n
→ (squareAnchorOddActivePrimes n).card < R.card
→ PairwiseParitySafeActiveOldSupportDisjointSquareSeatFamily n R
→ ∃ p, Nat.Prime p ∧ SquareCell n p
```

Reuse the existing Frontier route. Do not duplicate L028/L029/L033 counting machinery unnecessarily.

## 6. Totient surplus: active primes embed into coprime base seats

This is a required arithmetic judgment, not an optional observation.

Prove that every anchor-nondivisor prime is itself a canonical coprime base offset:

```text
squareAnchorNondivisorPrimes n ⊆ squareAnchorCoprimeBaseOffsets n
```

Reason:

```text
q prime
q ≤ n
¬ q ∣ n
=> Nat.Coprime n q
=> q is a base coprime offset
```

Then prove the inclusion is strict for positive/nontrivial anchors because offset `1` lies in the coprime base but not in the prime world.

Target cardinal theorem:

```text
1 < n
→ (squareAnchorNondivisorPrimes n).card < Nat.totient n
```

using the already-proved

```text
(squareAnchorCoprimeBaseOffsets n).card = Nat.totient n.
```

Also derive the thinner consequence

```text
1 < n
→ (squareAnchorOddActivePrimes n).card < Nat.totient n
```

without analytic prime counting.

This is important: it proves that the exact active prime world is strictly smaller than one canonical packet half.

## 7. Cardinality of the parity-safe candidate universe

Attempt exact cardinality theorems.

### Even anchor

For `0 < n` and `Even n`, every anchor-coprime offset has odd complete point, so aim for

```text
squareAnchorOddPointCoprimeOffsets n = squareAnchorCoprimeOffsets n
```

and hence

```text
(squareAnchorOddPointCoprimeOffsets n).card = 2 * Nat.totient n.
```

### Odd anchor

For `Odd n`, the two seats in each canonical packet `(r, n+r)` have opposite complete-point parity. Hence exactly one seat per packet should survive.

Attempt the exact theorem

```text
(squareAnchorOddPointCoprimeOffsets n).card = Nat.totient n
```

under the weakest correct positivity/nontriviality assumptions.

Do not force this statement if Lean finds an endpoint exception. If the exact theorem is false, produce the smallest explicit Lean counterexample and replace it with the strongest correct bound.

At minimum, prove a universal lower bound strong enough to combine with Section 6:

```text
1 < n
→ Nat.totient n ≤ (squareAnchorOddPointCoprimeOffsets n).card
```

if the exact parity split becomes unnecessarily expensive.

The preferred outcome is the exact parity split.

## 8. Required candidate-surplus theorem

Combine Sections 6 and 7 into an explicit theorem showing that, for `1<n`, the parity-safe candidate seat universe is strictly larger than the parity-safe active prime world:

```text
(squareAnchorOddActivePrimes n).card
  < (squareAnchorOddPointCoprimeOffsets n).card
```

under the weakest correct hypotheses.

This theorem is a **candidate-universe surplus**, not a provider theorem.

Keep that distinction explicit in the theorem docstring and report.

## 9. Mandatory false beam: the whole safe universe is not a provider

Do not infer pairwise support disjointness from the cardinal surplus.

Use a small explicit counterexample to prove that the full parity-safe candidate universe can contain two seats hit by the same old active prime.

Suggested witness:

```text
n = 5
r = 2
s = 8
```

because

```text
5^2 + 2 = 27
5^2 + 8 = 33
```

and old active prime `3` divides both. Both complete points are odd and both offsets are coprime to `5`.

Prove a concrete theorem showing, as appropriate:

```text
2,8 ∈ squareAnchorOddPointCoprimeOffsets 5
3 ∈ squareOffsetAnchorNondivisorSupport 5 2
3 ∈ squareOffsetAnchorNondivisorSupport 5 8
```

and therefore the full safe universe is not pairwise active-support-disjoint.

This false beam is required because it identifies the remaining provider problem precisely as an **old-prime wave overlap / packing problem**, not parity and not candidate-seat shortage.

## 10. Stronger-beam judgment

After the required theorems build, answer these questions with actual Lean theorems or explicit counterexamples:

1. Does parity-safe restriction eliminate the L032 fresh-collision exception for every anchor?
2. Is the safe candidate universe always strictly larger than the exact parity-safe active prime world for `1<n`?
3. Does the whole safe candidate universe form a provider? Expected answer: no; prove the explicit `n=5` overlap.
4. Can one extract, from the existing packet/wave APIs alone, a canonical pairwise-disjoint-support subfamily whose card still exceeds the active world?
5. If not, state the exact next finite obstruction in terms of wave overlap / packing. Do not launch a new general graph framework.

Do not proceed to PRIM-L035 automatically.

## 11. Outcome classification

Use exactly one:

```text
A — PARITY-SAFE TOTIENT SURPLUS / UNIVERSAL FRESH-COLLISION ELIMINATION
B — PARITY-SAFE STRUCTURAL REFINEMENT ONLY
C — PARITY-SAFE SURPLUS OR ELIMINATION FAILS
```

Use Outcome A only if Lean proves both:

- universal fresh-collision elimination on the parity-safe family; and
- a strict candidate-seat cardinal surplus over the parity-safe active prime world.

A does **not** mean a universal provider or Legendre proof.

## 12. Report

Create:

```text
lean/dk_math/docs/dev/NumberTheory-PrimitiveStructure-260822-v0/
  primitive-parity-safe-active-world-totient-surplus-lean-judgment-260825.md
```

The report must clearly distinguish:

```text
candidate universe surplus
vs
pairwise-disjoint support provider
```

and record the `n=5` overlap false beam.

## 13. Validation

Run at least:

```text
lake build DkMath.NumberTheory.Legendre.ParitySafeActiveCapacity
lake build DkMath.NumberTheory.Legendre
git diff --check
```

plus the usual trailing-whitespace and forbidden-placeholder audit.

Stay on Lean / Mathlib v4.32.2. Do not run a full repository build unless needed for a real dependency issue.

## 14. Stop boundary

Stop after the parity-safe capacity, totient/cardinality surplus, universal fresh-collision elimination, and explicit old-wave overlap false beam are judged.

Do not implement:

- analytic prime counting,
- a generic graph/matching package,
- a universal provider,
- a descent,
- Legendre's conjecture,
- PRIM-L035.
