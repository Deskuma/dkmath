# PRIM-L029 — Old-Support Capacity / Exact Difference Criterion Lean Judgment

Date: 2026-08-25
Branch: `wip/number-theory-primitive-structure-260822-v2`
Toolchain: keep Lean / Mathlib v4.32.2. Do not upgrade.

## 0. Review decision carried into this checkpoint

PRIM-L028 is accepted as **Outcome A — DIRECT CAPACITY FRONTIER BRIDGE**.

The generic theorem

```text
pairwise-coprime actual shell seats
        -> pairwise-disjoint actual old-prime supports
        -> full cover spends at least one distinct old prime per seat
        -> R.card <= (primeScalesUpTo n).card
```

is now proved, and strict capacity excess is connected through `Frontier` to an actual prime in the square cell.

The example-only declarations previously left at the bottom of `CoprimeSeatCapacity.lean` have been removed by the user. Keep the production module surface clean.

The next checkpoint must weaken the provider hypothesis to the exact information consumed by the capacity proof. Complete-point coprimality is sufficient but stronger than necessary: the capacity proof only needs pairwise disjointness of the bounded old-prime supports.

This is a proof-backed Lean checkpoint, not report-only reconnaissance.

## 1. Purpose

Replace the strong family input

```text
Nat.Coprime (n^2+r) (n^2+s)
```

by the exact capacity input

```text
Disjoint
  (squareOffsetPrimeSupport n r)
  (squareOffsetPrimeSupport n s).
```

Then show two things in Lean:

1. the L028 capacity/frontier bridge survives under this strictly weaker condition;
2. old-support separation has a concrete arithmetic characterization in terms of the offset difference.

The conceptual point is that a common **fresh** prime `q > n` is irrelevant to the finite old-prime capacity accounting. Two complete points may therefore fail to be coprime while their actual old-prime supports are still disjoint.

## 2. Required source changes

Add one focused module, suggested path:

```text
DkMath/NumberTheory/Legendre/OldSupportCapacity.lean
```

It may import:

```lean
import DkMath.NumberTheory.Legendre.CoprimeSeatCapacity
```

and any lower module required for support membership arithmetic.

Add the new module to:

```text
DkMath/NumberTheory/Legendre.lean
```

Do not modify the public statements of L025–L028 theorems.
Do not reintroduce example/tutorial namespaces into production modules.
Do not introduce graph/coloring machinery.

## 3. L029-1 — exact old-support family predicate

Introduce one minimal predicate, suggested shape:

```lean
def PairwiseOldSupportDisjointSquareSeatFamily
    (n : ℕ) (R : Finset ℕ) : Prop :=
  (∀ r ∈ R, SquareOffset n r) ∧
    (R : Set ℕ).PairwiseDisjoint
      (fun r => squareOffsetPrimeSupport n r)
```

An equivalent explicit pairwise formulation is acceptable if it is materially easier in Lean.

Do not package this as a structure.

## 4. L029-2 — complete-coprime families embed into old-support families

Prove a thin bridge:

```text
PairwiseCoprimeSquareSeatFamily n R
  -> PairwiseOldSupportDisjointSquareSeatFamily n R.
```

Reuse `pairwiseDisjoint_squareOffsetPrimeSupport_of_family` from L028. Do not reprove divisor separation.

This establishes the logical implication from the old strong provider to the new exact-capacity provider.

## 5. L029-3 — strictness witness: fresh collision does not consume old capacity

Lean must certify that the new hypothesis is genuinely weaker, not merely a rename.

Use the concrete square shell `n = 3` and offsets

```text
r = 1
s = 6
```

so the complete points are

```text
3^2 + 1 = 10
3^2 + 6 = 15.
```

Prove all of the following in a small theorem package or separate thin theorems:

```text
SquareOffset 3 1
SquareOffset 3 6
¬ Nat.Coprime 10 15
Disjoint
  (squareOffsetPrimeSupport 3 1)
  (squareOffsetPrimeSupport 3 6)
```

The mathematical reason is that the common prime `5` is fresh (`5 > 3`), while the old supports are `{2}` and `{3}`.

Prefer proving the support fact through the actual support API rather than hard-coding Finset equality unless equality is the cleanest Lean route.

A useful public conclusion is acceptable, for example:

```text
there exists an old-support-disjoint two-seat family
which is not a complete-point-coprime family.
```

Do not over-generalize the strictness witness.

## 6. L029-4 — exact ordered difference criterion

For `r <= s`, prove an exact theorem characterizing old-support disjointness by the offset difference.

Target mathematical content:

```text
Disjoint (squareOffsetPrimeSupport n r)
         (squareOffsetPrimeSupport n s)

iff

∀ q, Nat.Prime q -> q <= n ->
  q ∣ n^2 + r ->
  ¬ q ∣ s - r.
```

The exact Lean binder style may follow the existing API.

Why this is exact:

```text
n^2 + s = (n^2 + r) + (s-r)    when r <= s.
```

Hence, once `q ∣ n^2+r`, divisibility of the second complete point is equivalent to divisibility of the offset gap `s-r`.

Requirements:

- prove both directions;
- use actual `squareOffsetPrimeSupport` membership;
- do not replace the statement by complete-point gcd = 1;
- do not lose the bound `q <= n`.

If a thin equivalent gcd formulation falls out naturally, for example using the gcd of `n^2+r` and `s-r`, it may be added only after the direct exact theorem is proved. Do not make gcd abstraction a prerequisite.

## 7. L029-5 — old-support finite capacity theorem

Prove the exact-capacity analogue of L028-5:

```text
PairwiseOldSupportDisjointSquareSeatFamily n R
+ SquareOffsetsFullyCovered n
------------------------------------------------
R.card <= (primeScalesUpTo n).card.
```

Suggested name:

```lean
card_pairwiseOldSupportDisjointSquareSeatFamily_le_primeScalesUpTo_of_fullyCovered
```

Reuse the L028 proof ingredients:

- full cover -> each support nonempty;
- pairwise disjoint support union;
- each support is contained in `primeScalesUpTo n`;
- finite cardinality.

Do not introduce a witness-choice function.

It is acceptable to factor a small private/local lemma if it prevents duplicating the full union-counting proof, but do not rewrite L028 public theorem statements.

## 8. L029-6 — strict capacity obstruction under the weaker family

Prove:

```text
PairwiseOldSupportDisjointSquareSeatFamily n R
+ (primeScalesUpTo n).card < R.card
------------------------------------------------
¬ SquareOffsetsFullyCovered n.
```

Suggested name:

```lean
not_fullyCovered_of_primeWorld_card_lt_pairwiseOldSupportDisjointSquareSeats
```

This must use the weaker old-support family directly, not convert back to complete-point coprimality.

## 9. L029-7 — local prime-square-cell consumer

With `hn : 0 < n`, connect L029-6 through the existing Frontier API and prove:

```text
∃ p, Nat.Prime p ∧ SquareCell n p.
```

Suggested name:

```lean
exists_prime_squareCell_of_primeWorld_card_lt_pairwiseOldSupportDisjointSquareSeats
```

Reuse the same existing Frontier chain as L028-7. Do not reprove the square-body composite argument.

## 10. L029-8 — optional universal sufficient provider

If it is genuinely thin after L029-7, define or state the sufficient provider theorem:

```text
(∀ n, 0 < n -> ∃ R,
    PairwiseOldSupportDisjointSquareSeatFamily n R ∧
    (primeScalesUpTo n).card < R.card)
  -> LegendreConjecture.
```

This direction is sufficient only. Do **not** claim equivalence with Legendre unless Lean proves the reverse direction independently.

If adding a named provider proposition would create needless API surface, state only the theorem with explicit assumptions or omit this optional item and record it in the report.

## 11. Stronger-beam judgment — mandatory

After the theorems build, judge exactly what improved over L028.

The checkpoint should establish, if Lean agrees:

```text
complete-point pairwise coprimality
        ↓ strictly stronger
pairwise old-support disjointness
        ↓ exact input used by finite capacity accounting
strict capacity excess
        ↓
local prime square-cell witness
```

The `n=3`, seats `{1,6}` witness is mandatory evidence that the implication is strict.

Then inspect whether the ordered difference criterion gives a materially more construction-friendly future provider:

```text
for old q <= n,
q dividing the first point must not divide the seat gap.
```

Do not start a growing-family search in this checkpoint.
Do not hand-build K5/K6.
Do not invoke analytic prime-counting or Jacobsthal bounds.

## 12. Outcome classification

### Outcome A — STRICTLY WEAKER CAPACITY FRONTIER BRIDGE

Use if Lean proves all of:

1. the old-support family capacity theorem;
2. the strict-cardinality local prime witness;
3. the `n=3, r=1, s=6` strictness witness showing complete coprimality is genuinely stronger;
4. the exact ordered difference criterion.

### Outcome B — WEAKER CAPACITY INTERFACE ONLY

Use if the old-support capacity/frontier theorem closes but strictness or the exact difference criterion does not produce the intended clean arithmetic interface.

### Outcome C — NO MATERIAL WEAKENING

Use if the new family collapses back to complete-point coprimality or the capacity proof cannot be reused cleanly.

## 13. Documentation

Create:

```text
lean/dk_math/docs/dev/NumberTheory-PrimitiveStructure-260822-v0/
  primitive-old-support-capacity-lean-judgment-260825.md
```

The report must include:

- exact declarations added;
- the complete-coprime -> old-support-disjoint bridge;
- the `n=3`, `{1,6}` strictness witness and its mathematical meaning;
- the exact ordered difference criterion;
- the weaker finite capacity theorem;
- the weaker local prime-square-cell consumer;
- whether an optional universal sufficient provider theorem was added;
- exact remaining provider problem;
- Outcome A/B/C;
- stop boundary.

## 14. Validation

Run at least:

```text
lake build DkMath.NumberTheory.Legendre.OldSupportCapacity
lake build DkMath.NumberTheory.Legendre
git diff --check
```

Also run the current trailing-whitespace / forbidden-placeholder audit.

Do not upgrade Mathlib. Do not run a full repository build unless an unexpected dependency change requires it.

## 15. Non-goals

Do not:

- claim Legendre's conjecture without a universal provider;
- claim the old-support capacity provider is equivalent to Legendre;
- require complete-point coprimality in the new main theorem;
- introduce graph/coloring/matching infrastructure;
- use PNT, Chebyshev, Rosser–Schoenfeld, Jacobsthal, or sieve estimates;
- hand-build K5/K6 merely to increase a constant seat count;
- restore example/tutorial declarations to production modules;
- replace Lean theorem attempts with report-only reconnaissance.

The essential checkpoint is:

```text
complete coprimality is stronger than needed
        ↓
keep only pairwise OLD-support disjointness
        ↓
characterize it exactly by old-prime divisibility of seat gaps
        ↓
full cover capacity theorem survives
        ↓
strict capacity excess still gives a prime square-cell witness
```
