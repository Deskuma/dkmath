# PUU-L021 — Square-Phase Survivor Subcover / Two-of-(q−1) Selection

## Goal

Connect the independent square-phase fiber tower from PUU-L016--L020 with the
wheel-survivor tower from PUU-L006--L009, without importing the Legendre
consumer layer.

The key new fact is structural, not merely cardinal:

- for a nonempty finite prime basis, a coprime-anchor square-phase fiber is a
  subset of the one-period wheel survivors;
- after adjoining a fresh odd prime `q`, each two-sheet square-phase projection
  fiber is a subset of the corresponding `(q - 1)`-seat wheel-survivor
  projection fiber.

Thus the PUU-L020 two-sheet cover is a genuine subcover of the PUU-L009 wheel
cover.

Do **not** prove escape existence or import `DkMath.NumberTheory.Legendre`.

## Recommended module

```text
DkMath.NumberTheory.PrimorialUniverse.SquareAnchorPhaseSurvivorSubcover
```

Suggested file:

```text
lean/dk_math/DkMath/NumberTheory/PrimorialUniverse/SquareAnchorPhaseSurvivorSubcover.lean
```

Import the existing square-phase projection module and wheel projection API.
Export the new module from `DkMath.NumberTheory.PrimorialUniverse`.

## 1. Phase-fiber elements of a coprime anchor are wheel survivors

For nonempty `S`, prove a pointwise theorem of the following shape:

```lean
theorem squareAnchorPhaseFiber_mem_wheelSurvivor_of_coprime_anchor
    {S : Finset ℕ}
    (hS : IsFinitePrimeBasis S)
    (hSne : S.Nonempty)
    {a b : ℕ}
    (hcop : Nat.Coprime a (finitePrimeBasisProduct S))
    (hb : b ∈ squareAnchorPhaseFiber S a) :
    IsPrimeBasisWheelSurvivor S b := by
  ...
```

Recommended proof route:

1. obtain `b < M` and `SameSquareAnchorPhase S a b` from
   `mem_squareAnchorPhaseFiber`;
2. descend the phase to `SameSquarePrimeSignProfile S a b`;
3. show no `p ∈ S` divides `b`: if `b = 0` in `ZMod p`, either local sign forces
   `a = 0` or `a = -0 = 0`, contradicting coprimality of `a` with `M`;
4. conclude `¬ ReservedByPrimeBasis S b`;
5. use `S.Nonempty` plus non-reservation to rule out `b = 0`;
6. combine positivity, `b < M`, and non-reservation.

A separate reusable lemma

```lean
Nat.Coprime b (finitePrimeBasisProduct S)
```

for same-phase `b` is welcome if it shortens the proof, but do not duplicate
existing reduced-residue APIs unnecessarily.

## 2. Finset inclusion

Package the pointwise result as a Finset subset theorem:

```lean
theorem squareAnchorPhaseFiber_subset_primeBasisWheelSurvivors
    {S : Finset ℕ}
    (hS : IsFinitePrimeBasis S)
    (hSne : S.Nonempty)
    {a : ℕ}
    (hcop : Nat.Coprime a (finitePrimeBasisProduct S)) :
    squareAnchorPhaseFiber S a ⊆ primeBasisWheelSurvivors S := by
  ...
```

A cardinality corollary is useful:

```lean
(squareAnchorPhaseFiber S a).card ≤
  (primeBasisWheelSurvivors S).card
```

The main value is the inclusion itself, not the inequality.

## 3. Fresh-prime projection subcover

Let `q` be a fresh odd prime and assume the base anchor is coprime to the
enlarged product.

For every old phase-fiber representative `b`, prove:

```lean
theorem squareAnchorPhaseProjectionFiber_subset_wheelProjectionFiber
    {S : Finset ℕ}
    (hS : IsFinitePrimeBasis S)
    (hSne : S.Nonempty)
    {q a b : ℕ}
    (hq : Nat.Prime q)
    (hqS : q ∉ S)
    (hq2 : q ≠ 2)
    (hcop : Nat.Coprime a (finitePrimeBasisProduct (insert q S)))
    (hb : b ∈ squareAnchorPhaseFiber S a) :
    squareAnchorPhaseProjectionFiber S q a b ⊆
      primeBasisWheelProjectionFiber S q b := by
  ...
```

The proof should reuse:

- PUU-L020 membership/projection theorems;
- the new phase-fiber-to-survivor theorem for the enlarged basis;
- PUU-L009 `primeBasisWheelProjectionFiber` membership structure.

Derive old-product coprimality of `a` from enlarged-product coprimality instead
of adding it as a second independent hypothesis.

## 4. Exact `2` versus `q - 1` comparison

Reuse the existing PUU-L020 theorem giving

```text
card phase projection fiber = 2
```

and PUU-L009

```lean
card_primeBasisWheelProjectionFiber ... = q - 1
```

to expose the exact local comparison.

Recommended theorem/corollary shapes:

```lean
(squareAnchorPhaseProjectionFiber S q a b).card = 2

(primeBasisWheelProjectionFiber S q b).card = q - 1

2 ≤ q - 1
```

Do not reprove either cardinality from scratch.

## 5. The special fresh prime `q = 3`

For fresh `q = 3`, the two covers have the same local cardinality:

```text
2 = q - 1.
```

Since the phase projection fiber is already a subset of the wheel projection
fiber, prove equality:

```lean
theorem squareAnchorPhaseProjectionFiber_eq_wheelProjectionFiber_of_q_eq_three
    ...
```

Equivalent specialized statement with `q := 3` is acceptable.

Mathematical meaning: adjoining fresh prime `3` gives no survivor lift outside
the square-phase pair.

## 6. Fresh odd prime above `3`: proper subcover

For a fresh prime `q` with `3 < q` (or equivalently prime odd `q ≠ 3`), prove
that the phase projection fiber is a proper subset of the wheel projection
fiber, preferably via strict cardinality:

```text
2 < q - 1.
```

A theorem of either form is acceptable:

```lean
(squareAnchorPhaseProjectionFiber S q a b).card <
  (primeBasisWheelProjectionFiber S q b).card
```

or a strict Finset inclusion theorem if convenient.

This is the exact `two-of-(q-1)` selection law.

## 7. Visible `6 → 30` regression

Use the existing `{2,3} → {2,3,5}`, `a = 1` regressions.

Record that over old representative `1`:

```text
phase fiber : {1, 19}
wheel fiber : {1, 7, 13, 19}
```

and over old representative `5`:

```text
phase fiber : {11, 29}
wheel fiber : {11, 17, 23, 29}
```

The new regression should visibly establish subset and cardinality `2 < 4`.
Reuse existing exact-fiber regression theorems where possible.

## 8. Semantic boundary

This checkpoint is provider-side finite congruence geometry only.

Do **not** introduce:

- `DkMath.NumberTheory.Legendre` imports;
- `escapingSquareOffsets`;
- Legendre conjecture or square-cell prime existence;
- wheel-gap / Jacobsthal bounds;
- a claim that phase-fiber inclusion forces a shell escape;
- PowerSwap, GN/CosmicFormula, PNT, or RH.

A phase-fiber representative is a survivor **seat modulo the finite basis**.
That fact alone is not a prime-existence theorem in a moving square shell.

## Report

Create:

```text
lean/dk_math/docs/dev/NumberTheory-PrimorialUnitUniverse-260827-v0/
  primorial-unit-universe-square-phase-survivor-subcover-260828.md
```

The report should explicitly distinguish:

```text
wheel-survivor fresh-prime fiber : q - 1 seats
square-phase fresh-prime fiber   : 2 seats for fresh odd q
```

and state that the second is now formally embedded as a subcover of the first.

## A+ criteria

1. coprime-anchor phase fiber embeds into wheel survivors;
2. Finset inclusion is public;
3. fresh odd phase projection fiber embeds into wheel projection fiber;
4. exact `2` versus `q - 1` comparison reuses L020/L009;
5. fresh `q = 3` equality is formalized;
6. `q > 3` proper-subcover/strict-cardinality statement is formalized;
7. `6 → 30` two-of-four regression is visible;
8. no Legendre consumer dependency or escape claim.
