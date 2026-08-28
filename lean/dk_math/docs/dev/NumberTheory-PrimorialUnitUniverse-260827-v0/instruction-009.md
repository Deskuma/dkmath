# PUU-L009 — Nested Wheel Projection / Reflection Compatibility

## Goal

PUU-L008 closed the global replication law

```text
old wheel
  -> q lift fibers per old survivor
  -> exactly one fresh-prime deletion per fiber
  -> enlarged wheel
```

The next checkpoint should expose the inverse structural direction needed by later square-anchor work:

> every enlarged survivor canonically projects to one old survivor by reduction modulo the old period.

Do **not** introduce square anchors yet. First make the nested wheel tower itself an explicit public API.

## Recommended module

```text
DkMath.NumberTheory.PrimorialUniverse.WheelProjection
```

Recommended file:

```text
lean/dk_math/DkMath/NumberTheory/PrimorialUniverse/WheelProjection.lean
```

Import the current public replication layer, preferably:

```lean
import DkMath.NumberTheory.PrimorialUniverse.WheelReplication
```

and export the module through

```text
DkMath.NumberTheory.PrimorialUniverse
```

## 1. Canonical projection

Define reduction to the old period:

```lean
def primeBasisWheelProjection (S : Finset ℕ) (x : ℕ) : ℕ :=
  x % finitePrimeBasisProduct S
```

Keep this arithmetic definition minimal. The meaningful survivor theorems may assume `IsFinitePrimeBasis S` and `S.Nonempty`.

## 2. Projection of a lift

Prove the exact left-inverse law for a seat already in the old period:

```lean
theorem primeBasisWheelProjection_lift
    {S : Finset ℕ} {r j : ℕ}
    (hrM : r < finitePrimeBasisProduct S) :
    primeBasisWheelProjection S (primeBasisWheelLift S r j) = r
```

This should be a direct modulo theorem.

This is the algebraic reason the quotient/remainder decomposition in PUU-L008 really is a projection/fiber decomposition rather than only a cardinality argument.

## 3. Enlarged survivor projects to old survivor

Main projection theorem:

```lean
theorem enlargedWheelSurvivor_projects_to_oldSurvivor
    {S : Finset ℕ}
    (hS : IsFinitePrimeBasis S)
    (hSne : S.Nonempty)
    {q x : ℕ}
    (hq : Nat.Prime q)
    (hqS : q ∉ S)
    (hx : IsPrimeBasisWheelSurvivor (insert q S) x) :
    IsPrimeBasisWheelSurvivor S (primeBasisWheelProjection S x)
```

Prefer reusing

```lean
enlargedWheelSurvivor_iff_exists_oldSurvivorLift
```

from PUU-L008 instead of rebuilding the quotient/remainder proof.

## 4. Projection is onto old survivors

Show that every old survivor has at least one enlarged survivor above it.

A suitable theorem shape is:

```lean
theorem oldWheelSurvivor_has_enlargedLift
    {S : Finset ℕ}
    (hS : IsFinitePrimeBasis S)
    (hSne : S.Nonempty)
    {q r : ℕ}
    (hq : Nat.Prime q)
    (hqS : q ∉ S)
    (hr : IsPrimeBasisWheelSurvivor S r) :
    ∃ x : ℕ,
      IsPrimeBasisWheelSurvivor (insert q S) x ∧
      primeBasisWheelProjection S x = r
```

Use the PUU-L008 local surviving-index Finset and its cardinality `q - 1`. Since `Nat.Prime q` gives `1 < q`, the fiber is nonempty.

Do not replace this by a bare cardinality argument over the whole wheel; keep the witness fiber-local.

## 5. Exact projection fiber

Expose the enlarged survivors lying over one old survivor. One possible definition is:

```lean
noncomputable def primeBasisWheelProjectionFiber
    (S : Finset ℕ) (q r : ℕ) : Finset ℕ :=
  (primeBasisWheelSurvivors (insert q S)).filter
    (fun x => primeBasisWheelProjection S x = r)
```

For an old survivor `r`, prove that this fiber is exactly the surviving-lift image of

```lean
freshPrimeSurvivingLiftIndices S q r
```

or prove the equivalent membership characterization.

Then prove the exact fiber cardinality:

```lean
theorem card_primeBasisWheelProjectionFiber
    {S : Finset ℕ}
    (hS : IsFinitePrimeBasis S)
    (hSne : S.Nonempty)
    {q r : ℕ}
    (hq : Nat.Prime q)
    (hqS : q ∉ S)
    (hr : IsPrimeBasisWheelSurvivor S r) :
    (primeBasisWheelProjectionFiber S q r).card = q - 1
```

This is the quotient form of the PUU-L008 replication law:

```text
enlarged survivor set
  --projection mod M-->
old survivor set

fiber size = q - 1
```

## 6. Reflection compatibility

The old and enlarged wheels both carry the reflection from PUU-L006. Prove that projection respects that symmetry on enlarged survivors.

Let

```text
M  = finitePrimeBasisProduct S
M' = finitePrimeBasisProduct (insert q S) = q*M
```

For an enlarged survivor `x`, its old projection `r = x % M` satisfies `0 < r < M`. The expected exact relation is

```text
projection(M' - x) = M - projection(x)
```

A theorem shape may be:

```lean
theorem primeBasisWheelProjection_reflect_insert_fresh
    {S : Finset ℕ}
    (hS : IsFinitePrimeBasis S)
    (hSne : S.Nonempty)
    {q x : ℕ}
    (hq : Nat.Prime q)
    (hqS : q ∉ S)
    (hx : IsPrimeBasisWheelSurvivor (insert q S) x) :
    primeBasisWheelProjection S
        (finitePrimeBasisProduct (insert q S) - x) =
      finitePrimeBasisProduct S - primeBasisWheelProjection S x
```

Use the canonical decomposition from PUU-L008 if that gives the cleanest proof. Avoid a large new modular-arithmetic framework.

This theorem is important: the reflection symmetry is not recreated independently at each primorial level; it is compatible with the nested wheel projection.

## 7. Optional same-index gap identity only

Do **not** build a full wheel-gap theory in this checkpoint.

If useful as a tiny helper, it is acceptable to record the exact same-lift-index difference identity

```text
lift(r₂,j) - lift(r₁,j) = r₂ - r₁
```

under `r₁ ≤ r₂`.

But do not claim that all enlarged wheel gaps are copies of old gaps: fresh-prime deletion can merge adjacent gaps. Full gap-word transport, gap-merging laws, maximal gaps, Jacobsthal bounds, and related counting belong later if they become necessary.

## 8. Regression

Use the visible `6 -> 30` wheel.

Old wheel:

```text
{1,5}
```

Enlarged wheel:

```text
{1,7,11,13,17,19,23,29}
```

Projection modulo `6` should split the eight seats into two fibers:

```text
1-fiber:  1, 7, 13, 19
5-fiber: 11,17,23,29
```

Each has cardinality `4 = 5 - 1`.

A regression may prove the fiber Finsets explicitly, or prove enough concrete membership/cardinality statements to make the decomposition visible.

Reflection compatibility is also visible:

```text
1 <-> 29 projects to 1 <-> 5
7 <-> 23 projects to 1 <-> 5
11 <-> 19 projects to 5 <-> 1
13 <-> 17 projects to 1 <-> 5
```

## 9. Semantic boundary

PUU-L009 should establish only the nested finite-wheel quotient structure:

```text
fresh-prime enlargement
      ↓
enlarged wheel
      ↓ mod old period
old wheel

surjective projection
constant fiber size q - 1
reflection-compatible
```

Do not introduce in this checkpoint:

- square-anchor orbit
- Legendre shell or square-hole propagation
- generic wheel-gap word recursion
- Jacobsthal function/bounds
- Euler-phi identification as the main proof route
- closed primorial product formula over an indexed prime sequence
- PowerSwap
- GN/CosmicFormula
- PNT/RH/analytic sieve

The purpose is to expose the **nested self-similar wheel tower** as an exact finite morphism before a square anchor is allowed to move through it.

## 10. Report

Write:

```text
lean/dk_math/docs/dev/NumberTheory-PrimorialUnitUniverse-260827-v0/
  primorial-unit-universe-wheel-projection-260827.md
```

Report at minimum:

- projection definition
- lift left-inverse theorem
- enlarged-survivor -> old-survivor theorem
- surjectivity
- exact fiber cardinality `q - 1`
- reflection compatibility
- `6 -> 30` regression
- why full gap transport was deliberately deferred
- semantic boundary

## A+ criterion

Outcome A+ requires the enlarged wheel to be formally recognized as a nested `(q - 1)`-sheeted finite cover of the old survivor wheel, with canonical modulo projection and compatible reflection, without importing square-anchor or Legendre structure.

STOP after PUU-L009.
