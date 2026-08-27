# PUU-L010 — Square-Anchor Orbit / Wheel Reservation Projection

## Goal

Introduce the square anchor and square-shell point as **PrimorialUniverse provider-side** objects, without importing the Legendre application layer.

For a finite prime basis `S` with product period

```text
M = finitePrimeBasisProduct S
```

make the finite orbit

```text
n       ↦ n^2 mod M
(n, r)  ↦ (n^2 + r) mod M
```

explicit and connect absolute reservation of `n^2 + r` with the survivor status of its projected wheel seat.

This checkpoint must remain independent of `DkMath.NumberTheory.Legendre`.  PUU-L011 will be the consumer bridge to the existing `SquareOffset`, `SquareOffsetCovered`, and Legendre vocabulary.

## Target module

```text
lean/dk_math/DkMath/NumberTheory/PrimorialUniverse/SquareAnchorOrbit.lean
```

Export it from:

```text
DkMath.NumberTheory.PrimorialUniverse
```

Recommended import:

```lean
import DkMath.NumberTheory.PrimorialUniverse.WheelProjection
```

Add only narrower Mathlib imports if compilation requires them.

## 1. Square-anchor projection vocabulary

Recommended definitions:

```lean
def squareAnchorWheelProjection
    (S : Finset ℕ) (n : ℕ) : ℕ :=
  primeBasisWheelProjection S (n ^ 2)


def squareShellWheelProjection
    (S : Finset ℕ) (n r : ℕ) : ℕ :=
  primeBasisWheelProjection S (n ^ 2 + r)
```

Naming may be adjusted if a repository collision exists, but preserve the meaning.

Do **not** define `SquareCell`, `SquareOffset`, or `SquareOffsetCovered` here; those already belong to `DkMath.NumberTheory.Legendre.Basic`.

## 2. Exact shell-coordinate law

Expose that the shell projection is the anchor projection advanced by the offset modulo the wheel period.

Preferred shape:

```lean
theorem squareShellWheelProjection_eq_anchor_add
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S)
    (n r : ℕ) :
    squareShellWheelProjection S n r =
      (squareAnchorWheelProjection S n + r) %
        finitePrimeBasisProduct S
```

Equivalent `r % M` formulations are acceptable if they produce a cleaner public theorem.

Also expose the consecutive-square update:

```lean
theorem squareAnchorWheelProjection_succ
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S)
    (n : ℕ) :
    squareAnchorWheelProjection S (n + 1) =
      (squareAnchorWheelProjection S n + (2 * n + 1)) %
        finitePrimeBasisProduct S
```

The mathematical point is the exact finite orbit update

```text
n^2  --(+ 2n+1)-->  (n+1)^2
```

inside the reservation period.

## 3. Periodicity of the square-anchor orbit

Prove that translating the anchor by any whole wheel period leaves the square projection unchanged.

Preferred public theorem:

```lean
theorem squareAnchorWheelProjection_add_mul_period
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S)
    (n k : ℕ) :
    squareAnchorWheelProjection S
        (n + k * finitePrimeBasisProduct S) =
      squareAnchorWheelProjection S n
```

A `Nat.ModEq` proof is welcome, but do not introduce a new abstract orbit framework.

A fixed-offset shell corollary is recommended:

```lean
theorem squareShellWheelProjection_add_mul_period
    ... :
    squareShellWheelProjection S
        (n + k * finitePrimeBasisProduct S) r =
      squareShellWheelProjection S n r
```

This is the precise sense in which the square-anchor trajectory is finite modulo the primorial period.

## 4. Generic reservation descends to the wheel projection

Before specializing to squares, prove the reusable projection law for any natural point:

```lean
theorem reservedByPrimeBasis_projection_iff
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S)
    (x : ℕ) :
    ReservedByPrimeBasis S (primeBasisWheelProjection S x) ↔
      ReservedByPrimeBasis S x
```

Either orientation is acceptable; add a simp-friendly companion if useful.

The proof should reuse PUU-L005 periodicity and the quotient/remainder decomposition rather than reimplement prime divisibility from scratch.

Also expose the negated form if useful:

```lean
¬ ReservedByPrimeBasis S (primeBasisWheelProjection S x) ↔
  ¬ ReservedByPrimeBasis S x
```

## 5. Unreserved absolute point iff projected wheel survivor

For a nonempty prime basis, zero residue cannot be unreserved.  Use this to upgrade the projected non-reservation statement to the one-period survivor predicate.

Required theorem, or equivalent:

```lean
theorem not_reserved_iff_projection_wheelSurvivor
    {S : Finset ℕ}
    (hS : IsFinitePrimeBasis S)
    (hSne : S.Nonempty)
    (x : ℕ) :
    (¬ ReservedByPrimeBasis S x) ↔
      IsPrimeBasisWheelSurvivor S
        (primeBasisWheelProjection S x)
```

This is an important semantic bridge:

```text
absolute point x avoids every old prime scale
                 ↕
its canonical residue is a wheel survivor
```

Then specialize it to the square shell:

```lean
theorem squareShell_not_reserved_iff_projection_survivor
    {S : Finset ℕ}
    (hS : IsFinitePrimeBasis S)
    (hSne : S.Nonempty)
    (n r : ℕ) :
    (¬ ReservedByPrimeBasis S (n ^ 2 + r)) ↔
      IsPrimeBasisWheelSurvivor S
        (squareShellWheelProjection S n r)
```

Do not call the survivor prime.

## 6. Nested-wheel coherence of square projections

The fresh-prime tower from PUU-L009 should commute with square projection.

Prefer first proving a generic nested-mod theorem for a fresh prime:

```lean
theorem primeBasisWheelProjection_insert_fresh_then_old
    {S : Finset ℕ}
    (hS : IsFinitePrimeBasis S)
    {q : ℕ}
    (hq : Nat.Prime q)
    (hqS : q ∉ S)
    (x : ℕ) :
    primeBasisWheelProjection S
        (primeBasisWheelProjection (insert q S) x) =
      primeBasisWheelProjection S x
```

Then expose square-anchor and/or square-shell corollaries, for example:

```lean
theorem squareShellWheelProjection_insert_fresh_projects_old
    ... :
    primeBasisWheelProjection S
        (squareShellWheelProjection (insert q S) n r) =
      squareShellWheelProjection S n r
```

This theorem should not require the square-shell point itself to be a survivor; it is a coherence law of the nested moduli.

## 7. Concrete regression

Use the established `6 → 30` tower.

Recommended visible checks:

```text
S = {2,3}, M = 6
n = 4
n^2 = 16
anchor projection = 4

r = 1
n^2 + r = 17
17 mod 6 = 5
5 is a {2,3}-wheel survivor
```

Also record the nested projection of the same shell point:

```text
17 mod 30 = 17
17 mod 6 = 5
```

so that projection through the 30-wheel agrees with direct projection to the 6-wheel.

Use small explicit theorems rather than `example` if they improve regression visibility.

## 8. Semantic boundary / STOP

Do not implement in PUU-L010:

- import or dependency on `DkMath.NumberTheory.Legendre`
- `SquareOffsetCovered` bridge
- Legendre conjecture equivalence
- proof that an unreserved square-shell point is prime
- square-hole propagation
- Jacobsthal bounds
- full wheel-gap recursion or gap merging
- Euler-phi identification
- analytic prime counting / PNT / RH
- PowerSwap
- GN / CosmicFormula

The next checkpoint should consume this provider from the Legendre side.

## Report

Create:

```text
lean/dk_math/docs/dev/NumberTheory-PrimorialUnitUniverse-260827-v0/
  primorial-unit-universe-square-anchor-orbit-260827.md
```

Record:

- exact public API,
- square-anchor successor update,
- period invariance,
- absolute reservation ↔ projected reservation,
- non-reservation ↔ projected survivor for nonempty bases,
- nested-wheel coherence,
- `n=4`, `6 → 30` regression,
- explicit statement that this module is Legendre-independent.

## Outcome rubric

### Outcome A+

All of the following are present:

1. square-anchor and square-shell projection definitions;
2. shell coordinate law;
3. consecutive-square update by `2*n+1`;
4. period invariance of the square-anchor orbit;
5. generic reservation/projection iff;
6. nonempty-basis unreserved iff projected survivor;
7. square-shell specialization;
8. fresh-prime nested projection coherence;
9. visible `n=4`, `6 → 30` regression;
10. no Legendre dependency or later-stage theorem leakage.

### Outcome P

The mathematical API is correct but one optional convenience corollary or regression is omitted because of disproportionate Lean engineering cost.  State the exact omission in the report.

### Outcome E

Only if a specific Mathlib modulo/cancellation API blocks the clean provider theorem.  Preserve all established modules, record the exact theorem/API blocker, and do not replace the target with a weaker unrelated counting statement.
