# PUU-L016 — Square-Anchor Phase Symmetry / Reservation-Pattern Invariant

## Goal

PUU-L015 proved that the global old-escape provider is exactly Legendre's
conjecture in different vocabulary.  Therefore this checkpoint must leave the
Legendre consumer layer and extract a genuinely independent invariant from the
provider-side wheel geometry already built in PUU-L001--L010.

The target invariant is:

> anchors with the same square coordinate modulo the finite prime-basis period
> have exactly the same reservation / survivor pattern for every fixed offset.

The first visible symmetry is the reflection

```text
n  <->  M - n
```

inside one period `M = finitePrimeBasisProduct S`, since

```text
(M - n)^2 ≡ n^2 (mod M).
```

This checkpoint is an orbit/phase theorem only.  It must not mention Legendre
escape existence or try to prove a short-gap bound.

## Preferred module

```text
DkMath/NumberTheory/PrimorialUniverse/SquareAnchorPhase.lean
```

Import only provider-side modules, preferably:

```lean
import DkMath.NumberTheory.PrimorialUniverse.SquareAnchorOrbit
```

Export through `DkMath.NumberTheory.PrimorialUniverse`.

Do **not** import `DkMath.NumberTheory.Legendre`.

## 1. Same square-anchor phase

Introduce a small provider-side predicate or relation, e.g.

```lean
def SameSquareAnchorPhase (S : Finset ℕ) (a b : ℕ) : Prop :=
  squareAnchorWheelProjection S a =
    squareAnchorWheelProjection S b
```

If a definition would be pure noise, theorem-only API is acceptable, but a
named relation is preferred because later checkpoints may study its fibers.

Provide basic relation theorems:

```text
refl
symm
trans
```

or an `Equivalence` theorem if that is cleaner.

## 2. Period translation is phase-preserving

Reuse PUU-L010 instead of reproving arithmetic:

```lean
theorem sameSquareAnchorPhase_add_mul_period ... :
  SameSquareAnchorPhase S n
    (n + k * finitePrimeBasisProduct S)
```

Equivalent orientation is fine.

This theorem should be a thin wrapper over
`squareAnchorWheelProjection_add_mul_period`.

## 3. Reflection inside one period

For `M := finitePrimeBasisProduct S`, prove the central new symmetry:

```lean
theorem squareAnchorPhase_reflect
    {S : Finset ℕ}
    (hS : IsFinitePrimeBasis S)
    {n : ℕ}
    (hn : n ≤ finitePrimeBasisProduct S) :
    SameSquareAnchorPhase S n
      (finitePrimeBasisProduct S - n)
```

Mathematical kernel:

```text
(M - n)^2 - n^2 = M * (M - 2n)
```

but do not force this subtraction identity in `Nat` if awkward.  A modulo proof,
`Nat.sub` arithmetic with `hn`, or a short `Int` detour is acceptable.

The theorem should work at the endpoints as well (`n = 0`, `n = M`).

If natural, add the involutive coordinate statement:

```text
M - (M - n) = n
```

under `n ≤ M`, but this is optional.

## 4. Same phase preserves every shell-offset coordinate

This is the main reusable invariant.  Prove:

```lean
theorem squareShellProjection_eq_of_sameAnchorPhase
    {S : Finset ℕ}
    (hS : IsFinitePrimeBasis S)
    {a b : ℕ}
    (hab : SameSquareAnchorPhase S a b)
    (r : ℕ) :
    squareShellWheelProjection S a r =
      squareShellWheelProjection S b r
```

Use PUU-L010
`squareShellWheelProjection_eq_anchor_add` rather than expanding squares if
possible.

This theorem is stronger conceptually than the reflection example:

```text
same square-anchor phase
  -> same projected seat for every offset r
```

## 5. Reservation-pattern invariance

Lift the coordinate equality back to absolute reservation status.  Preferred
public theorem:

```lean
theorem reservedByPrimeBasis_square_add_iff_of_sameAnchorPhase
    {S : Finset ℕ}
    (hS : IsFinitePrimeBasis S)
    {a b : ℕ}
    (hab : SameSquareAnchorPhase S a b)
    (r : ℕ) :
    ReservedByPrimeBasis S (a ^ 2 + r) ↔
      ReservedByPrimeBasis S (b ^ 2 + r)
```

Proof route:

```text
absolute reservation
  <-> reservation of canonical projection      (PUU-L010)
  =  same shell projection                     (phase invariant)
  <-> absolute reservation
```

Also provide the non-reservation iff by `not_congr`.

For `S.Nonempty`, an optional survivor spelling is useful:

```lean
IsPrimeBasisWheelSurvivor S (squareShellWheelProjection S a r)
  ↔
IsPrimeBasisWheelSurvivor S (squareShellWheelProjection S b r)
```

but direct coordinate equality may already make this trivial; do not duplicate
API without value.

## 6. Reflection corollary for reservation patterns

Specialize the previous theorem to the reflected anchor:

```lean
theorem reservedByPrimeBasis_square_reflect_iff ...
```

with semantic meaning:

```text
for 0 ≤ n ≤ M,
all offsets r see the same finite-prime reservation pattern from n and M-n.
```

This is the first independent square-anchor orbit symmetry extracted after the
PUU-L015 anti-relabeling audit.

## 7. Optional phase-class Finset — only if small

If implementation remains compact, define the one-period phase fiber:

```lean
noncomputable def squareAnchorPhaseFiber
    (S : Finset ℕ) (n : ℕ) : Finset ℕ :=
  (Finset.range (finitePrimeBasisProduct S)).filter
    (fun m => SameSquareAnchorPhase S n m)
```

Provide membership theorem only.  Full cardinality / CRT sign classification is
**not** part of PUU-L016.

This optional Finset is intended as the input to a later `±`-fiber / CRT audit.

## 8. Visible `M = 6` regression

For `S = {2,3}`, `M = 6`, record the phase symmetry:

```text
1^2 mod 6 = 5^2 mod 6 = 1
2^2 mod 6 = 4^2 mod 6 = 4
```

Prefer theorems using the general reflection result rather than four unrelated
`norm_num` facts.

At least one regression should show reservation-pattern preservation for a
fixed offset, e.g. anchors `1` and `5` with one or two visible `r` values.

## Outcome A+ rubric

PUU-L016 is A+ if it establishes:

1. a named same-square-anchor-phase relation (or equivalent public API);
2. period translation preserves phase;
3. one-period reflection `n -> M-n` preserves square-anchor phase;
4. same phase gives identical shell projection for every offset;
5. absolute finite-basis reservation and non-reservation patterns are identical
   for same-phase anchors;
6. a reflection-specialized pattern theorem;
7. visible `{2,3}`, `M=6` regression;
8. provider-only dependency direction and semantic report.

## STOP

Do **not** prove or assume:

- existence of a square-shell escape;
- any `escapingSquareOffsets` theorem;
- `SuccessorOldEscapeCriterion`;
- Legendre conjecture;
- a Jacobsthal/max-gap bound;
- a claim that reflection alone forces an escape;
- full CRT characterization of phase fibers;
- phase-fiber cardinality;
- PowerSwap;
- GN/CosmicFormula;
- PNT/RH.

The next question after PUU-L016 is whether one square-anchor phase fiber has a
nontrivial **prime-coordinate sign decomposition**.  For a squarefree prime
basis one expects equality of square phases to decompose locally as independent
`±` choices modulo each basis prime.  That CRT/sign-fiber theorem should be a
later checkpoint, only after the elementary phase invariant is stable.

## Report

Create:

```text
lean/dk_math/docs/dev/NumberTheory-PrimorialUnitUniverse-260827-v0/
  primorial-unit-universe-square-anchor-phase-symmetry-260827.md
```

The report must state explicitly that this is an independent provider-side
invariant, but **not yet a Legendre provider**.  Its value is that the square
anchor orbit factors through phase classes whose members have identical
reservation patterns for every offset.