# FLT5 cp-004i+ Golden Euclidean Division Report

Date: 2026-07-20

Branch: `hackathon/feature-gn5-flt5-260719-v0`

## Result

Stop condition **B** was reached.  Golden quotient/remainder division, an
honest global `EuclideanDomain GoldenInt`, and the formerly missing coprime
fifth-power factor split are now certified without `sorry`.

In particular, the old conditional result

```text
beta = epsilon * gamma^5
GoldenUnit epsilon
```

is now unconditional for every `SignedGoldenRamifierStrippedPacket`.

The exact remaining proposition has moved strictly downstream to unit and
coordinate arithmetic:

```lean
abbrev SignedGoldenUnitFifthPowerExclusion : Prop :=
  forall {u v w : Nat} (p : SignedGoldenRamifierStrippedPacket u v w)
    (epsilon gamma : GoldenInt),
    GoldenUnit epsilon ->
    p.beta = goldenMul epsilon (goldenPow gamma 5) ->
    False
```

Certified receivers show that this proposition implies
`SignedGoldenRamifierStrippedCore`, `SignedBranchARefuter`, and contradiction
for every routed Branch-B packet.

## Added implementation

### `GoldenEuclidean.lean`

- `GoldenRat` and `goldenRatNorm`;
- nearest-integer and simultaneous nearest-lattice lemmas using Mathlib
  `round`;
- `goldenRat_norm_abs_le_five_sixteen`, the sharp square-cell estimate;
- explicit rational quotient coordinates, deterministic rounded quotient,
  and residual;
- the rational norm identity for the residual;
- `golden_remainder_size_lt`;
- `exists_golden_quotient_remainder`;
- `goldenEuclideanDomain : EuclideanDomain GoldenInt`.

The exact division theorem is:

```lean
theorem exists_golden_quotient_remainder
    (x y : GoldenInt) (hy : y != 0) :
    exists q r : GoldenInt,
      x = q * y + r /\
      (r = 0 \/ goldenEuclideanSize r < goldenEuclideanSize y)
```

The quotient is not merely existential: `goldenQuotient x y` rounds both
rational coordinates of `x / y`, and `goldenRemainder x y` is the corresponding
residual.

### `GoldenCoprimeFactor.lean`

- `goldenUnit_iff_isUnit` connects the explicit and standard unit predicates;
- `goldenCoprimeFactorOfFifthPower` inhabits the former blocker;
- `signedGoldenFifthPowerUpToUnitCore` removes its last algebraic hypothesis.

The proof constructs Mathlib's `GCDMonoid` from the certified Euclidean
domain, proves `IsUnit (gcd x y)` from `GoldenRelPrime`, and applies
`exists_associated_pow_of_mul_eq_pow`.

### `SignedGoldenUnitClasses.lean`

- `GoldenUnitClassesModFifth`, the precise expected five-representative unit
  classification contract;
- `SignedGoldenFiniteUnitSectorCore` and its receiver;
- preservation of the exact packet second-coordinate equation in each sector;
- `SignedGoldenUnitFifthPowerExclusion`, the exact remaining arithmetic core;
- receivers back through stripped core, Signed Branch-A, and routed Branch-B.

The stable modules were added to `DkMath.FLT.Five.Main`.

## Unit-classification audit

Four honest routes were checked.

1. A Pell/Fibonacci classification is mathematically appropriate, since
   `goldenNorm (a,b) = +/-1` becomes a Pell-type equation after the linear
   change `(2*a+b)^2 - 5*b^2 = +/-4`.  Mathlib's general Pell API classifies
   the norm-one equation, but it does not directly supply the required
   generalized `+/-4` classification in the integral basis used here.
2. Mathlib has unit and norm APIs for `Zsqrtd`, but no ready theorem was found
   identifying all units of this golden order as signed powers of `phi`.
3. The packet-specific reduction modulo fifth powers is now isolated by
   `GoldenUnitClassesModFifth`; its receiver combines the absorbed fifth power
   with `gamma` and leaves exactly five representatives.
4. A direct coordinate/valuation attack can use the already certified formulas
   in `GoldenFifthPowerCoordinates.lean` and
   `beta.snd = -5^7*a^10`.  This is now precisely the content of
   `SignedGoldenUnitFifthPowerExclusion`; it is not assumed or disguised as a
   completed descent.

Thus the new blocker is not an algebraic-structure gap.  It is the classical
unit-sector/descent arithmetic after the factorization is already available.

## Petal-reusable artifacts

The checkpoint produced several reusable normalization components without
moving them into `DkMath.Petal.*`:

- nearest points in a rank-two rational lattice;
- a finite fundamental coordinate cell;
- a sharp `5/16` absolute-norm contraction bound;
- an explicit normalization residual;
- a natural-valued well-founded normalization relation;
- separation of quotient scale from the contravariant coordinate error.

A future bridge could package a rank-two integral lattice equipped with a
multiplicative observation polynomial and a certified contracting fundamental
cell.  The current concrete golden implementation should remain the reference
model.

## Verification

All required checks passed:

- `lake build DkMath.FLT.Five.GoldenOrder`;
- `lake build DkMath.FLT.Five.GoldenEuclidean`;
- `lake build DkMath.FLT.Five.SignedGoldenFifthPower`;
- `lake build DkMath.FLT.Five.GoldenFifthPowerCoordinates`;
- `lake env lean DkMath/FLT/Five/Main.lean`;
- `lake env lean DkMathTest/FLT/Five/CheckAxioms.lean`;
- `lake -Kjobs=1 build` (8690 jobs);
- `./lean-build.sh`.

`CheckAxioms.lean` now audits the new Euclidean, factor-split, finite-sector,
and receiver declarations.  It reports only the repository's accepted logical
axioms (`propext`, `Classical.choice`, and `Quot.sound`), never `sorryAx`.

The whole-repository build still reports pre-existing `sorry` warnings in
unrelated research modules.  None occurs in the cp-004i implementation or its
FLT5 dependency chain.
