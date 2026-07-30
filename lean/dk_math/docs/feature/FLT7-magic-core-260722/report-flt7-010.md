# FLT7-010 implementation report

## Outcome

Outcome A. The explicit seventh-power coordinates, characteristic-seven
collapse, coordinate route, exact one-hot away factor, and four endpoint
residue sectors are complete. This checkpoint remains a finite residue ledger:
it proves neither a contradiction nor a descent.

## Files changed

- `DkMath/FLT/Seven/SeventhPowerCoordinates.lean`
- `DkMath/FLT/Seven/CoordinateNormalForm.lean`
- `DkMath/FLT/Seven/ModSevenSectors.lean`
- `DkMath/FLT/Seven.lean`
- `DkMathTest/FLT/SevenSeventhPowerCoordinates.lean`
- `DkMathTest/FLT/SevenModSevenSectors.lean`
- `docs/feature/FLT7-magic-core-260722/report-flt7-010.md`

## Explicit coordinate surface

The definitions `seventhPowerFst` and `seventhPowerSnd` are the requested
degree-seven integer polynomials. The theorem surface is:

- `traceOne_pow_seven_fst`
- `traceOne_pow_seven_snd`
- `traceOne_pow_seven_eq`

Thus, for `gamma = (u,v)` in the discriminant `-7` trace-one order,

```text
gamma^7 = (seventhPowerFst u v, seventhPowerSnd u v).
```

The ramified polynomials `ramifiedSeventhFst` and
`ramifiedSeventhSnd` satisfy

```text
ramifiedSeventhFst = -seventhPowerFst - 4*seventhPowerSnd
ramifiedSeventhSnd = 2*seventhPowerFst + seventhPowerSnd,
```

and `sevenAxis_mul_pow_seven_eq` packages the exact equality

```text
sevenAxis * gamma^7 =
  (ramifiedSeventhFst u v, ramifiedSeventhSnd u v).
```

## Second-coordinate factor and characteristic-seven collapse

The universal factorization is exposed as

```text
seventhPowerSnd u v = 7*v*seventhPowerSndCore u v.
```

The key finite-field identity is

```text
SndCore(u,v) = (u^2 + u*v + 2*v^2)^3  in ZMod 7.
```

The norm form is the same quadratic form. Conceptually, its collapse comes
from the double-root identity

```text
tau^2 - tau + 2 = (tau - 4)^2 in characteristic 7.
```

Consequently every seventh power loses its nilpotent coordinate modulo `7`:

```text
gamma^7                 = (u+4v, 0)
sevenAxis * gamma^7     = (-(u+4v), 2*(u+4v)).
```

The module also proves that norm nondivisibility implies
`7 ∤ seventhPowerSndCore`, and the exact carry equivalence

```text
49 ∣ seventhPowerSnd u v  <->  7 ∣ v
```

under the same norm hypothesis. This uses only the displayed factorization
and primality of `7`, not LTE.

## Coordinate normal forms

`AwayCoordinateNormalForm` records the original counterexample, away gap,
root, element equality, and both expanded coordinate equations.
`RamifiedCoordinateNormalForm` similarly expands the FLT7-009 ramified
seventh-power packet. The constructors are:

- `awayCoordinateNormalForm_of_route`
- `ramifiedCoordinateNormalForm_of_packet`
- `coordinateCounterexampleRoute_of_pack`

The resulting `CoordinateCounterexampleRoute` retains exactly the away and
ramified branches of FLT7-009 while making their integer coordinates directly
available.

## Away exceptional factor

The away second-coordinate equality and its visible factor `7` prove

```text
7 ∣ y*z*(y+z).
```

Primitive endpoint coprimality excludes simultaneous divisibility of each
pair among `y`, `z`, and `y+z`. Therefore `AwayExceptionalFactor` gives the
exact one-hot trichotomy:

- right/Y factor: `7 ∣ y`, but not `z` or `y+z`;
- left/Z factor: `7 ∣ z`, but not `y` or `y+z`;
- sum factor: `7 ∣ y+z`, but not `y` or `z`.

No residue-triple enumeration is used.

## Four endpoint residue sectors

`fermat7Equation_modSeven_linear` applies Frobenius to reduce the Fermat
equation to `x+y=z` in `ZMod 7`. Combining it with the coordinate route and
one-hot factor proves `sevenEndpointResidueSector_of_counterexample`, whose
constructors are exactly:

```text
Ramified: (x,y,z) = (0,t,t)
Away-Y:   (x,y,z) = (t,0,t)
Away-Z:   (x,y,z) = (-t,t,0)
Away-Sum: (x,y,z) = (-2t,t,-t)
```

Each constructor includes `t != 0`; this follows from the established
primitive endpoint coprimality/nondivisibility data.

## Verification

The following checks passed:

- focused builds of all three new modules;
- `lake build DkMath.FLT.Seven`;
- both focused test files via `lake env lean`;
- `lake build DkMath.FLT`;
- forbidden-token scan over the new modules and tests;
- `git diff --check`.

The focused axiom audit reports only
`[propext, Classical.choice, Quot.sound]`. No `sorry`, `admit`, custom axiom,
or `native_decide` was introduced. Existing unrelated research modules still
emit their pre-existing `sorry` warnings during the broad FLT build.

## Recommended FLT7-011 boundary

Measure the exact additional `7`-adic load in the away second-coordinate
equation. Combine

```text
seventhPowerSnd = 7*v*SndCore,
7 ∤ SndCore,
```

with the unique exceptional endpoint factor to obtain a valuation-transfer
statement or an explicit strict size transformation. It should not be called
a descent until the target packet and its strictly decreasing measure have
both been defined and proved.
