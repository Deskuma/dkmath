# PUU-L031 — Square-Shifted Survivor Offset Profile

## Status

PUU-L031 is implemented as a provider-side finite cyclic translation layer.
The preceding L030 mixed-radix audit remains the bounded coordinate baseline;
this checkpoint returns to the square shell `n^2 + t` and records how its
whole-period non-reservation pattern depends on the square anchor phase.

## Implemented module

`DkMath/NumberTheory/PrimorialUniverse/SquareAnchorOffsetProfile.lean`

The module defines `squareAnchorUnreservedOffsetProfile S n` as the filter of
`Finset.range (finitePrimeBasisProduct S)` consisting of offsets `t` for which
`n^2 + t` is not reserved by the finite prime basis.  The public theorem
`mem_squareAnchorUnreservedOffsetProfile_iff` gives the direct bounded
membership form:

```text
t < M ∧ ¬ ReservedByPrimeBasis S (n^2 + t).
```

For a nonempty finite basis, the translated-survivor theorem
`mem_squareAnchorUnreservedOffsetProfile_iff_translatedSurvivor` proves:

```text
t ∈ Profile(S,n)
  ↔ t < M ∧
      IsPrimeBasisWheelSurvivor S ((A_n + t) % M),
```

where `A_n = squareAnchorWheelProjection S n`.  The companion theorem
`mem_squareAnchorUnreservedOffsetProfile_iff_survivor` exposes the same fact
using the existing `primeBasisWheelSurvivors` Finset.  The proof reuses
`squareShell_not_reserved_iff_projection_survivor` and
`squareShellWheelProjection_eq_anchor_add`; no divisibility characterization
is duplicated.

## Whole-period results

`card_squareAnchorUnreservedOffsetProfile` proves

```text
|Profile(S,n)| = |primeBasisWheelSurvivors(S)|
```

for every nonempty finite prime basis.  The proof uses the explicit cyclic map
`t ↦ (A_n + t) % M` and its inverse on the bounded period.  It does not
introduce an Euler-phi identification.

`squareAnchorUnreservedOffsetProfile_eq_of_sameAnchorPhase` proves equality
of profiles whenever `SameSquareAnchorPhase S a b` holds, by reusing the
existing same-phase reservation equivalence.

`mem_squareAnchorUnreservedOffsetProfile_succ_iff` derives the successor law
from `squareAnchorWheelProjection_succ`.  For an offset `t < M`, the exact
orientation is:

```text
t ∈ Profile(S,n+1)
  ↔ ((t + (2*n+1)) % M) ∈ Profile(S,n).
```

Thus the profile is the inverse cyclic translate by the odd square increment.

## Visible regression

`squareAnchorUnreservedOffsetProfile_two_three_regression` checks the
`S = {2,3}`, `M = 6` case using public profile and phase APIs:

```text
n = 1: A_n = 1
n = 2: A_n = 4
n = 5: A_n = 1
```

It proves that profiles at `1` and `5` are equal, the profile at `2` differs
already at offset `0`, and for every bounded `t < 6` the successor transport
from `n = 1` to `n = 2` has the displayed forward orientation with increment
`3`.

## Boundary and information content

The new formal information is exactly the quadratic coupling:

```text
raw bounded offsets:      t ∈ [0,M)
square-shell profile:     t ↦ (n^2 + t) mod M
reachable profile labels: n^2 mod M
```

The module does not define or import Legendre consumers, `SquareCell`,
`SquareOffset`, or `escapingSquareOffsets`.  It proves no bound such as
`t ≤ 2*n`, no escape or square-shell prime existence, no Jacobsthal or wheel
gap theorem, no neutral-seat primality statement, and no PNT/RH,
PowerSwap/GN/CosmicFormula consequence.

## Conclusion

L031 produced no information beyond the fixed wheel-survivor pattern plus
square-phase-dependent cyclic translation.  In particular, whole-period
cardinality and phase/successor transport do not provide a short-prefix or
first-hit conclusion.  The next bounded audit should therefore address the
short-prefix / first-hit interaction of quadratic shifts rather than add
further whole-period translation identities.

## Verification

The focused target

```text
lake build DkMath.NumberTheory.PrimorialUniverse.SquareAnchorOffsetProfile
```

completed successfully, including the imported dependency chain.  The final
focused build after the docstring and regression cleanup emitted no Lean
warnings.

