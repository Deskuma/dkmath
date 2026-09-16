# LUNA-005 — fixed-(S,u) Mordell incidence ledger

This checkpoint freezes the exact finite decomposition of shell witnesses by
the fixed positive Mordell parameters `(S,u)`. Each parameter fiber maps to a
finite coordinate image, and every image point satisfies the corresponding
Mordell equation. No integral-point estimate or analytic provider is added.

## 1. Files changed

Added [GNExcessCubicMordellIncidence.lean](../../../DkMath/ABC/GNExcessCubicMordellIncidence.lean)
and imported it from `DkMath/ABC.lean` immediately after
`GNExcessCubicMordellTransport`. The focused and aggregator build logs are
retained in [lean-005-output.txt](lean-005-output.txt) and
[build-005-abc-output.txt](build-005-abc-output.txt). The validation record is
[validation-005.txt](validation-005.txt).

The production module imports only
`DkMath.ABC.GNExcessCubicMordellTransport`.

## 2. Mordell parameter definition

`GNExcessCubicMordellParameter a` is the transparent pair

```text
(GNExcessCubicComplement a,
 GNExcessCubicSquarefulQuotient (GNExcessCubicFullRepeatedModulus a))
```

It is the fixed coefficient pair `(S,u)` attached to a shell witness.

## 3. Represented parameter space

`GNExcessCubicRealizedLargeModulusShellMordellParameterSpace X D` is the
finite image of the shell witness space under that parameter map.
`mem_GNExcessCubicRealizedLargeModulusShellMordellParameterSpace_iff` gives the
exact witness-and-coordinate membership characterization.

## 4. Fixed parameter fiber

`GNExcessCubicRealizedLargeModulusShellMordellParameterFiber X D S u` is the
shell witness space filtered by `Complement a = S` and
`SquarefulQuotient (FullRepeatedModulus a) = u`.
Its membership theorem is exact, and every represented parameter has a
nonempty fiber.

## 5. Positivity packet

`GNExcessCubicRealizedLargeModulusShellMordellParameter_pos` proves
`0 < S ∧ 0 < u` for every represented `(S,u)`. Complement positivity is
derived from the production complement packet; quotient positivity is taken
from the realized square-cube packet.

## 6. Exact fiber partition

The fixed-parameter fibers are pairwise disjoint. The theorem
`GNExcessCubicRealizedLargeModulusShellWitnessSpace_eq_biUnion_mordellParameterFibers`
proves that their finite `biUnion` is exactly the shell witness space.

## 7. Witness-count ledger

`GNExcessCubicRealizedLargeModulusShellWitnessCount_eq_sum_mordellParameterFiberCards`
turns the partition into the exact finite identity

```text
ShellWitnessCount X D =
  ∑ (S,u) in represented parameters, #Fiber(X,D,S,u).
```

No parameter-count or fiber-size bound is asserted.

## 8. Coordinate definitions

For fixed `(S,u)` the module defines

```text
GNExcessCubicMordellZ S u a =
  4*S*u²*oddPart (FullRepeatedModulus a)
GNExcessCubicMordellY S u a = 4*S*u²*(2*a+3)
GNExcessCubicMordellCoordinate S u a = (Z,Y).
```

No elliptic-curve object is introduced.

## 9. Coordinate image

`GNExcessCubicRealizedLargeModulusShellMordellCoordinateSpace X D S u` is the
finite image of the fixed parameter fiber under the coordinate map.
Its membership theorem states exactly that a pair `(Z,Y)` is represented by a
fiber witness with the displayed coordinate equalities.

## 10. Fixed Mordell equation theorem

`GNExcessCubicRealizedLargeModulusShellMordellCoordinateSpace_equation` proves
for every image point

```text
Y² + 48*S²*u⁴ = Z³.
```

The proof recovers the production witness, rewrites its canonical `S` and
`u` using the fiber equalities, and consumes the LUNA-004 production Mordell
identity. The converse direction is intentionally absent.

## 11. Coordinate injectivity

For represented positive `(S,u)`, coordinate equality gives equality of the
odd-part coordinate and of `2*a+3`. The theorem
`mordellCoordinates_injective_fixed_SU` then yields equality of the witnesses.
This is a fixed-parameter cancellation result only.

## 12. Coordinate image card identity

`GNExcessCubicRealizedLargeModulusShellMordellCoordinateSpace_card` proves

```text
#CoordinateSpace(X,D,S,u) = #ParameterFiber(X,D,S,u)
```

for every represented parameter. It uses `Finset.card_image_of_injOn` and
the fixed-`(S,u)` injectivity theorem.

## 13. Two-level total card ledger

`GNExcessCubicRealizedLargeModulusShellWitnessCount_eq_sum_mordellCoordinateCards`
combines the fiber partition and image-card identity:

```text
ShellWitnessCount X D =
  ∑ (S,u) in represented parameters,
    #CoordinateSpace(X,D,S,u).
```

This is the requested exact production interface for future analytic work.

## 14. Optional `(r,S)` relation status

Skipped. LUNA-003 already exposes the independent exact `(r,S)` ledger, and
no additional equivalence is needed for this fixed-`(S,u)` checkpoint.

## 15. Explicit no-counting boundary

PROVED:

- shell witnesses partition exactly by fixed `(S,u)`;
- represented parameters are positive;
- each fixed fiber maps injectively to its exact finite Mordell coordinate
  image;
- every image point satisfies `Y² + 48*S²*u⁴ = Z³`;
- the shell witness count equals the sum of the coordinate-image cards.

NOT PROVED:

- equality with all integral points on a Mordell curve;
- any integral-point count or uniform bound in `S,u`;
- Helfgott--Venkatesh, rank estimates, or moment estimates;
- balanced-box power saving;
- ABC.

## 16. Focused build

The required command passed:

```text
lake build DkMath.ABC.GNExcessCubicMordellIncidence
```

The output is retained in [lean-005-output.txt](lean-005-output.txt), ending
with `Build completed successfully (8800 jobs).`.

## 17. ABC aggregator build

The required command passed:

```text
lake build DkMath.ABC
```

The output is retained in [build-005-abc-output.txt](build-005-abc-output.txt),
ending with `Build completed successfully (8864 jobs).`.

## 18. Forbidden scan

The changed production module was scanned for
`sorry`, `admit`, `axiom`, `abc_main_axiom`, `native_decide`, and `unsafe`.
No occurrences were found. No analytic provider class, axiom, or external
point-counting theorem was introduced.

## 19. Axiom audit

The principal declarations report the expected trust boundary
`[propext, Classical.choice, Quot.sound]` (or a subset). The focused output
contains no `sorryAx` for the new declarations.

Audited declarations include parameter membership, fiber nonemptiness and
partition, the fixed Mordell equation, coordinate image-card identity, and
the two-level total card ledger.

## 20. Remaining research frontier

The formal production boundary now ends at the exact finite ledger

```text
ShellWitnessCount X D =
  ∑ represented (S,u),
    # { production Mordell coordinates (Z,Y) }
```

with every coordinate satisfying `Y² + 48*S²*u⁴ = Z³`. Characterizing or
bounding all integral points, importing Helfgott--Venkatesh or rank input,
obtaining moment or balanced-box estimates, and proving ABC remain open.
LUNA-006 is not opened automatically.
