# LUNA-011 — realized witness/incidence extraction

## Scope and files

This checkpoint makes the exact witness/fiber meaning of the LUNA-010 shell
count explicit. It introduces no shell-count estimate, fiber-cardinality
bound, or ABC closure.

Changed production files:

- `DkMath/ABC/GNExcessCubicRealizedIncidence.lean`
- `DkMath/ABC.lean` (public import)

Changed campaign records:

- `README.md`, `ROADMAP.md`, `validation-011.txt`, and this report.

## Witness map and exact images

`GNExcessCubicFullRepeatedModulus a` names the existing canonical full
repeated part `GNNonExceptionalRepeatedPart 3 a 1`.
`GNExcessCubicRealizedLargeWitnessSpace X` is the finite set of `1 ≤ a ≤ X`
whose full repeated modulus exceeds `X+1`.

The theorem
`GNExcessCubicRealizedLargeWitnessSpace_image_eq_modulusSpace` proves the
exact finite-set equality

```text
image fullRepeatedModulus (largeWitnessSpace X)
  = GNExcessCubicRealizedLargeModulusSpace X.
```

The forward direction uses the LUNA-009 full-repeated membership bridge. The
reverse direction uses the existing positive realized-modulus witness theorem.
No injectivity is used.

`GNExcessCubicRealizedLargeModulusShellWitnessSpace X D` filters these points
by the same half-open `[D,2D)` modulus shell. Its image theorem,
`GNExcessCubicRealizedLargeModulusShellWitnessSpace_image_eq_shell`, gives the
exact shell equality. Consequently,
`GNExcessCubicRealizedLargeModulusShellCount_le_witnessCount` records the only
automatic cardinal relation: image cardinality is at most source cardinality.

## Fibers and shell partition

`GNExcessCubicFullRepeatedWitnessFiber X M` is the exact equality fiber of the
full repeated-modulus map inside `[1,X]`. A realized modulus has a nonempty
fiber by `GNExcessCubicFullRepeatedWitnessFiber_nonempty_of_mem_modulusSpace`.

The exact finite partition theorem
`GNExcessCubicRealizedLargeModulusShellWitnessSpace_eq_biUnion_fibers` proves

```text
shellWitnessSpace X D
  = ⋃ M ∈ modulusShell X D, fullRepeatedWitnessFiber X M.
```

The fibers are pairwise disjoint by equality of their modulus coordinates.
`GNExcessCubicRealizedLargeModulusShellWitnessCount_eq_sum_fiberCards` then
proves the exact cardinal identity

```text
shellWitnessCount X D
  = ∑ M ∈ modulusShell X D, (fiber X M).card.
```

This records witness multiplicity explicitly instead of assuming the repeated
modulus map is injective. The LUNA-008 169 and 8281 collision regressions stay
in their existing test module and are not duplicated.

## Complement packet and spacing

For every shell witness,
`GNExcessCubicRealizedLargeModulusShellWitness_complement_packet` exposes
`1 ≤ a`, `a ≤ X`, `D ≤ M < 2D`, `X+1 < M`,

```text
M * GNExcessCubicComplement a = a^2 + 3*a + 3,
Squarefree (GNExcessCubicComplement a),
Nat.Coprime M (GNExcessCubicComplement a),
GNExcessCubicComplement a ≤ X.
```

It reuses the LUNA-008 canonical complement and sharp-bound theorems; no
factorization argument is duplicated.

`GNExcessCubicFullRepeatedWitnessFiber_spacing` specializes the existing
quadratic spacing theorem to two distinct points in one exact `M`-fiber:

```text
M ≤ (b-a) * (a+b+3).
```

`GNExcessCubicFullRepeatedWitnessFiber_spacing_le_interval` gives the direct
interval form `M ≤ (b-a)*(2*X+3)`. The optional
`GNExcessCubicFullRepeatedWitnessFiber_gap_gt_of_mul_lt_modulus` provides a
parameterized strict gap when `K*(2*X+3) < M`.

The whole-space sanity consequence
`GNExcessCubicRealizedLargeModulusSpace_card_le_witnessSpace_card` is also
proved; it is only the elementary image-cardinality inequality.

## Verification and trust boundary

Focused build:

```text
lake build DkMath.ABC.GNExcessCubicRealizedIncidence  PASS
```

ABC aggregator:

```text
lake build DkMath.ABC                               PASS
```

The principal image, shell partition, fiber-card, complement-packet, and
spacing declarations audit to `propext`, `Classical.choice`, and `Quot.sound`,
or a subset. No `sorry`, `admit`, new axiom, `abc_main_axiom`, or
`native_decide` was added.

## Remaining research frontier

The exact target is now explicit: derive a genuinely new arithmetic bound on
the number of distinct `M` in one dyadic shell, using the complement equation
and the exact spacing of each full-repeated fiber. This checkpoint supplies
only coordinates, images, fibers, and certificates; it does not estimate any
of their cardinalities.
