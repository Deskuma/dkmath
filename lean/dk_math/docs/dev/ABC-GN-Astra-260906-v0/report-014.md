# LUNA-014 — square-cube / Pell-parameter incidence ledger

## Scope and files

This checkpoint freezes the canonical squareful quotient, its square-times-cube
identity, and the exact finite partition of a realized dyadic shell by the
squarefree Pell parameter `T = oddPart M * S`. It adds no cardinality estimate,
Pell solution bound, incidence sparsity theorem, provider assumption, or use of
`abc_main_axiom`.

Changed files:

- `DkMath/ABC/GNExcessCubicPellParameterIncidence.lean`
- `DkMath/ABC.lean` (public import)
- `README.md`, `ROADMAP.md`, `validation-014.txt`, and this report.

## Canonical square-cube coordinates

`GNExcessCubicSquarefulQuotient M` is the canonical natural quotient
`evenPart M / oddPart M`. For nonzero squareful `M`,
`evenPart_eq_oddPart_mul_GNExcessCubicSquarefulQuotient` proves the exact
reconstruction

```text
evenPart M = oddPart M * GNExcessCubicSquarefulQuotient M.
```

Reusing the LUNA-013 odd/even packet, the theorem
`squareful_eq_squareQuotient_sq_mul_oddPart_cube` then gives

```text
M = (GNExcessCubicSquarefulQuotient M)^2 * (oddPart M)^3.
```

The realized-modulus packet exposes positivity of `M`, `oddPart M`, and the
canonical quotient, together with squarefullness, squarefreeness of the odd
part, and the exact identity. The generic theorem
`oddPart_cube_le_of_squarefull` records `(oddPart M)^3 ≤ M`; its shell consumer
`GNExcessCubicRealizedLargeModulusShell_oddPart_cube_lt` derives the strict
bound `(oddPart M)^3 < 2*D` from `M < 2*D`.

## Pell parameter space and support packet

`GNExcessCubicPellParameter (M,S)` is the direct pair map
`oddPart M * S`. Its image defines
`GNExcessCubicRealizedLargeModulusShellPellParameterSpace X D`, with an exact
membership equivalence against represented incidence pairs. Every represented
parameter is positive and squarefree. The packet
`GNExcessCubicRealizedLargeModulusShellPellParameter_packet` exposes

```text
T = r*S,       r = oddPart M,
Squarefree r,  r^3 < 2*D,
1 ≤ S ≤ X.
```

No injectivity of the pair-to-parameter map is asserted.

## Parameter fibers and fixed-T equation

`GNExcessCubicRealizedLargeModulusShellPellParameterFiber X D T` filters the
shell witness space by

```text
oddPart (GNExcessCubicFullRepeatedModulus a)
  * GNExcessCubicComplement a = T.
```

The module proves its exact membership theorem and nonemptiness for every
represented `T`. Distinct represented parameters have pairwise disjoint
fibers, and

```text
PellParameterSpace X D).biUnion (fun T => PellParameterFiber X D T)
  = shellWitnessSpace X D.
```

Consequently,
`GNExcessCubicRealizedLargeModulusShellWitnessCount_eq_sum_pellParameterFiberCards`
provides the exact fourth fiber-card sum. The fixed-parameter equation is

```text
(2*a + 3)^2 + 3
  = 4*T*(evenPart (FullRepeatedModulus a))^2
```

for every witness in the corresponding fiber.

## Four-way ledger

`GNExcessCubicRealizedLargeModulusShell_four_way_card_ledger` combines the
existing modulus-fiber sum, complement-fiber sum, incidence-pair cardinality,
and the new Pell-parameter fiber sum. This is an exact finite re-indexing
identity; it does not estimate any of its terms.

## Verification and trust boundary

The focused module and public aggregator were rebuilt. The new Lean source has
no `sorry`, `admit`, new `axiom`, `abc_main_axiom`, or `native_decide`. Audited
declarations use only the standard Lean boundary (`propext`,
`Classical.choice`, and `Quot.sound`, or subsets thereof).

The formalized endpoint remains finite and structural. No theorem here counts
Pell solutions at fixed `T`, bounds the number of represented parameters,
proves incidence sparsity, or couples this ledger to an ABC quality estimate.
