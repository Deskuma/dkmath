# Primitive direction / finite escape implementation report

Date: 2026-08-20
Branch: `wip/structural-arithmetic-red-ribbon-260818-v0`
Baseline HEAD: `72ffa947` (directive checkpoint)

## Baseline and inspected scope

The StructuralArithmetic Phase A-D tower was clean and build-checked before
editing. The inspection covered `PowerGauge`, `PrimeCoordinates`,
`InterPeriod`, `KUSObservation`, the current README and reports, the full
`PrimitiveSet` / `PrimitiveBeam` boundary APIs, Hackathon finite-prime escape
files, `UniqueFactorizationGN`, and existing factorization-support lemmas.

The worktree contained only the preceding StructuralArithmetic checkpoint.

## Representation decision

The implementation uses prime-divisor semantics rather than
`Submonoid.closure`:

```text
PrimeScaleGeneratedBy S n :=
  n ≠ 0 ∧ ∀ q, Nat.Prime q → q ∣ n → q ∈ S
```

This directly matches the existing `FreshPrimeFactor` provider and avoids a
new general commutative-monoid generation layer. `KnownPrimeScales S` records
the required interpretation that every member of `S` is prime. The closure
alternative was rejected because it adds machinery without improving the
finite prime-support theorem needed here.

The new `FreshPrimeDirection` is intentionally separate from both
`PrimitiveSet.PrimitiveOn` (Erdos divisibility antichain) and
`PrimitiveBeam.PrimitivePrimeFactorOfDiffPow` (first occurrence across power
differences).

## New modules and declarations

`PrimitiveDirection.lean`:

- `KnownPrimeScales` and `KnownPrimeScales.prime_of_mem`;
- `PrimeScaleGeneratedBy`;
- `FreshPrimeDirection`;
- `primeScaleGeneratedBy_one`;
- `primeScaleGeneratedBy_prime_iff_mem`;
- `freshPrimeDirection_of_prime_dvd_not_mem`;
- `not_primeScaleGeneratedBy_of_freshPrimeDirection`.

`FinitePrimeEscapeBridge.lean`:

- `freshPrimeFactor_to_freshPrimeDirection`;
- `freshPrimeFactor_not_primeScaleGeneratedBy`;
- `exists_freshPrimeFactor_not_primeScaleGeneratedBy`;
- `GN5_escape_has_freshPrimeDirection`;
- `GN5_escape_not_primeScaleGeneratedBy_two_three_five`;
- `knownPrimeScales_two_three_five`.

Every new public declaration has a Lean docstring. The public aggregate imports
both modules after the existing Phase A-D modules.

## Existing escape bridge and GN5 witness

The bridge consumes `DkMath.Hackathon.finitePrimeEscape_hits_GN5` directly and
does not reprove the product-plus-offset arithmetic or recompute the GN5 value.
It formally derives:

```text
¬ PrimeScaleGeneratedBy ({2, 3, 5}) (GN 5 1 1)
```

and separately exposes the existential fresh-direction witness. The known set
`{2, 3, 5}` is proved to satisfy `KnownPrimeScales`.

No KUS theorem was added: the current KUS observer reads a dimension support,
not ordinary prime-factor coordinates, so forcing a KUS-to-prime bridge here
would violate the established source/observation distinction.

## Verification

Baseline commands, all successful:

```text
lake build DkMath.NumberTheory.StructuralArithmetic.PowerGauge
lake build DkMath.NumberTheory.StructuralArithmetic.PrimeCoordinates
lake build DkMath.NumberTheory.StructuralArithmetic.InterPeriod
lake build DkMath.NumberTheory.StructuralArithmetic.KUSObservation
lake build DkMath.NumberTheory.StructuralArithmetic
```

Phase E commands:

```text
lake build DkMath.NumberTheory.StructuralArithmetic.PrimitiveDirection
lake build DkMath.NumberTheory.StructuralArithmetic.FinitePrimeEscapeBridge
lake build DkMath.NumberTheory.StructuralArithmetic
git diff --check
```

All commands succeeded. The Hackathon bridge transitively replays the existing
`ZsigmondyCyclotomicResearch.lean` warning that one pre-existing declaration
uses `sorry`; the new Phase E files contain no `sorry`, `admit`, `axiom`, or
`unsafe` escape. No project-specific axiom was introduced.

## Next gap

The next load-bearing gap is a generic GN / GN5 structural bridge. It should
consume the now-stable raw prime-direction and escape vocabulary without
identifying it with PowerGauge period projection or arbitrary KUS observations.
