# KUS observation bridge implementation report

Date: 2026-08-20
Branch: `wip/structural-arithmetic-red-ribbon-260818-v0`
Baseline HEAD: `8322e61bd04ff78380c7bdde1dae1c30749994a7`

## Baseline and inspected scope

The worktree was clean before this implementation. The existing Phase A-C
modules built successfully:

- `PowerGauge.lean`;
- `PrimeCoordinates.lean`;
- `InterPeriod.lean`;
- the `StructuralArithmetic` aggregate.

The design inspection covered the StructuralArithmetic modules, KUS `Coeff`,
`Scale`, and `Transport`, KUS bridge design specifications, and the existing
`CosmicBridge` / `DynamicArithmeticSequence` concrete APIs. No existing
`ObservationSpec` or observer API was present.

## Design decision

The bridge uses a small `ObservationSpec` with one field:

```text
coordinates : US U Blueprint -> ι -> Nat
```

`rawObservation` applies this field to `extract_g`, preserving the raw typed
KUS source. `observePeriod` applies the already public
`projectCoordinates`; it does not define a second modular calculus.

An alternative prime-specific observer was rejected because arbitrary KUS
blueprints are not intrinsically valuation structures. A global theorem that
all `ScaleSpec` transports preserve observations was also rejected: that claim
is false for representation-dependent coordinates. The semantic law is instead
the explicit proposition `ObservationCompatible`.

## New module and public API

New module:

`DkMath/NumberTheory/StructuralArithmetic/KUSObservation.lean`

Definitions:

- `ObservationSpec`;
- `rawObservation`;
- `observePeriod`;
- `ObservationCompatible`;
- `cosmicUnitObservation`.

Theorem-level contracts:

- `rawObservation_mkGWith`;
- `observePeriod_period_zero`;
- `observePeriod_period_one`;
- `observePeriod_eq_project`;
- `observePeriod_project_of_dvd`;
- `rawObservation_scaleGKUS_of_compatible`;
- `observePeriod_scaleGKUS_of_compatible`;
- `rawObservation_cosmicTerm`;
- `observePeriod_cosmicTerm`;
- `cosmicUnitObservation_id_compatible`.

Every new public declaration has a Lean docstring. Period zero remains the raw
view, period one remains complete observable collapse, and coarsening reuses
`projectCoordinates_project_of_dvd`.

## Concrete witness

The witness is the existing
`DkMath.KUS.CosmicBridge.cosmicTerm d k : GKUS Nat Nat DHNTBlueprint`. Its
support unit is the dimension `d`; `cosmicUnitObservation` reads that retained
unit as a coordinate indexed by `Unit`. Consequently the raw observation is
`fun _ => d`, while the period-`p` view is `fun _ => d % p`. This demonstrates
source retention, a nonconstant support-derived coordinate, and deliberate
periodic loss without pretending that `DHNTBlueprint` is a prime-factorization
API.

The identity `ScaleSpec` is supplied as a concrete compatible transport. General
transport compatibility remains conditional on `ObservationCompatible`.

## Verification

Baseline commands, all successful:

```text
lake build DkMath.NumberTheory.StructuralArithmetic.PowerGauge
lake build DkMath.NumberTheory.StructuralArithmetic.PrimeCoordinates
lake build DkMath.NumberTheory.StructuralArithmetic.InterPeriod
lake build DkMath.NumberTheory.StructuralArithmetic
```

Post-edit commands:

```text
lake build DkMath.NumberTheory.StructuralArithmetic.KUSObservation
lake build DkMath.NumberTheory.StructuralArithmetic
git diff --check
```

The two Lean builds and `git diff --check` succeeded. The shell emitted the
known non-blocking `/opt/wonderful/bin/wf-env: Permission denied` environment
message.

The new source contains no `sorry`, project-specific `axiom`, or `unsafe`
escape. An axiom audit is performed on the new public theorems after the final
aggregate build; only imported Lean/Mathlib foundational axioms are acceptable.

## Next gap

The next load-bearing gap is the primitive multiplicative-direction and
finite-prime-escape layer, while preserving the distinction from the existing
Erdos-style `PrimitiveSet`.
