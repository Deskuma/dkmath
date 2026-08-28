# Structural Arithmetic inter-period implementation report

Date: 2026-08-20
Branch: `wip/structural-arithmetic-red-ribbon-260818-v0`
Baseline HEAD: `6d63e46c904334185b21190f3bb2388278ee6ba9`

## Baseline inspected

The worktree was clean. `PowerGauge`, `PrimeCoordinates`, and the public
`StructuralArithmetic` aggregate all built successfully before editing.
Phases A and B were already implemented, although the integration README still
described the prime-coordinate bridge as future work. No inter-period module or
theorem was present.

The preflight also confirmed the relevant boundaries in KUS, the existing
Erdos-style `PrimitiveSet`, finite-prime escape, generic `GN`, specialized
`GN5`, and golden-unit fifth-power classification. Those areas were not changed.

## Files changed

- `DkMath/NumberTheory/StructuralArithmetic/InterPeriod.lean` — new theorem
  layer and Lean docstrings;
- `DkMath/NumberTheory/StructuralArithmetic.lean` — public aggregation;
- `docs/dev/StructuralArithmetic-RedRibbon-260818-v0/README.md` — phase and
  architecture status;
- this report.

## New theorems

- `projectExponent_project_of_dvd`;
- `projectCoordinates_project_of_dvd`;
- `SamePowerSector.of_dvd`;
- `SamePowerStructure.of_dvd`;
- `projectPrimeCoordinates_coarsen_of_dvd`;
- `projectPrimeCoordinates_eq_of_dvd`.

Every new public theorem has a Lean docstring. The module documentation records
the raw/projected distinction and the period-zero and period-one behavior.

## Mathematical contract

For natural periods with `m ∣ d`, repeated projection satisfies

```text
(n % d) % m = n % m.
```

The implementation uses Mathlib's `Nat.mod_mod_of_dvd`, lifts it pointwise to
arbitrary coordinate functions, and specializes it to prime-valuation
coordinates. Equality at period `d` therefore descends to equality at period
`m`. The implication is intentionally one-way: the API neither reconstructs a
raw source nor claims that equality at a coarser period lifts to a finer one.

No nonzero-period restriction is imposed. When `m = 0`, `m ∣ d` forces `d = 0`;
when `m = 1`, the result is the established total collapse.

## Verification

Baseline commands, all successful:

```text
lake build DkMath.NumberTheory.StructuralArithmetic.PowerGauge
lake build DkMath.NumberTheory.StructuralArithmetic.PrimeCoordinates
lake build DkMath.NumberTheory.StructuralArithmetic
```

Post-edit verification:

```text
lake build DkMath.NumberTheory.StructuralArithmetic.InterPeriod
lake build DkMath.NumberTheory.StructuralArithmetic
```

Both commands completed successfully. The build emitted no source linter
warning for the new module. `#print axioms` reported only Lean/Mathlib
foundational axioms already used by the imported equality/function and
prime-coordinate machinery (`propext`, `Quot.sound`, and, for the prime
specializations, `Classical.choice`); it reported no project-specific or newly
introduced axiom.

## Remaining gap

The primary next gap is a small KUS observation specification that retains a
raw `GKUS` support/source while deriving StructuralArithmetic coordinates and
their period projection. Compatibility with `ScaleSpec` must remain an explicit
hypothesis; arbitrary KUS blueprints are not intrinsically prime-coordinate
systems.
