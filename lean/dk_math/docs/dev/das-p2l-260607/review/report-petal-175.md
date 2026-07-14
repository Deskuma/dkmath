# Report Petal 175

## Checkpoint

`cp: 175`

Main root only: adjacent-diagnosis split preflight report.

## Result

This checkpoint is a refactor preflight only.

No Lean declarations were moved.  No new Lean module was created.  No
declaration names were changed.

Created:

```text
docs/dev/das-p2l-260607/refactor/pressure-adjacent-diagnosis-split-plan.md
```

## Split Plan Summary

`PressureAccounting.lean` currently has about 3773 lines.

The adjacent-diagnosis surface is concentrated around the following cluster:

- `SourcePressureLocalIslandWitnessAdjacentDiagnosis`
- `SourcePressureLocalIslandWitnessAdjacentPairInList`
- `SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis`
- bounded wrappers for three-, four-, and five-witness lists;
- projection and propagation helpers.

The proposed future direction is staged:

1. Keep `PressureAccounting.lean` as the compatibility surface.
2. Extract low-risk declarations only after dependency checks.
3. Prefer extracting the adjacent-pair address predicate first, because it has
   the smallest dependency surface.
4. Move the adjacent diagnosis carrier only after overlap-obstruction and
   pair-budget dependencies are stable.
5. Move bounded wrappers last.

## Key Risk

The main technical risk is import cycles.  The bounded wrappers depend on
one-step and bounded diagnosis theorems already in `PressureAccounting.lean`,
so moving them too early may drag most of the file into the new module.

## Recommended Next Checkpoint

Recommended next checkpoint:

```text
Design or implement the first low-risk extraction:
SourcePressureLocalIslandWitnessAdjacentPairInList and its immediate API.
```

This should be done only if the upstream witness carrier is already available
without importing `PressureAccounting.lean` back into the new module.  If that
dependency boundary is not clean, the next checkpoint should instead identify
the smallest upstream witness/address module needed before extraction.

## Boundary

This checkpoint did not introduce:

- arbitrary-length classifier;
- fuel-indexed diagnosis;
- sorting;
- coverage;
- maximality;
- uniqueness;
- prefix behavior;
- union accounting;
- interval merging;
- Collatz convergence.

Recovered budgets remain pair-local.  Overlap remains an adjacent obstruction
on the enclosing list.

## Verification

Builds completed:

```text
lake build DkMath.Collatz.PetalBridge.PressureAccounting
lake build DkMath.Collatz.PetalBridge.PressureFrontier
lake build DkMath.Collatz.PetalBridge
```

No-sorry checks completed for:

```text
lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean
```

Whitespace check completed:

```text
git diff --check
```

The build still reports the existing unrelated warning:

```text
DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:152:6:
declaration uses `sorry`
```
