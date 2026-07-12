# report-petal-216

## Situation

Checkpoint petal-216 asked whether the named mass-balance API from cp215 should
expose an equality boundary surface.

cp215 had:

```text
True:
  next positive iff left < right

False:
  next nonpositive iff right <= left
```

The equality surface

```text
left = right
```

is already included in the False Beam side by `right <= left`, but it was not
yet clear whether equality had a sharper meaning.

## Inspection and Lean Result

Lean confirms a stronger exact relation:

```text
nextMargin = right - left
```

Therefore equality is not merely a weak False-side case.  It is the exact zero
boundary:

```text
nextMargin = 0 iff left = right
```

So the equality boundary deserved a small named API.

## Added Exact Relation

Implemented in `DkMath.Collatz.PetalBridge.PressureBeam`:

```lean
sourcePressureMargin_next_eq_massBalanceRight_sub_left
```

This proves:

```text
nextMargin = right - left
```

The proof unfolds the named mass-balance sides and `SourcePressureMarginInt`
and closes by `ring`.

## Boundary Beam

Implemented:

```lean
sourcePressureMargin_next_eq_zero_iff_massBalanceLeft_eq_right
sourcePressureMargin_next_eq_zero_of_massBalanceLeft_eq_right
```

These prove that equality of the named mass-balance sides is exactly the
zero-margin boundary.

## False Beam Boundary

Implemented:

```lean
sourcePressureMargin_next_nonpos_of_massBalanceLeft_eq_right
not_sourcePressureMargin_next_pos_of_massBalanceLeft_eq_right
```

These make explicit that equality belongs to the False Beam side and rules out
the positive side.

## Strict False Beam

Implemented:

```lean
sourcePressureMargin_next_neg_iff_massBalanceRight_lt_left
```

This separates strict failure from boundary failure:

```text
nextMargin < 0 iff right < left
```

So the local Beam picture is now:

```text
left < right   -> positive
left = right   -> zero boundary
right < left   -> negative
```

## Classification

True Beam:

- positive side remains `left < right`

False Beam:

- nonpositive side remains `right <= left`
- equality boundary gives `nextMargin = 0`
- strict false side is `right < left`

Gap:

- no global behavior follows from these local classifiers
- the addressed edge still only says where the comparison is being read

## Guardrails

This checkpoint is boundary-surface analysis, not propagation.

No theorem was added for:

- time or orbit propagation
- arbitrary target transport
- arbitrary next positivity
- canonical target selection
- global coverage
- convergence
- aggregation
- overlap repair

## Wise Wolf Inference

The next natural API layer could package the three-way local decision surface:

```text
left < right
left = right
right < left
```

as a small trichotomy theorem or as separate caller-friendly wrappers.  That
would still be local classification only, but it would make future obstruction
reports more precise.

## Experimental Lemma Table

| experiment | status | result |
| --- | --- | --- |
| exact relation | passed | `nextMargin = right - left` |
| equality boundary | passed | `nextMargin = 0 iff left = right` |
| boundary implies false side | passed | equality gives `nextMargin <= 0` |
| boundary excludes true side | passed | equality gives `¬ 0 < nextMargin` |
| strict false side | passed | `nextMargin < 0 iff right < left` |
| propagation | intentionally not added | outside checkpoint scope |

## Verification

Commands run:

```text
lake build DkMath.Collatz.PetalBridge.PressureBeam
lake build DkMath.Collatz.PetalBridge
rg -n "\bsorry\b|admit" DkMath/Collatz/PetalBridge/PressureBeam.lean DkMath/Collatz/PetalBridge/PressureAutomaton.lean DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean DkMath/Collatz/PetalBridge/PressureAccounting.lean DkMath/Collatz/PetalBridge/PressureFrontier.lean DkMath/Collatz/PetalBridge/PressureDecay.lean DkMath/Collatz/PetalBridge/DriftBudget.lean
git diff --check
```

Results:

- `lake build DkMath.Collatz.PetalBridge.PressureBeam`: passed
- `lake build DkMath.Collatz.PetalBridge`: passed
- no-sorry check on the listed pressure files: no matches
- `git diff --check`: passed

Known unrelated build warning remains:

```text
DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:152:6:
declaration uses `sorry`
```
