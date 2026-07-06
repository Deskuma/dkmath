# report-petal-217

## Situation

Checkpoint petal-217 asked whether the local Beam mass-balance classifier
should expose a compact three-way decision surface:

```text
left < right
left = right
right < left
```

cp216 already provided the individual classifiers:

```text
nextMargin > 0 iff left < right
nextMargin = 0 iff left = right
nextMargin < 0 iff right < left
```

The question was whether a compact trichotomy theorem would reduce future proof
noise or merely duplicate ambient order facts.

## API Decision

I added one compact addressed-edge trichotomy wrapper.

I did not add a raw mass-balance-only trichotomy theorem, because that would
mostly duplicate `lt_trichotomy` for integers.  The useful theorem is the
paired local classifier: each mass-balance case is returned together with the
corresponding next-margin sign.

## Added Theorem

Implemented in `DkMath.Collatz.PetalBridge.PressureBeam`:

```lean
sourcePressureMargin_next_sign_massBalance_trichotomy_of_addressedDepthTarget
```

It returns:

```text
(nextMargin > 0 and left < right)
or
(nextMargin = 0 and left = right)
or
(nextMargin < 0 and right < left)
```

This packages the local decision surface without claiming any propagation.

## Classification

True Beam:

- the positive branch is paired with `left < right`

Boundary:

- the zero branch is paired with `left = right`

False Beam:

- the negative branch is paired with `right < left`

Gap:

- this theorem does not provide the upstream source of the mass-balance
  inequality
- it only classifies one addressed edge once the local quantities are known

## Guardrails

This checkpoint is local decision-surface analysis, not propagation.

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

The local classifier is now essentially closed:

```text
nextMargin = right - left
```

and the three sign cases are packaged.

The next major investigation should likely move upstream and ask where
`left < right`, `left = right`, or `right < left` comes from:

```text
mass-balance inequality source
```

Candidate upstream modules:

- `PressureAccounting`
- `DriftBudget`
- `PressureFrontier`
- local-island witness structure

This is a source-of-inequality question, not another local classifier
normalization.

## Experimental Lemma Table

| experiment | status | result |
| --- | --- | --- |
| raw mass-balance trichotomy | skipped | would mostly duplicate `lt_trichotomy` |
| addressed paired trichotomy | passed | `sourcePressureMargin_next_sign_massBalance_trichotomy_of_addressedDepthTarget` |
| propagation | intentionally not added | outside checkpoint scope |
| upstream inequality source | open | next investigation target |

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
