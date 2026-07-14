# report-petal-227

## Checkpoint

`petal-227-revised`

## Goal

Use the Pulse-level full diagnostic theorem as a strategic probe:

```lean
sourcePressureBeamPulse_witness_singleton_full_diagnostic
```

The theorem consumes one explicit witness membership:

```lean
W ∈ L
```

and packages the local singleton pulse diagnostic:

- entry: `left < right`;
- center/right: `SourcePressureBeamAddressedDepthTarget L ...`;
- exit: `right <= left`.

## Branches Taken

Branch B was taken first:

```text
caller exists but only has Beam seed
```

The smallest available higher-level caller is:

```lean
SourcePressureBeamSeed L
```

This caller does not itself present a named `W ∈ L` at the surface, and we
should not invent a canonical witness.  However, the existing seed machinery
already exposes an existential contained witness through:

```lean
exists_sourcePressureBeamSeedContainsDepth_of_seed
```

That gives:

```lean
∃ j, SourcePressureBeamSeedContainsDepth L j
```

and `SourcePressureBeamSeedContainsDepth L j` unfolds to:

```lean
∃ W ∈ L, W.val = j
```

So the seed can safely feed the full diagnostic existentially.

Branch C was then implemented as an experiment:

```text
failure resolution -> Beam seed wrapper -> existential witness diagnostic
```

This is valid because `SourcePressureBeamSeed L` is definitionally the
Beam-facing name for `SourcePressureFailureResolution L`.

## Added Theorem

Added in `DkMath.Collatz.PetalBridge.PressureBeam.Pulse`:

```lean
theorem exists_sourcePressureBeamPulse_witness_singleton_full_diagnostic_of_seed
```

Meaning:

```text
SourcePressureBeamSeed L
  -> exists W in L
       such that W's singleton pulse has the full local entry-depth-exit
       diagnostic.
```

The theorem consumes:

```lean
sourcePressureBeamPulse_witness_singleton_full_diagnostic
```

It does not rebuild the pulse facts manually.  It opens the seed existential,
keeps the extracted witness explicit, and applies the full diagnostic package
to that witness membership.

Also added:

```lean
theorem exists_sourcePressureBeamPulse_witness_singleton_full_diagnostic_of_failureResolution
```

Meaning:

```text
SourcePressureFailureResolution L
  -> exists W in L
       such that W's singleton pulse has the full local entry-depth-exit
       diagnostic.
```

This theorem intentionally stays in the Beam-facing Pulse layer.  It does not
move Beam vocabulary into `PressureAutomaton`; it only lets a caller that still
has the automaton/failure-resolution state enter the same existential
diagnostic surface.

## Branches Inspected But Not Taken

Branch A:

- No better existing caller with an already surfaced `W ∈ L` was found.
- The Pulse API itself has explicit-membership theorems, but adding another
  direct alias there would only duplicate the cp226 theorem.

Branch D:

- Multiple possible caller surfaces exist, but the seed route is the smallest
  one with the fewest new assumptions after explicit `W ∈ L`.
- Branch C was still added as a caller convenience for code that has not yet
  switched to Beam seed vocabulary.

Branch E:

- No contradiction or useful local negative theorem was discovered.

Branch F:

- Not applicable.  A valid caller route exists through the Beam seed.

## Classification

True Beam:

- `W ∈ L -> full local singleton diagnostic` is already proved by cp226.
- `SourcePressureBeamSeed L -> ∃ W ∈ L, full local singleton diagnostic` is now
  proved by cp227-r1.
- `SourcePressureFailureResolution L -> ∃ W ∈ L, full local singleton
  diagnostic` is also proved by the Branch C experiment.

Boundary:

- The new theorem is existential.  It identifies one witness already contained
  in the supplied seed list.

False Beam:

- No false/negative theorem was needed here.
- The failure-resolution overlap branch remains an obstruction branch, not an
  overlap repair theorem.

Gap:

- The direct automaton/failure-resolution bridge is no longer missing at the
  existential diagnostic level.
- The remaining gap is more specific:

```text
recovered adjacent pair / overlap branch
  -> branch-specific chosen side witness
  -> full diagnostic
```

That would be stronger documentation for a particular branch, but it should not
be added unless a caller needs the branch-specific witness identity.

## Dependency Direction

No dependency inversion was introduced.

The new theorem was placed in:

```text
DkMath/Collatz/PetalBridge/PressureBeam/Pulse.lean
```

No lower diagnostic module imports `PressureBeam`.

## Guardrails

The new theorems do not claim:

- list-wide coverage;
- witness-family aggregation;
- arbitrary witness selection;
- canonical target selection;
- arbitrary target transport;
- overlap repair;
- propagation;
- Collatz convergence.

They are local explicit-witness API consumption, lifted existentially from the
Beam seed and then from the failure-resolution wrapper.

## Verification

Commands run from `lean/dk_math`:

```text
lake build DkMath.Collatz.PetalBridge.PressureBeam.Pulse
lake build DkMath.Collatz.PetalBridge.PressureBeam
lake build DkMath.Collatz.PetalBridge
```

All builds completed successfully.

Additional checks from repository root:

```text
rg -n "sorry|admit" lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam
git diff --check
```

The no-sorry grep found no matches in the PressureBeam split files.
`git diff --check` passed.

Known unrelated warning observed during builds:

```text
DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:152:6:
declaration uses `sorry`
```

## Next Branch To Attack

The next useful branch is no longer the generic Branch C bridge; that now
exists.

The next precise branch is branch-specific witness identity:

```text
recovered adjacent pair branch
  -> left witness A in L
  -> full diagnostic for A

overlap obstruction branch
  -> one obstruction witness in L
  -> full diagnostic for that witness
```

This should only be attacked if a caller needs to preserve which side of the
failure-resolution branch produced the diagnostic.  Otherwise the new
failure-resolution existential theorem is enough and keeps the API smaller.
