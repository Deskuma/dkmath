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

## Branch Taken

Branch B was taken:

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

## Branches Inspected But Not Taken

Branch A:

- No better existing caller with an already surfaced `W ∈ L` was found.
- The Pulse API itself has explicit-membership theorems, but adding another
  direct alias there would only duplicate the cp226 theorem.

Branch C:

- `PressureAutomaton` exposes `SourcePressureFailureResolution L`, with either
  a recovered adjacent pair or an overlap obstruction.
- The recovered branch gives an adjacent-pair relation, and the overlap branch
  is list-addressed, but the clean exposed Beam-facing route is already
  mediated by `SourcePressureBeamSeed`.
- A direct failure-resolution theorem may be useful later, but it would be a
  higher duplicate of the seed route unless a caller specifically works before
  entering Beam seed vocabulary.

Branch D:

- Multiple possible caller surfaces exist, but the seed route is the smallest
  one with the fewest new assumptions after explicit `W ∈ L`.

Branch E:

- No contradiction or useful local negative theorem was discovered.

Branch F:

- Not applicable.  A valid caller route exists through the Beam seed.

## Classification

True Beam:

- `W ∈ L -> full local singleton diagnostic` is already proved by cp226.
- `SourcePressureBeamSeed L -> ∃ W ∈ L, full local singleton diagnostic` is now
  proved by cp227-r1.

Boundary:

- The new theorem is existential.  It identifies one witness already contained
  in the supplied seed list.

False Beam:

- No false/negative theorem was needed here.
- The failure-resolution overlap branch remains an obstruction branch, not an
  overlap repair theorem.

Gap:

- A direct automaton-level bridge from
  `SourcePressureFailureResolution L` to the full diagnostic may be possible,
  but it is currently unnecessary because `SourcePressureBeamSeed L` is exactly
  the Beam-facing wrapper of that state.
- If a future caller must stay at `PressureAutomaton` level, the missing bridge
  to inspect is:

```text
failure/obstruction branch -> explicit W ∈ L -> full diagnostic
```

## Dependency Direction

No dependency inversion was introduced.

The new theorem was placed in:

```text
DkMath/Collatz/PetalBridge/PressureBeam/Pulse.lean
```

No lower diagnostic module imports `PressureBeam`.

## Guardrails

The new theorem does not claim:

- list-wide coverage;
- witness-family aggregation;
- arbitrary witness selection;
- canonical target selection;
- arbitrary target transport;
- overlap repair;
- propagation;
- Collatz convergence.

It is local explicit-witness API consumption, lifted existentially from the
Beam seed.

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

The next useful branch is Branch C, but only if a caller needs to remain at the
automaton/failure-resolution level.

Candidate future theorem:

```text
SourcePressureFailureResolution L
  -> exists W in L
       such that W's singleton pulse has the full local diagnostic
```

This should be added only when it removes real caller noise.  For current Beam
work, the seed theorem is the cleaner public surface.
