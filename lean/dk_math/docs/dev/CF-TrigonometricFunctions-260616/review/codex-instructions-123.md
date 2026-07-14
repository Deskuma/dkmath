# Codex instructions

Target:
DkMath.Analysis.DkReal.SemanticCF2DPhaseShift

Goal:
Continue checkpoint 104 by connecting the closed quotient chart path to semantic boundary observation. First package the evaluated quotient path as a fixed-`q2` path. Then add small `Path.cast` / `Path.trans` normalization lemmas only as needed. Do not force the full four-path comparison if it becomes noisy.

Principle:
Keep this layer pre-geometric. Do not use angle, arc, degree, circle, rotation, piOverFour, or fortyFive in Lean theorem names. The goal is comparison between quotient chart traversal and fixed-boundary observation.

Context:
`shiftedCyclicChartEdgePath` and `shiftedCyclicFourPath` are implemented. The local comparison theorem is available:

```lean id="on71ck"
shiftedSemanticCyclicChartEval_edgePath
```

It states that evaluating one quotient edge path recovers the corresponding fixed-`q2` finite level edge. The full comparison between evaluation of `shiftedCyclicFourPath` and `shiftedSemanticFinFourLevelPath` remains TODO because `Path.trans` and `Path.cast` normalization lemmas may be needed.

Part A:
Define the observed fixed-boundary path obtained by evaluating the closed quotient path.

Candidate definition:

```lean id="tclon0"
def shiftedSemanticObservedCyclicFourPath
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) :
    Path
      (shiftedSemanticCyclicChartEval hcore z
        (shiftedCyclicChartLeft (0 : Fin 4)))
      (shiftedSemanticCyclicChartEval hcore z
        (shiftedCyclicChartLeft (0 : Fin 4))) where
  toFun t := shiftedSemanticCyclicChartEval hcore z (shiftedCyclicFourPath t)
  continuous_toFun :=
    (continuous_shiftedSemanticCyclicChartEval hcore z).comp
      shiftedCyclicFourPath.continuous_toFun
  source' := by
    rw [shiftedCyclicFourPath_source]
  target' := by
    rw [shiftedCyclicFourPath_target]
```

Adjust endpoint proofs to the actual `Path` API. If the endpoint type is inconvenient, use `.cast` to rewrite endpoints to the preferred finite level endpoints.

Part B:
Add source and target aliases for the observed path.

Candidate theorem names:

```lean id="nopqjw"
theorem shiftedSemanticObservedCyclicFourPath_source
    ...

theorem shiftedSemanticObservedCyclicFourPath_target
    ...
```

Part C:
Prove the observed path is fixed-boundary-valued.

This may be automatic because the codomain is already `LevelSet ℝ (Vec.q2 z)`. Still expose a theorem if useful:

```lean id="iuvkdl"
theorem shiftedSemanticObservedCyclicFourPath_q2
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) (t : unitInterval) :
    Vec.q2 ((shiftedSemanticObservedCyclicFourPath hcore z t).1) =
      Vec.q2 z
```

Part D:
Try to prove endpoint evaluation aliases.

Candidate theorem shapes:

```lean id="av9vr9"
theorem shiftedSemanticCyclicChartEval_left_zero
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) :
    shiftedSemanticCyclicChartEval hcore z
      (shiftedCyclicChartLeft (0 : Fin 4)) =
        shiftedSemanticFinLeftLevelEndpoint hcore z (0 : Fin 4)
```

This should be a wrapper around `shiftedSemanticCyclicChartEval_left`.

Part E:
賢狼のおまけ challenge:
Try to prove local comparison for the observed quotient path on the first edge segment if a simple theorem about `Path.trans` evaluation exists.

Do not force this unless Mathlib exposes convenient lemmas. Candidate direction:

```lean id="t0ysnj"
theorem shiftedSemanticObservedCyclicFourPath_firstSegment
    ...
```

A simpler useful fallback is to add TODO notes identifying the exact missing normalization lemmas for `Path.trans` and `Path.cast`.

Part F:
If a small `Path.cast` apply lemma is needed and easy, add it locally.

Candidate shape:

```lean id="a07aqj"
theorem path_cast_apply
    {α : Type _} [TopologicalSpace α]
    {a b c d : α}
    (p : Path a b) (hac : a = c) (hbd : b = d)
    (t : unitInterval) :
    (p.cast hac hbd) t = p t := by
  ...
```

Only add this if it is accepted cleanly and does not conflict with Mathlib names. If Mathlib already has such a theorem, use it instead.

Part G:
Do not force the full theorem below yet, but try it after Part A succeeds:

```lean id="np2fqx"
theorem shiftedSemanticObservedCyclicFourPath_eq_finFourLevelPath
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) :
    shiftedSemanticObservedCyclicFourPath hcore z =
      shiftedSemanticFinFourLevelPath hcore z
```

If this is hard, leave TODO:

```text id="jsvv2o"
[TODO: semantic-cf2d/shifted-cyclic-path-eval]
Compare the evaluated closed quotient path with the fixed-`q2` four-level path after Path.trans and Path.cast normalization lemmas are available.
```

Part H:
Update docs.

Update `DkReal.lean` and `design-phase-center-shift-104.md`.

Record clearly:

```text id="y73pw9"
implemented:
  observed closed quotient path into fixed q2 boundary
  source/target/q2 aliases

implemented if successful:
  local first-segment comparison
  cast/trans normalization lemmas

remaining:
  full comparison with shiftedSemanticFinFourLevelPath
  Euclidean one-eighth reading later
```

Required checks:

```text id="x6r8aj"
lake build DkMath.Analysis.DkReal.SemanticCF2DPhaseShift
lake build DkMath.Analysis.DkReal
git diff --check
```
