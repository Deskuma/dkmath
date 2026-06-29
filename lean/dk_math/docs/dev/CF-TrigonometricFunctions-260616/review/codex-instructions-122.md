# Codex instructions

Target:
DkMath.Analysis.DkReal.SemanticCF2DPhaseShift

Goal:
Continue checkpoint 104 by packaging path traversal on `ShiftedCyclicChart`. Start with one quotient edge path, then use quotient seam equalities to concatenate the four finite edges into one closed quotient path if feasible. Do not introduce Euclidean angle language.

Principle:
Keep this layer pre-geometric. Do not use angle, arc, degree, circle, rotation, piOverFour, or fortyFive in Lean theorem names. The goal is path traversal on the shifted cyclic chart quotient, not Euclidean interpretation.

Context:
`ShiftedCyclicChart` is implemented as a quotient of `ShiftedFiniteChart`. The representative constructor and endpoint representatives are available:
`shiftedCyclicChartMk`,
`shiftedCyclicChartLeft`,
`shiftedCyclicChartRight`,
`shiftedCyclicChartRight_eq_succ_left`.

Topology is now connected:
`continuous_shiftedCyclicChartMk`,
`continuous_shiftedSemanticFinChartEval`,
`continuous_shiftedSemanticCyclicChartEval`.

Part A:
Define a quotient edge path for a fixed finite index.

Candidate definition:

```lean id="cld6ch"
def shiftedCyclicChartEdgePath (i : Fin 4) :
    Path (shiftedCyclicChartLeft i) (shiftedCyclicChartRight i) where
  toFun t := shiftedCyclicChartMk (i, t)
  continuous_toFun := by
    exact continuous_shiftedCyclicChartMk.comp
      (by
        -- prove continuity of t ↦ (i, t)
        fun_prop)
  source' := by rfl
  target' := by rfl
```

Adjust the continuity proof to match the available topology API. If `fun_prop` does not solve the pair map, prove it using product continuity.

Part B:
Add an apply theorem.

```lean id="wc2a18"
@[simp]
theorem shiftedCyclicChartEdgePath_apply
    (i : Fin 4) (t : unitInterval) :
    shiftedCyclicChartEdgePath i t =
      shiftedCyclicChartMk (i, t) := rfl
```

Part C:
Prove endpoint aliases if useful.

```lean id="ei53pk"
theorem shiftedCyclicChartEdgePath_source (i : Fin 4) :
    shiftedCyclicChartEdgePath i 0 = shiftedCyclicChartLeft i

theorem shiftedCyclicChartEdgePath_target (i : Fin 4) :
    shiftedCyclicChartEdgePath i 1 = shiftedCyclicChartRight i
```

Only add these if they improve downstream readability.

Part D:
Concatenate four quotient edge paths into a closed quotient path.

Candidate definition:

```lean id="em217e"
def shiftedCyclicFourPath :
    Path (shiftedCyclicChartLeft (0 : Fin 4))
      (shiftedCyclicChartLeft (0 : Fin 4)) := by
  let p0 := shiftedCyclicChartEdgePath (0 : Fin 4)
  let p1 := shiftedCyclicChartEdgePath (1 : Fin 4)
  let p2 := shiftedCyclicChartEdgePath (2 : Fin 4)
  let p3 := shiftedCyclicChartEdgePath (3 : Fin 4)
  -- use shiftedCyclicChartRight_zero_eq_one_left
  -- use shiftedCyclicChartRight_one_eq_two_left
  -- use shiftedCyclicChartRight_two_eq_three_left
  -- use shiftedCyclicChartRight_three_eq_zero_left
  ...
```

Use `Path.trans` and `Path.cast`, following the style already used in `shiftedSemanticFourLevelPath`.

If endpoint casts become noisy, stop after proving the four seam facts are exactly the right endpoint equalities for the quotient edge paths.

Part E:
Add source and target aliases for the closed quotient path if Part D succeeds.

```lean id="xjxjhj"
theorem shiftedCyclicFourPath_source :
    shiftedCyclicFourPath 0 = shiftedCyclicChartLeft (0 : Fin 4)

theorem shiftedCyclicFourPath_target :
    shiftedCyclicFourPath 1 = shiftedCyclicChartLeft (0 : Fin 4)
```

Part F:
賢狼のおまけ challenge:
If the closed quotient path is implemented, try to prove that evaluating it by `shiftedSemanticCyclicChartEval` gives the existing fixed-`q2` closed path observation.

Candidate theorem shape:

```lean id="gh7o6y"
theorem shiftedSemanticCyclicChartEval_fourPath_eq_finFourLevelPath
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) (t : unitInterval) :
    shiftedSemanticCyclicChartEval hcore z (shiftedCyclicFourPath t) =
      shiftedSemanticFinFourLevelPath hcore z t
```

This may be hard because both sides are built by `Path.trans` and casts. If it is too noisy, do not force it. Instead, prove the local edge version:

```lean id="c4477n"
theorem shiftedSemanticCyclicChartEval_edgePath
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) (i : Fin 4) (t : unitInterval) :
    shiftedSemanticCyclicChartEval hcore z (shiftedCyclicChartEdgePath i t) =
      shiftedSemanticFinLevelEdge hcore z i t
```

This local theorem should be much easier and is still very valuable.

Part G:
If the full four-path evaluation theorem is too hard, leave a TODO:

```text id="uzp3qr"
[TODO: semantic-cf2d/shifted-cyclic-path-eval]
Compare evaluation of the closed quotient path with the fixed-`q2` four-level path after path-trans cast normalization lemmas are available.
```

Part H:
Do not add Euclidean reading yet.

Part I:
Update docs.

Update `DkReal.lean` and `design-phase-center-shift-104.md`.

Record clearly:

```text id="jvnluu"
implemented:
  quotient edge path
  closed quotient four-path if successful
  local evaluation theorem for quotient edge path

implemented if successful:
  comparison between quotient four-path evaluation and fixed-q2 four-level path

remaining:
  path evaluation comparison if not finished
  Euclidean one-eighth reading later
```

Required checks:

```text id="z7ie1m"
lake build DkMath.Analysis.DkReal.SemanticCF2DPhaseShift
lake build DkMath.Analysis.DkReal
git diff --check
```
