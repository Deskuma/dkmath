# Codex instructions

Target:
DkMath.Analysis.DkReal.SemanticCF2DPhaseShift

Goal:
Continue checkpoint 104 by testing the topology layer for `ShiftedCyclicChart`. First add only the minimal quotient-topology and continuity API needed for the descended evaluation. Do not introduce Euclidean angle language, and do not force a full path structure if topology becomes noisy.

Principle:
Keep this layer pre-geometric. Do not use angle, arc, degree, circle, rotation, piOverFour, or fortyFive in Lean theorem names. The goal is quotient topology and continuity of fixed-`q2` boundary evaluation.

Context:
`ShiftedCyclicChart` is implemented as the quotient of `ShiftedFiniteChart` by the generated seam equivalence. The quotient representative API is stable:
`shiftedCyclicChartMk`, `shiftedCyclicChartLeft`, `shiftedCyclicChartRight`,
`shiftedCyclicChartRight_eq_succ_left`,
`shiftedSemanticCyclicChartEval`,
`shiftedSemanticCyclicChartEval_mk`,
`shiftedSemanticCyclicChartEval_left`,
`shiftedSemanticCyclicChartEval_right`,
and `shiftedSemanticCyclicChartEval_q2`.

Part A:
Inspect whether Mathlib already provides a quotient topology instance for `Quot shiftedFiniteChartSetoid`.

Try to state a basic continuity theorem for the quotient representative map if the API supports it.

Candidate theorem shape:

```lean id="lg2dvb"
theorem continuous_shiftedCyclicChartMk :
    Continuous shiftedCyclicChartMk
```

If this does not make sense because the topology instance is absent or the API is different, do not force it. Record the actual missing instance or theorem in a TODO comment.

Part B:
Prove continuity of finite chart evaluation before quotienting.

Candidate theorem:

```lean id="c6gyaa"
theorem continuous_shiftedSemanticFinChartEval
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) :
    Continuous (fun p : ShiftedFiniteChart =>
      shiftedSemanticFinChartEval hcore z p)
```

Expected route:
Unfold `ShiftedFiniteChart = Fin 4 × unitInterval`.
Use the fact that `Fin 4` is finite/discrete and each branch evaluates by `shiftedSemanticFinLevelEdge`.
If the proof is hard, first prove continuity on each finite edge:

```lean id="rqr8yp"
theorem continuous_shiftedSemanticFinChartEval_of_fixed_index
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) (i : Fin 4) :
    Continuous (fun t : unitInterval =>
      shiftedSemanticFinChartEval hcore z (i, t))
```

Part C:
If quotient topology is available, prove continuity of descended quotient evaluation.

Candidate theorem:

```lean id="umqw88"
theorem continuous_shiftedSemanticCyclicChartEval
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) :
    Continuous (fun p : ShiftedCyclicChart =>
      shiftedSemanticCyclicChartEval hcore z p)
```

Expected route:
Use the quotient-lift continuity theorem from Mathlib, with Part B as the continuity of the representative-level evaluation.

Part D:
If Part C succeeds, add a small observation theorem saying continuity remains fixed-boundary-valued.

This may be only documentation, because the codomain is already `LevelSet ℝ (Vec.q2 z)`.

Part E:
Do not create a new quotient path object in this checkpoint unless it is completely straightforward.

If a path construction is tempting, leave it as TODO:

```text id="lwylgw"
[TODO: semantic-cf2d/shifted-cyclic-path]
Package path traversal on ShiftedCyclicChart only after continuous quotient evaluation is stable.
```

Part F:
賢狼のおまけ instruction:
Add a short design note in `design-phase-center-shift-104.md` explaining the difference between the algebraic quotient and the topological quotient.

Use wording like:

```text id="pecwd1"
Algebraic quotient:
  identifies seam endpoints as equal chart points.

Topological quotient:
  must additionally give the glued chart space the quotient topology.

Boundary evaluation:
  should be continuous only after the representative-level evaluation and the quotient-lift theorem are connected.
```

Also add a warning:

```text id="vzi7bh"
This is still not a Euclidean angle parameter.
```

Part G:
Failure mode:
If quotient topology is unavailable or proof-heavy, do not add partial broken instances. Instead, add a precise TODO listing the missing theorem or instance, keep all current quotient evaluation API unchanged, and ensure the file still builds.

Part H:
Update docs.

Update `DkReal.lean` and `design-phase-center-shift-104.md`.

Record clearly:

```text id="bg7m49"
implemented if successful:
  representative-level chart evaluation continuity
  quotient evaluation continuity
  quotient topology design note

remaining:
  shifted cyclic path structure
  Euclidean one-eighth reading later

if blocked:
  exact missing topology API or theorem
```

Required checks:

```text id="vo0vyc"
lake build DkMath.Analysis.DkReal.SemanticCF2DPhaseShift
lake build DkMath.Analysis.DkReal
git diff --check
```
