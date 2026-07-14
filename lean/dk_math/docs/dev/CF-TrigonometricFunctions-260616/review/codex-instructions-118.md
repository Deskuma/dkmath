# Codex instructions

Target:
DkMath.Analysis.DkReal.SemanticCF2DPhaseShift

Goal:
Continue checkpoint 104 by preparing the cyclic quotient layer without fully committing to a quotient type yet. Add a finite chart/evaluation API for the shifted closed boundary using `Fin 4` and `unitInterval`, then expose the seam relation at the chart level.

Principle:
Keep this layer pre-geometric. Do not use angle, arc, degree, circle, rotation, piOverFour, or fortyFive in Lean theorem names. The goal is finite chart evaluation and seam compatibility before any continuous quotient phase parameter is introduced.

Context:
The finite fixed-`q2` observation layer is implemented. `shiftedSemanticFinBaseLevelPoint`, finite center-to-successor-base level theorem, closed shifted four-level path source/target aliases, and `shiftedSemanticFinFourLevelPath_q2` are available.

Part A:
Add a finite chart type or alias for one of the four shifted edges plus a local edge parameter.

Preferred lightweight option:

```lean id="kizvs5"
abbrev ShiftedFiniteChart := Fin 4 × unitInterval
```

If an abbrev name conflicts with project style, use a def or namespace-local name.

Part B:
Define chart evaluation into the fixed `q2` level set.

Candidate definition:

```lean id="kj056d"
def shiftedSemanticFinChartEval
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ)
    (p : ShiftedFiniteChart) : LevelSet ℝ (Vec.q2 z) :=
  shiftedSemanticFinLevelEdge hcore z p.1 p.2
```

Also add a value theorem:

```lean id="kxqcg3"
@[simp]
theorem shiftedSemanticFinChartEval_val
    ...
```

Part C:
Add endpoint evaluation theorems for the chart.

Candidate theorem shapes:

```lean id="nhf5dz"
theorem shiftedSemanticFinChartEval_at_left
    ...

theorem shiftedSemanticFinChartEval_at_right
    ...
```

Meaning:
For an edge `i`, evaluating at local `0` gives the finite left level endpoint.
Evaluating at local `1` gives the finite right level endpoint.

Use the project’s existing `unitInterval` notation or constructors. If explicit `0` and `1` for `unitInterval` are noisy, use the theorem forms already available from paths/edges and keep this part minimal.

Part D:
Define a seam relation on finite charts, but do not quotient yet.

Candidate relation:

```lean id="ts8urj"
def shiftedFiniteSeamRel (p q : ShiftedFiniteChart) : Prop :=
  ∃ i : Fin 4,
    p = (i, 1) ∧ q = (finFourSucc i, 0)
```

Adjust syntax for `unitInterval` values as needed. If `unitInterval` endpoints are hard to write, define helper constants:

```lean id="edm9w3"
def unitIntervalZero : unitInterval := ⟨0, by constructor <;> norm_num⟩
def unitIntervalOne : unitInterval := ⟨1, by constructor <;> norm_num⟩
```

Use project conventions if such constants already exist.

Part E:
Prove seam compatibility for chart evaluation.

Candidate theorem:

```lean id="g41d2a"
theorem shiftedSemanticFinChartEval_eq_of_seamRel
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ)
    {p q : ShiftedFiniteChart}
    (hrel : shiftedFiniteSeamRel p q) :
    shiftedSemanticFinChartEval hcore z p =
      shiftedSemanticFinChartEval hcore z q
```

Expected route:
Unpack the relation and use `shiftedSemanticFinRightLevelEndpoint_eq_succ_left`.

If proof becomes noisy, first prove a specialized theorem:

```lean id="x2apx5"
theorem shiftedSemanticFinChartEval_right_eq_succ_left
    ...
```

Part F:
Do not construct the quotient in this checkpoint unless everything above is trivial and the quotient design is clearly accepted by existing project conventions.

Instead, add TODO:

```text id="nvipqc"
[TODO: semantic-cf2d/shifted-cyclic-quotient]
Use ShiftedFiniteChart modulo shiftedFiniteSeamRel, or an equivalent project-specific quotient wrapper, once chart evaluation compatibility is stable.
```

Part G:
Update docs.

Update `DkReal.lean` and `design-phase-center-shift-104.md`.

Record clearly:

```text id="rp6mwg"
implemented:
  finite shifted chart
  chart evaluation into fixed q2 level set
  seam relation
  evaluation compatibility across seams

remaining:
  actual quotient wrapper
  Euclidean one-eighth reading later
```

Required checks:

```text id="go1kh7"
lake build DkMath.Analysis.DkReal.SemanticCF2DPhaseShift
lake build DkMath.Analysis.DkReal
git diff --check
```
