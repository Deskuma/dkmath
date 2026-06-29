# Codex instructions

Target:
DkMath.Analysis.DkReal.SemanticCF2DPhaseShift

Goal:
Continue checkpoint 104 by introducing the first quotient wrapper for the finite shifted chart layer. Use the seam relation only through its generated equivalence relation. Then descend chart evaluation to the quotient. Do not introduce Euclidean angle language.

Principle:
Keep this layer pre-geometric. Do not use angle, arc, degree, circle, rotation, piOverFour, or fortyFive in Lean theorem names. The goal is a quotient of finite shifted charts by seam identification, and a well-defined fixed-`q2` boundary evaluation.

Context:
`ShiftedFiniteChart = Fin 4 × unitInterval` is implemented. `shiftedSemanticFinChartEval` evaluates finite charts into the fixed `q2` boundary. `shiftedFiniteSeamRel` identifies `(i, 1)` with `(finFourSucc i, 0)`. Lean already proves `shiftedSemanticFinChartEval_eq_of_seamRel`.

Part A:
Introduce the equivalence closure of the finite seam relation.

Preferred route:
Use Mathlib’s relation equivalence closure if available in the current imports, likely under `Relation.EqvGen`.

Candidate definition shape:

```lean id="q0q89l"
def shiftedFiniteChartRel (p q : ShiftedFiniteChart) : Prop :=
  Relation.EqvGen shiftedFiniteSeamRel p q
```

If the name or namespace differs, use the appropriate Mathlib API. If `Relation.EqvGen` is not available without heavy imports, stop and add a precise TODO instead of inventing a large custom relation.

Part B:
Define a `Setoid` for shifted finite charts.

Candidate shape:

```lean id="lb9efr"
def shiftedFiniteChartSetoid : Setoid ShiftedFiniteChart where
  r := shiftedFiniteChartRel
  iseqv := ...
```

Expected route:
The equivalence proof should come from the equivalence closure API. If the API already provides a `Setoid`, use it instead.

Part C:
Define the quotient type.

Candidate definition:

```lean id="kpxkbd"
abbrev ShiftedCyclicChart :=
  Quot shiftedFiniteChartSetoid
```

Alternative names are acceptable if they better match project style, but avoid Euclidean wording.

Part D:
Prove chart evaluation respects the generated equivalence.

Candidate theorem:

```lean id="t12sh6"
theorem shiftedSemanticFinChartEval_eq_of_chartRel
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ)
    {p q : ShiftedFiniteChart}
    (hrel : shiftedFiniteChartRel p q) :
    shiftedSemanticFinChartEval hcore z p =
      shiftedSemanticFinChartEval hcore z q
```

Expected proof route:
Induct over `Relation.EqvGen`.

Use:
`shiftedSemanticFinChartEval_eq_of_seamRel` for the base seam relation.
Use equality reflexivity for reflexive cases.
Use symmetry of equality for symmetric cases.
Use transitivity of equality for transitive cases.

If the induction names are unfamiliar, inspect examples in Mathlib or nearby project code.

Part E:
Define quotient evaluation.

Candidate definition:

```lean id="alrr0o"
def shiftedSemanticCyclicChartEval
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ)
    (p : ShiftedCyclicChart) : LevelSet ℝ (Vec.q2 z) :=
  Quot.lift
    (shiftedSemanticFinChartEval hcore z)
    (by
      intro p q hrel
      exact shiftedSemanticFinChartEval_eq_of_chartRel hcore z hrel)
    p
```

Adjust theorem/proof syntax to the actual `Quot` API.

Part F:
Add lift/quotient computation theorem.

Candidate theorem:

```lean id="uz8zvd"
@[simp]
theorem shiftedSemanticCyclicChartEval_mk
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ)
    (p : ShiftedFiniteChart) :
    shiftedSemanticCyclicChartEval hcore z (Quot.mk _ p) =
      shiftedSemanticFinChartEval hcore z p
```

If `Quot.mk` syntax differs for the local setoid, adapt accordingly.

Part G:
Do not add topology or path structure on the quotient in this checkpoint unless it is trivial.

If quotient evaluation succeeds, update TODO to:

```text id="dipxax"
[TODO: semantic-cf2d/shifted-cyclic-topology]
Add topology/path structure to the shifted cyclic chart quotient only after the quotient evaluation API is stable.
```

Part H:
Update docs.

Update `DkReal.lean` and `design-phase-center-shift-104.md`.

Record clearly:

```text id="vpc7ip"
implemented:
  generated equivalence relation for finite seam relation
  quotient chart wrapper
  quotient evaluation into fixed q2 boundary
  quotient evaluation computation theorem

remaining:
  quotient topology/path structure
  Euclidean one-eighth reading later
```

Required checks:

```text id="wu3sxp"
lake build DkMath.Analysis.DkReal.SemanticCF2DPhaseShift
lake build DkMath.Analysis.DkReal
git diff --check
```
