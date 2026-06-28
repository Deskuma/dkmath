# Codex instructions

Target:
DkMath.Analysis.DkReal.SemanticCF2DPhaseShift

Goal:
Continue checkpoint 104 by strengthening the algebraic quotient observation API for `ShiftedCyclicChart`. Do not add quotient topology or path structure yet unless the representative API finishes cleanly and the topology design is completely straightforward.

Principle:
Keep this layer pre-geometric. Do not use angle, arc, degree, circle, rotation, piOverFour, or fortyFive in Lean theorem names. The goal is quotient representative readability and seam equality inside the cyclic chart quotient.

Context:
`ShiftedFiniteChart = Fin 4 × unitInterval` is implemented. The seam relation is closed under `Relation.EqvGen`, packaged as `shiftedFiniteChartSetoid`, and quotiented as `ShiftedCyclicChart`. Evaluation descends to the quotient through `shiftedSemanticCyclicChartEval`, with representative computation theorem `shiftedSemanticCyclicChartEval_mk` and q2 observation theorem `shiftedSemanticCyclicChartEval_q2`.

Part A:
Add a representative constructor alias for the quotient.

Candidate definition:

```lean id="saa1wl"
def shiftedCyclicChartMk (p : ShiftedFiniteChart) : ShiftedCyclicChart :=
  Quot.mk shiftedFiniteChartSetoid p
```

Add computation theorem if useful:

```lean id="m8j96u"
@[simp]
theorem shiftedCyclicChartMk_eq_mk (p : ShiftedFiniteChart) :
    shiftedCyclicChartMk p = Quot.mk shiftedFiniteChartSetoid p := rfl
```

Part B:
Add named quotient representatives for local left and right endpoints.

Candidate definitions:

```lean id="fa3juy"
def shiftedCyclicChartLeft (i : Fin 4) : ShiftedCyclicChart :=
  shiftedCyclicChartMk (i, (0 : unitInterval))

def shiftedCyclicChartRight (i : Fin 4) : ShiftedCyclicChart :=
  shiftedCyclicChartMk (i, (1 : unitInterval))
```

Part C:
Prove seam equality inside the quotient.

Candidate theorem:

```lean id="wuo1so"
theorem shiftedCyclicChartRight_eq_succ_left (i : Fin 4) :
    shiftedCyclicChartRight i =
      shiftedCyclicChartLeft (finFourSucc i)
```

Expected route:
Use `Quot.sound`.
The proof should use the generated equivalence relation with one generating seam step.

If `Quot.sound` needs the setoid relation directly, provide:

```lean id="l2a5hm"
show shiftedFiniteChartRel (i, (1 : unitInterval))
  (finFourSucc i, (0 : unitInterval))
```

Then use `Relation.EqvGen.rel` and the witness for `shiftedFiniteSeamRel`.

Part D:
Add finite small seam aliases in quotient wording if useful.

Candidate theorem names:

```lean id="kd1rxl"
shiftedCyclicChartRight_zero_eq_one_left
shiftedCyclicChartRight_one_eq_two_left
shiftedCyclicChartRight_two_eq_three_left
shiftedCyclicChartRight_three_eq_zero_left
```

These can wrap `shiftedCyclicChartRight_eq_succ_left`.

Part E:
Add quotient evaluation theorems for left and right representatives.

Candidate theorem shapes:

```lean id="dle6ps"
theorem shiftedSemanticCyclicChartEval_left
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) (i : Fin 4) :
    shiftedSemanticCyclicChartEval hcore z (shiftedCyclicChartLeft i) =
      shiftedSemanticFinLeftLevelEndpoint hcore z i

theorem shiftedSemanticCyclicChartEval_right
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) (i : Fin 4) :
    shiftedSemanticCyclicChartEval hcore z (shiftedCyclicChartRight i) =
      shiftedSemanticFinRightLevelEndpoint hcore z i
```

Expected route:
Unfold left/right representatives, use `shiftedSemanticCyclicChartEval_mk`, then `shiftedSemanticFinChartEval_at_left/right`.

Part F:
Add a theorem showing quotient seam equality and evaluation seam compatibility agree.

Candidate theorem:

```lean id="r7j9yu"
theorem shiftedSemanticCyclicChartEval_right_eq_succ_left
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) (i : Fin 4) :
    shiftedSemanticCyclicChartEval hcore z (shiftedCyclicChartRight i) =
      shiftedSemanticCyclicChartEval hcore z (shiftedCyclicChartLeft (finFourSucc i))
```

This should follow by rewriting with `shiftedCyclicChartRight_eq_succ_left`, or by the left/right evaluation theorems.

Part G:
Do not add topology/path structure in this checkpoint unless the above finishes with no complications.

Update the TODO as follows only if this checkpoint succeeds:

```text id="o7ks84"
[TODO: semantic-cf2d/shifted-cyclic-topology]
Add topology/path structure to `ShiftedCyclicChart` after the quotient representative and seam-equality API is stable.
```

Part H:
Update docs.

Update `DkReal.lean` and `design-phase-center-shift-104.md`.

Record clearly:

```text id="x93ru8"
implemented:
  quotient representative constructor
  quotient left/right representatives
  quotient seam equality
  quotient evaluation at representatives
  quotient evaluation seam compatibility

remaining:
  quotient topology/path structure
  Euclidean one-eighth reading later
```

Required checks:

```text id="dxdqpr"
lake build DkMath.Analysis.DkReal.SemanticCF2DPhaseShift
lake build DkMath.Analysis.DkReal
git diff --check
```
