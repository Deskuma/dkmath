# Codex instructions

Target:
DkMath.Analysis.DkReal.SemanticCF2DPhaseShift

Goal:
Continue checkpoint 104 by moving from the completed scalar shifted-frame API toward the semantic shifted-edge design. Do not force a final shifted semantic path if the correction law is not yet clear. Instead, formalize the endpoint candidates, compute the raw midpoint behavior, and record the obstruction precisely.

Principle:
Keep this pre-geometric. Do not use angle, arc, degree, circle, rotation, piOverFour, or fortyFive in Lean theorem names. This layer is about endpoint, center, shifted frame, normalization, and q2 boundary behavior.

Part A:
Add semantic endpoint candidate definitions for the shifted frame.

Use the existing normalized center of neighboring quarter edges as the natural candidate.

Suggested definitions, adjusted to existing API names:

```lean id="yabgjk"
def shiftedSemanticLeftEndpoint
    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) : Vec ℝ :=
  normalizedPhaseEdge r z phaseCenter

def shiftedSemanticRightEndpoint
    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) : Vec ℝ :=
  normalizedPhaseEdge r (semanticAct r z) phaseCenter

def shiftedSemanticSeam
    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) : Vec ℝ :=
  semanticAct r z
```

If these names are too strong, use `Candidate` in the names.

Part B:
Prove basic q2 facts for the endpoint candidates under the core-zero hypothesis.

Candidate theorem shapes:

```lean id="hofwuh"
theorem shiftedSemanticLeftEndpoint_q2_of_core_eq_zero
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) :
    Vec.q2 (shiftedSemanticLeftEndpoint r z) = Vec.q2 z

theorem shiftedSemanticRightEndpoint_q2_of_core_eq_zero
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) :
    Vec.q2 (shiftedSemanticRightEndpoint r z) = Vec.q2 z

theorem shiftedSemanticSeam_q2_of_core_eq_zero
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) :
    Vec.q2 (shiftedSemanticSeam r z) = Vec.q2 z
```

The right endpoint may require applying the same core-zero action law after one semantic action. If that is not directly available, prove or reuse a theorem that the core-zero semantic action preserves q2.

Part C:
Define the raw affine midpoint candidate between the shifted semantic endpoints.

Candidate definition:

```lean id="ncrkoq"
def shiftedSemanticRawMidpoint
    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) : Vec ℝ :=
  Vec.mk
    (((shiftedSemanticLeftEndpoint r z).core +
        (shiftedSemanticRightEndpoint r z).core) / 2)
    (((shiftedSemanticLeftEndpoint r z).beam +
        (shiftedSemanticRightEndpoint r z).beam) / 2)
```

Or define a general vector affine helper if that is cleaner.

Part D:
Try to compute or compare the raw midpoint with the old seam.

Do not assume equality.

Preferred outcomes:

1. If equality is false generally, add a theorem or documented lemma showing the obstruction in coordinate form.
2. If a clean coordinate formula is available, prove it.
3. If the expression is too large, add a precise TODO comment saying that the raw midpoint is not definitionally the seam and requires a correction law.

Candidate theorem direction:

```lean id="hpa18o"
theorem shiftedSemanticRawMidpoint_obstruction
    ...
```

Avoid naming it as a failure theorem unless a concrete inequality or coordinate mismatch is proven. A coordinate formula is better than a negative theorem.

Part E:
Prepare correction-law design in docs.

Update design-phase-center-shift-104.md with a new section:

```text id="zl55rz"
Semantic shifted-edge obstruction

Natural endpoints:
  normalized center state of edge k
  normalized center state of edge k + 1

Observation:
  their raw affine midpoint is not generally the old seam state

Consequence:
  a shifted normalization or projection law must be chosen before defining
  the final shifted semantic edge
```

If a coordinate formula was proved, include the theorem name.

Part F:
Do not add the Euclidean one-eighth reading yet.

Required checks:

```text id="wmj7ie"
lake build DkMath.Analysis.DkReal.SemanticCF2DPhaseShift
lake build DkMath.Analysis.DkReal
git diff --check
```
