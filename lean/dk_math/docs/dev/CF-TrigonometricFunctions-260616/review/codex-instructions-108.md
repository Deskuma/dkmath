# Codex instructions

Target:
DkMath.Analysis.DkReal.SemanticCF2DPhaseShift

Goal:
Continue checkpoint 104 by strengthening the shifted-frame scalar API and then prepare the semantic shifted-edge layer. Keep the implementation pre-geometric. Do not introduce angle, arc, degree, circle, rotation, piOverFour, or fortyFive language in Lean theorem names.

Context:
The scalar shifted frame is now implemented. It names neighboring quarter centers as shifted endpoints and proves that the old seam endpoint is the shifted center. The theorem shiftedQuarterAffine_center_eq_shiftedQuarterCenter is already available.

Part A:
Add small scalar shifted-frame consequences.

Candidate theorem names:

```lean
theorem shiftedQuarterRightEndpoint_sub_leftEndpoint (k : ℕ) :
    shiftedQuarterRightEndpoint k - shiftedQuarterLeftEndpoint k = 1 / 4

theorem shiftedQuarterCenter_eq_leftEndpoint_add_halfQuarter (k : ℕ) :
    shiftedQuarterCenter k =
      shiftedQuarterLeftEndpoint k + phaseHalfQuarterStep

theorem shiftedQuarterRightEndpoint_eq_center_add_halfQuarter (k : ℕ) :
    shiftedQuarterRightEndpoint k =
      shiftedQuarterCenter k + phaseHalfQuarterStep
```

These should be straightforward from the existing definitions and the one-eighth shift theorem.

Part B:
Add an affine shifted-frame endpoint theorem if useful.

Candidate theorem:

```lean
theorem shiftedQuarterAffine_zero_eq_leftEndpoint (k : ℕ) :
    (1 - (0 : ℝ)) * shiftedQuarterLeftEndpoint k +
        (0 : ℝ) * shiftedQuarterRightEndpoint k =
      shiftedQuarterLeftEndpoint k

theorem shiftedQuarterAffine_one_eq_rightEndpoint (k : ℕ) :
    (1 - (1 : ℝ)) * shiftedQuarterLeftEndpoint k +
        (1 : ℝ) * shiftedQuarterRightEndpoint k =
      shiftedQuarterRightEndpoint k
```

If repeating the affine expression becomes noisy, introduce a scalar helper definition only if it improves readability:

```lean
def shiftedQuarterAffine (k : ℕ) (t : ℝ) : ℝ :=
  (1 - t) * shiftedQuarterLeftEndpoint k +
    t * shiftedQuarterRightEndpoint k
```

Then prove endpoint and center theorems for it.

Part C:
Prepare the semantic shifted-edge layer, but do not force it if endpoint states are not yet clear.

Try to identify the correct semantic endpoint states corresponding to shiftedQuarterLeftEndpoint k and shiftedQuarterRightEndpoint k. The expected conceptual choice is that these endpoints should come from normalized center states of neighboring quarter edges, not from raw affine centers.

If the endpoint states can be defined cleanly, introduce a small shifted semantic edge definition. If not, add a precise TODO comment and update the design document with the exact obstruction.

Candidate theorem shape, only if the definition is clean:

```lean
theorem shiftedSemanticPhaseEdge_center_scalar_compat :
    ...
```

The expected meaning is that the shifted semantic edge at phaseCenter corresponds to the old seam state, matching the scalar theorem shiftedQuarterAffine_center_eq_shiftedQuarterCenter.

Part D:
Update docs.

Update design-phase-center-shift-104.md with the implemented scalar consequences. If semantic shifted edge is not introduced, add a short note explaining that endpoint state selection is still the blocking design choice.

Required checks:

```text
lake build DkMath.Analysis.DkReal.SemanticCF2DPhaseShift
lake build DkMath.Analysis.DkReal
git diff --check
```
