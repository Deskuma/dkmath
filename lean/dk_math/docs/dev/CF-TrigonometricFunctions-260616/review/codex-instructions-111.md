# Codex instructions

Target:
DkMath.Analysis.DkReal.SemanticCF2DPhaseShift

Goal:
Continue checkpoint 104 by testing whether the raw shifted semantic affine has the same q2 profile as the original affine edge. If it does, define the pointwise normalized shifted semantic edge and prove its boundary law. If it does not, record the exact obstruction and stop before inventing a heavier projection law.

Principle:
Keep this layer pre-geometric. Do not use angle, arc, degree, circle, rotation, piOverFour, or fortyFive in Lean theorem names. The goal is q2 profile and correction law, not Euclidean interpretation.

Context:
The shifted semantic endpoint candidates are fixed. The raw shifted midpoint is known to have q2 equal to one half of q2 z. The corrected shifted midpoint is proven equal to the old seam. What remains is to decide whether the whole shifted semantic edge can use pointwise q2 normalization.

Part A:
Try to prove the q2 profile of the raw shifted semantic affine.

Candidate theorem:

```lean id="kc9s5s"
theorem shiftedSemanticRawAffine_q2_of_core_eq_zero
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) (t : ℝ) :
    Vec.q2 (shiftedSemanticRawAffine r z t) =
      phaseDepth t * Vec.q2 z
```

Expected checks:
At t = 0, this should reduce to q2 z.
At t = 1, this should reduce to q2 z.
At t = phaseCenter, this should reduce to one half of q2 z.

If the theorem is false or hard, try to prove a coordinate formula for the q2 profile instead. Do not force the desired statement if Lean exposes a different profile.

Part B:
If Part A succeeds, define the pointwise normalized shifted semantic edge.

Candidate definition:

```lean id="rbsgd2"
def shiftedSemanticNormalizedEdge
    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) (t : ℝ) : Vec ℝ :=
  Vec.mk
    (phaseNormalization t * (shiftedSemanticRawAffine r z t).core)
    (phaseNormalization t * (shiftedSemanticRawAffine r z t).beam)
```

If a general vector scale helper exists, use it only if it improves readability.

Part C:
Prove endpoint behavior for the normalized shifted edge.

Candidate theorem names:

```lean id="yrz1tq"
theorem shiftedSemanticNormalizedEdge_zero
    ...

theorem shiftedSemanticNormalizedEdge_one
    ...
```

Expected results:
At t = 0, it should equal shiftedSemanticLeftEndpoint.
At t = 1, it should equal shiftedSemanticRightEndpoint.

These should use phaseNormalization_zero and phaseNormalization_one if available.

Part D:
Prove q2 boundary preservation.

Candidate theorem:

```lean id="r22s4x"
theorem shiftedSemanticNormalizedEdge_q2_of_core_eq_zero
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) (t : ℝ) :
    Vec.q2 (shiftedSemanticNormalizedEdge r z t) = Vec.q2 z
```

Expected route:
Use shiftedSemanticRawAffine_q2_of_core_eq_zero and phaseNormalization_sq_mul_phaseDepth.

Part E:
Prove that the normalized shifted edge center is the old seam.

Candidate theorem:

```lean id="gp32np"
theorem shiftedSemanticNormalizedEdge_center_eq_seam_of_core_eq_zero
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) :
    shiftedSemanticNormalizedEdge r z phaseCenter =
      shiftedSemanticSeam r z
```

Expected route:
Use shiftedSemanticRawAffine_center_eq_rawMidpoint and the existing corrected midpoint theorem, or show the normalization coefficient at phaseCenter matches the center correction scalar.

Part F:
If Part A fails:
Do not define shiftedSemanticNormalizedEdge. Instead, add a theorem or comment with the actual q2 profile Lean exposes, and update docs to say pointwise q2 normalization is not yet justified.

Part G:
Update docs.

Update DkReal.lean and design-phase-center-shift-104.md with whatever was proven.

Required checks:

```text id="wpszml"
lake build DkMath.Analysis.DkReal.SemanticCF2DPhaseShift
lake build DkMath.Analysis.DkReal
git diff --check
```
