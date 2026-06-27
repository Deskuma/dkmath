# Codex instructions

Target:
DkMath.Analysis.DkReal.SemanticCF2DPhaseShift

Goal:
Continue checkpoint 104 by turning the raw shifted-midpoint obstruction into an explicit center correction law. Do not define the final shifted semantic path yet unless the center correction is completely stable.

Principle:
Keep this layer pre-geometric. Do not introduce angle, arc, degree, circle, rotation, piOverFour, or fortyFive in Lean theorem names. The goal is correction/projection back to the q2 boundary, not Euclidean interpretation.

Context:
The semantic shifted endpoint candidates are now implemented. Under the core-zero hypothesis, both normalized endpoint candidates and the seam lie on the same q2 boundary. The raw midpoint is not the seam; Lean proves it is a scalar multiple of the seam and has q2 equal to one half of the original q2.

Part A:
Add an explicit corrected midpoint for the shifted semantic frame.

Use the existing obstruction theorem:

```lean id="u2nutp"
shiftedSemanticRawMidpoint_eq_scaled_seam_of_core_eq_zero
```

Candidate definition:

```lean id="p65enw"
def shiftedSemanticCorrectedMidpoint
    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) : Vec ℝ :=
  Vec.mk
    ((2 / phaseNormalization phaseCenter) *
      (shiftedSemanticRawMidpoint r z).core)
    ((2 / phaseNormalization phaseCenter) *
      (shiftedSemanticRawMidpoint r z).beam)
```

If an existing `Vec.scale` API is available and convenient, use it instead.

Part B:
Prove that the correction returns the raw midpoint to the old seam under the core-zero hypothesis.

Candidate theorem:

```lean id="jj8ewa"
theorem shiftedSemanticCorrectedMidpoint_eq_seam_of_core_eq_zero
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) :
    shiftedSemanticCorrectedMidpoint r z = shiftedSemanticSeam r z
```

Expected proof route:
Use `shiftedSemanticRawMidpoint_eq_scaled_seam_of_core_eq_zero hcore z`.
Then simplify the scalar coefficient:

```text id="o08m3a"
(2 / phaseNormalization phaseCenter) *
  (phaseNormalization phaseCenter / 2) = 1
```

You may need a nonzero theorem for `phaseNormalization phaseCenter`. If no API exists, prove a local lemma from `phaseNormalization_sq_mul_phaseDepth phaseCenter` and `phaseDepth_center_eq`.

Part C:
Prove q2 recovery for the corrected midpoint.

Candidate theorem:

```lean id="zti0va"
theorem shiftedSemanticCorrectedMidpoint_q2_of_core_eq_zero
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) :
    Vec.q2 (shiftedSemanticCorrectedMidpoint r z) = Vec.q2 z
```

Prefer proving this from the equality with `shiftedSemanticSeam`, then reuse `shiftedSemanticSeam_q2`.

Part D:
Optionally add a raw shifted affine semantic helper, but do not normalize the whole path yet unless it is straightforward.

Candidate definition:

```lean id="ds0em5"
def shiftedSemanticRawAffine
    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) (t : ℝ) : Vec ℝ :=
  Vec.mk
    ((1 - t) * (shiftedSemanticLeftEndpoint r z).core +
      t * (shiftedSemanticRightEndpoint r z).core)
    ((1 - t) * (shiftedSemanticLeftEndpoint r z).beam +
      t * (shiftedSemanticRightEndpoint r z).beam)
```

Candidate endpoint and center theorem shapes:

```lean id="g18h0m"
theorem shiftedSemanticRawAffine_zero
    ...

theorem shiftedSemanticRawAffine_one
    ...

theorem shiftedSemanticRawAffine_center_eq_rawMidpoint
    ...
```

If this helper makes the correction law clearer, include it. If it creates proof noise, leave it for the next checkpoint.

Part E:
Update docs.

Update DkReal.lean and design-phase-center-shift-104.md.

Record:

```text id="xjw5s0"
raw shifted midpoint:
  falls to half q2 depth

corrected shifted midpoint:
  returns exactly to the old seam

remaining:
  choose whether the full shifted semantic edge should use pointwise q2 normalization,
  seam-centered projection, or another correction law
```

Part F:
Do not add the Euclidean one-eighth reading yet.

Required checks:

```text id="b4cxdc"
lake build DkMath.Analysis.DkReal.SemanticCF2DPhaseShift
lake build DkMath.Analysis.DkReal
git diff --check
```
