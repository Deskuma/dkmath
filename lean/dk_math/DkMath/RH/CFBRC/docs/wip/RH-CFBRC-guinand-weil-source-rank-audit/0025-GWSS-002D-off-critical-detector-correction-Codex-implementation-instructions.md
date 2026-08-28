# GWSS-002D off-critical detector correction — Codex implementation instructions

Date: 2026-08-21

Repository: `Deskuma/dkmath`

Branch: `wip/RH-CFBRC-guinand-weil-source-rank-audit-260820-v0`

## 0. Mission

Correct only the missing load-bearing GWSS-002D step in the implementation reported by `0024-GWSS-002-off-critical-Mellin-witness-report.md`.

Do not start GWSS-003.

Current review result:

```text
GWSS-002-A  FOUND
GWSS-002-B  FOUND
GWSS-002-C  FOUND
GWSS-002-D  MISSING FROM LOAD-BEARING WITNESS
GWSS-002-E  PARTIAL: admissible finite weight exists, but its nonzero moment currently detects occupancy only
```

The current final theorem proves, from an off-critical zero, both:

```text
(z^2).im != 0
and
exists admissible Mellin weight with nonzero zero-side moment
```

but these two conclusions are logically parallel.  The nonzero weighted moment is obtained only from nonzero orbit mass and does not use `(z^2).im != 0`.

Therefore the present weight would also have nonzero moment for a critical-line occupied orbit.  It is an orbit-occupancy witness, not yet an off-critical detector.

The missing bridge required by `0023` is:

```text
target orbit q0
  -> extract mass(q0)
  -> multiply by q0.im
  -> synthesize one Mellin weight whose zero-side moment equals q0.im * mass(q0)
  -> off-criticality makes that moment nonzero
```

Only after this is formalized may the classification return to:

```text
OFF-CRITICAL-MELLIN-WITNESS-FOUND
```

## 1. Trusted existing results

Reuse the existing implementation in:

```text
PascalCenteredXiMellinOffCriticalWitnessAudit.lean
PascalCenteredXiMellinActualWindowFullRankAudit.lean
```

In particular, keep and reuse:

```lean
pascalCenteredXiZeroDiskFinset_sq_im_ne_zero
pascalCenteredXiSquaredOrbitMass_ne_zero
exists_matrix_coordinate_extractor
exists_pascalCenteredXiMellinMoment_coordinate_extractor
pascalCenteredXiMellinWitnessWeight
pascalCenteredXiMellinWitnessWeight_differentiable
pascalCenteredXiMellinWitnessWeight_even
pascalCenteredXiMellinWitnessWeight_moment_eq
```

Do not rewrite A/B/C unless a tiny refactor is required.

## 2. Required scalar detector theorem

Let

```text
q0 := pascalCenteredXiSquaredOrbitCoordinate R j0
m0 := pascalCenteredXiSquaredOrbitMassVec R j0
```

Prove the exact scalar detector is nonzero under the actual off-critical target hypothesis:

```lean
theorem pascalCenteredXiOffCriticalOrbitScalarDetector_ne_zero
    {R : ℝ}
    (j0 : Fin (pascalCenteredXiSquaredOrbitIndexCard R))
    (hoff : (pascalCenteredXiSquaredOrbitCoordinate R j0).im ≠ 0)
    (hmass : pascalCenteredXiSquaredOrbitMassVec R j0 ≠ 0) :
    ((pascalCenteredXiSquaredOrbitCoordinate R j0).im : ℂ) *
        pascalCenteredXiSquaredOrbitMassVec R j0 ≠ 0 := by
  ...
```

Equivalent theorem shape is acceptable.

The proof must use both `hoff` and `hmass`.

## 3. Required scaled coordinate-extractor theorem

Starting from:

```lean
exists_pascalCenteredXiMellinMoment_coordinate_extractor
```

obtain coefficients `c0` satisfying:

```text
sum_i c0_i * moment_i = m0
```

Then define scaled coefficients conceptually by:

```text
c_i := (q0.im : ℂ) * c0_i
```

and prove the exact identity:

```text
sum_i c_i * moment_i = (q0.im : ℂ) * m0
```

A preferred theorem shape is:

```lean
theorem exists_pascalCenteredXiMellin_offCritical_detector_coefficients
    {R ε : ℝ}
    {τ : Fin (pascalCenteredXiSquaredOrbitIndexCard R) → ℝ}
    (hε : 0 < ε)
    (hdet : (pascalCenteredXiMellinEvaluationMatrix R ε τ).det ≠ 0)
    (j0 : Fin (pascalCenteredXiSquaredOrbitIndexCard R)) :
    ∃ c : Fin (pascalCenteredXiSquaredOrbitIndexCard R) → ℂ,
      (∑ i, c i * pascalCenteredXiMellinMomentVec R ε τ i) =
        ((pascalCenteredXiSquaredOrbitCoordinate R j0).im : ℂ) *
          pascalCenteredXiSquaredOrbitMassVec R j0 := by
  ...
```

If convenient, include `hoff` and conclude both the equality and nonzero result in one theorem.

This is finite algebra only.  No new analytic theorem is needed.

## 4. Required admissible off-critical witness theorem

Package the scaled coefficients using the existing:

```lean
pascalCenteredXiMellinWitnessWeight ε τ c
```

and prove a local theorem parameterized by `hε`, `hdet`, `j0`, `hoff`, and target-mass nonzero, whose zero-side moment has the exact value:

```text
(q0.im : ℂ) * massVec(j0)
```

and hence is nonzero.

Preferred semantic shape:

```lean
theorem exists_pascalCenteredXiMellinOffCriticalWitness_of_full_rank_target
    {R ε : ℝ}
    (hε : 0 < ε)
    {τ : Fin (pascalCenteredXiSquaredOrbitIndexCard R) → ℝ}
    (hdet : (pascalCenteredXiMellinEvaluationMatrix R ε τ).det ≠ 0)
    (j0 : Fin (pascalCenteredXiSquaredOrbitIndexCard R))
    (hoff : (pascalCenteredXiSquaredOrbitCoordinate R j0).im ≠ 0)
    (hmass : pascalCenteredXiSquaredOrbitMassVec R j0 ≠ 0) :
    ∃ c,
      Differentiable ℂ (pascalCenteredXiMellinWitnessWeight ε τ c) ∧
      PascalCenteredEvenWeight (pascalCenteredXiMellinWitnessWeight ε τ c) ∧
      pascalCenteredXiZeroDiskWeightedMoment
          (pascalCenteredXiMellinWitnessWeight ε τ c) R =
        ((pascalCenteredXiSquaredOrbitCoordinate R j0).im : ℂ) *
          pascalCenteredXiSquaredOrbitMassVec R j0 ∧
      pascalCenteredXiZeroDiskWeightedMoment
          (pascalCenteredXiMellinWitnessWeight ε τ c) R ≠ 0 := by
  ...
```

Equivalent packaging is acceptable, but the exact detector value should be public if practical.

## 5. Repair the global theorem

Replace or strengthen:

```lean
exists_pascalCenteredXiMellinOffCriticalWitness
```

so that the returned witness moment is load-bearingly tied to the target off-critical coordinate.

For the selected target `z`, after obtaining `j0` with:

```text
pascalCenteredXiSquaredOrbitCoordinate R j0 = z^2
```

the theorem should prove the synthesized weight has zero-side moment equal to:

```text
((z^2).im : ℂ) * pascalCenteredXiSquaredOrbitMass R (z^2)
```

or the equivalent indexed mass expression.

Then derive nonzero using:

```text
pascalCenteredXiZeroDiskFinset_sq_im_ne_zero hz hre
pascalCenteredXiSquaredOrbitMass_ne_zero hq
```

The key review test is:

```text
If `hre : z.re ≠ 0` is removed, the final nonzero witness conclusion must no longer follow from the theorem as stated.
```

It is acceptable for the theorem still to return `(z^2).im ≠ 0` as an additional conjunct, but that fact must also enter the proof of the witness moment nonvanishing.

## 6. Critical-line sanity theorem

Add one small semantic sanity theorem if it is cheap:

```text
for an actual zero with z.re = 0,
((z^2).im : ℂ) * orbitMass(z^2) = 0
```

This is not needed for the one-way witness classification, but it confirms that the detector genuinely vanishes on the critical line rather than merely being a generic occupied-orbit witness.

Do not turn this into a new equivalence framework.

## 7. Report correction

Update `0024-GWSS-002-off-critical-Mellin-witness-report.md` or add a narrowly scoped follow-up report, preferably:

```text
0026-GWSS-002D-off-critical-detector-correction-report.md
```

The report must state explicitly that the first 0024 implementation had a semantic gap:

```text
The original nonzero moment used occupied-orbit mass only; off-criticality was
reported in parallel but did not load-bearingly imply witness nonvanishing.
```

Then document the corrected exact detector identity.

## 8. Classification

Until this correction is proved:

```text
GWSS-002: NOT CLOSED
GWSS-003: NOT AUTHORIZED
```

After the exact off-critical detector weight is proved and verified:

```text
OFF-CRITICAL-MELLIN-WITNESS-FOUND
GWSS-002: CLOSED
Next unresolved Gap: MELLIN-WITNESS-ARITHMETIC-CONTROL-GAP
GWSS-003: authorized next but not started
GWSS-004: not authorized
```

## 9. Firewall

Do not add:

```text
prime-side estimates
archimedean estimates
elementary-term estimates
top-horizontal removal
T -> infinity
Weil positivity
Li criterion
RH deduction
functional-equation reflection as a provider
```

The coefficient vector remains target/carrier dependent.  It is an existential finite combination inside the already-certified canonical Mellin family, not a new independent source.

## 10. Verification

Run at minimum:

```text
lake build DkMath.RH.CFBRC.PascalCenteredXiMellinOffCriticalWitnessAudit
git diff --check
```

Inspect `#print axioms` for:

```text
scalar off-critical detector nonzero
scaled coordinate extractor
local admissible off-critical witness
final global off-critical witness
```

Requirements:

```text
NO sorry
NO admit
NO native_decide
NO new axiom
```

Expected axiom footprint remains:

```text
propext
Classical.choice
Quot.sound
```

After the correction report, STOP.  Do not start GWSS-003 in the same assignment.
