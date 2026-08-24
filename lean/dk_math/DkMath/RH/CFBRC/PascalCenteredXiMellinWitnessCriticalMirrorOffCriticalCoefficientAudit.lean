/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.PascalCenteredXiMellinWitnessCriticalMirrorExtractorAudit
import Mathlib.Tactic

/-!
# GWSS-003H4: canonical off-critical coefficient and detector transport

This module scales the canonical finite Mellin extractor row by the target
squared-coordinate imaginary part.  The critical mirror changes that real
scalar's sign and conjugates the extractor row, giving the exact coefficient
law `cOff (mirror j) = -conj (cOff j)`.  The finite mass vector and detector
scalar are transported separately from the matrix inversion.

Only finite coefficient and detector identities are proved here.  The
synthesized witness feature, whole-source transport, shifted energies,
positivity, and source-rank claims are outside this stage.
 -/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open DkMath.Analysis
open scoped BigOperators ComplexConjugate Matrix

/-! ## H6-A: target imaginary scalar -/

/-- The target squared-coordinate imaginary part, cast to the coefficient
field. -/
noncomputable def pascalCenteredXiSquaredOrbitImaginaryScalar
    (R : ℝ)
    (j : Fin (pascalCenteredXiSquaredOrbitIndexCard R)) : ℂ :=
  (pascalCenteredXiSquaredOrbitCoordinate R j).im

/-- The target imaginary scalar changes sign under the canonical critical
mirror, including the self-mirror zero case. -/
theorem pascalCenteredXiSquaredOrbitImaginaryScalar_mirror
    (R : ℝ) (j : Fin (pascalCenteredXiSquaredOrbitIndexCard R)) :
    pascalCenteredXiSquaredOrbitImaginaryScalar R
        (pascalCenteredXiSquaredOrbitMirrorIndex R j) =
      -pascalCenteredXiSquaredOrbitImaginaryScalar R j := by
  unfold pascalCenteredXiSquaredOrbitImaginaryScalar
  rw [pascalCenteredXiSquaredOrbitMirrorIndex_spec]
  simp

/-! ## H6-B/C: canonical coefficient row -/

/-- The canonical off-critical coefficient row is the canonical inverse
extractor row scaled by the target squared-coordinate imaginary part. -/
noncomputable def pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow
    (R ε : ℝ)
    (τ : Fin (pascalCenteredXiSquaredOrbitIndexCard R) → ℝ)
    (j : Fin (pascalCenteredXiSquaredOrbitIndexCard R)) :
    Fin (pascalCenteredXiSquaredOrbitIndexCard R) → ℂ :=
  fun i => pascalCenteredXiSquaredOrbitImaginaryScalar R j *
    pascalCenteredXiMellinCanonicalExtractorRow R ε τ j i

/-- Entrywise critical-mirror transport of the canonical off-critical
coefficient row.  The conjugation is retained: this is not a real-valuedness
claim about the extractor row. -/
theorem pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow_mirror
    {R ε : ℝ}
    (hε : 0 < ε)
    (τ : Fin (pascalCenteredXiSquaredOrbitIndexCard R) → ℝ)
    (hdet : (pascalCenteredXiMellinEvaluationMatrix R ε τ).det ≠ 0)
    (j : Fin (pascalCenteredXiSquaredOrbitIndexCard R))
    (i : Fin (pascalCenteredXiSquaredOrbitIndexCard R)) :
    pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow R ε τ
        (pascalCenteredXiSquaredOrbitMirrorIndex R j) i =
      -conj (pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow R ε τ j i) := by
  unfold pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow
  rw [pascalCenteredXiSquaredOrbitImaginaryScalar_mirror,
    pascalCenteredXiMellinCanonicalExtractorRow_mirror hε τ hdet]
  simp [pascalCenteredXiSquaredOrbitImaginaryScalar, Complex.conj_ofReal,
    mul_comm]

/-- Function-level form of the canonical coefficient-row mirror law. -/
theorem pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow_mirror_fun
    {R ε : ℝ}
    (hε : 0 < ε)
    (τ : Fin (pascalCenteredXiSquaredOrbitIndexCard R) → ℝ)
    (hdet : (pascalCenteredXiMellinEvaluationMatrix R ε τ).det ≠ 0)
    (j : Fin (pascalCenteredXiSquaredOrbitIndexCard R)) :
    pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow R ε τ
        (pascalCenteredXiSquaredOrbitMirrorIndex R j) =
      fun i => -conj (pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow
        R ε τ j i) := by
  funext i
  exact pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow_mirror
    hε τ hdet j i

/-! ## H6-D/E: mass vector and detector scalar -/

/-- The canonical mirror preserves the finite multiplicity-weighted mass
vector.  This uses the canonical coordinate specification directly rather
than identifying two independent existential choices. -/
theorem pascalCenteredXiSquaredOrbitMassVec_mirror
    (R : ℝ) (j : Fin (pascalCenteredXiSquaredOrbitIndexCard R)) :
    pascalCenteredXiSquaredOrbitMassVec R
        (pascalCenteredXiSquaredOrbitMirrorIndex R j) =
      pascalCenteredXiSquaredOrbitMassVec R j := by
  unfold pascalCenteredXiSquaredOrbitMassVec
  rw [pascalCenteredXiSquaredOrbitMirrorIndex_spec,
    pascalCenteredXiSquaredOrbitMass_conj]

/-- The signed finite detector scalar formed from the target imaginary part
and its multiplicity-weighted orbit mass. -/
noncomputable def pascalCenteredXiMellinCanonicalDetectorScalar
    (R : ℝ) (j : Fin (pascalCenteredXiSquaredOrbitIndexCard R)) : ℂ :=
  pascalCenteredXiSquaredOrbitImaginaryScalar R j *
    pascalCenteredXiSquaredOrbitMassVec R j

/-- The canonical detector scalar is odd under the critical mirror. -/
theorem pascalCenteredXiMellinCanonicalDetectorScalar_mirror
    (R : ℝ) (j : Fin (pascalCenteredXiSquaredOrbitIndexCard R)) :
    pascalCenteredXiMellinCanonicalDetectorScalar R
        (pascalCenteredXiSquaredOrbitMirrorIndex R j) =
      -pascalCenteredXiMellinCanonicalDetectorScalar R j := by
  unfold pascalCenteredXiMellinCanonicalDetectorScalar
  rw [pascalCenteredXiSquaredOrbitImaginaryScalar_mirror,
    pascalCenteredXiSquaredOrbitMassVec_mirror]
  ring

/-! ## H6-F: canonical detector extraction -/

/-- The canonical off-critical row extracts the signed detector scalar from
the actual finite Mellin moment vector. -/
theorem pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow_extracts
    {R ε : ℝ}
    (hε : 0 < ε)
    (τ : Fin (pascalCenteredXiSquaredOrbitIndexCard R) → ℝ)
    (hdet : (pascalCenteredXiMellinEvaluationMatrix R ε τ).det ≠ 0)
    (j : Fin (pascalCenteredXiSquaredOrbitIndexCard R)) :
    ∑ i,
      pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow R ε τ j i *
        pascalCenteredXiMellinMomentVec R ε τ i =
      pascalCenteredXiMellinCanonicalDetectorScalar R j := by
  unfold pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow
  let a := pascalCenteredXiSquaredOrbitImaginaryScalar R j
  have hmul (f : Fin (pascalCenteredXiSquaredOrbitIndexCard R) → ℂ) :
      a * (∑ i, f i) = ∑ i, a * f i := by
    simpa using (Finset.mul_sum
      (Finset.univ : Finset (Fin (pascalCenteredXiSquaredOrbitIndexCard R))) f a)
  have hmoment := pascalCenteredXiMellinMomentVec_eq_mellinEvaluation_mulVec_massVec
    hε τ
  have hmoment' :
      pascalCenteredXiMellinMomentVec R ε τ =
        pascalCenteredXiMellinEvaluationMatrix R ε τ *ᵥ
          pascalCenteredXiSquaredOrbitMassVec R := by
    change pascalCenteredXiMellinMomentVec R ε τ =
      (fun i j => pascalCenteredXiMellinSecondDifferenceWeight ε (τ i)
        (pascalCenteredXiSquaredOrbitRepresentativeFin R j)) *ᵥ
        pascalCenteredXiSquaredOrbitMassVec R
    exact hmoment
  have hextract := pascalCenteredXiMellinCanonicalExtractorRow_extracts
    τ hdet j (pascalCenteredXiSquaredOrbitMassVec R)
  calc
    ∑ i, (a * pascalCenteredXiMellinCanonicalExtractorRow R ε τ j i) *
        pascalCenteredXiMellinMomentVec R ε τ i =
        ∑ i, a * (pascalCenteredXiMellinCanonicalExtractorRow R ε τ j i *
          pascalCenteredXiMellinMomentVec R ε τ i) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = a * ∑ i, pascalCenteredXiMellinCanonicalExtractorRow R ε τ j i *
        pascalCenteredXiMellinMomentVec R ε τ i := by
      rw [hmul]
    _ = a * ∑ i, pascalCenteredXiMellinCanonicalExtractorRow R ε τ j i *
        (((pascalCenteredXiMellinEvaluationMatrix R ε τ) *ᵥ
          pascalCenteredXiSquaredOrbitMassVec R) i) := by
      rw [hmoment']
    _ = a * pascalCenteredXiSquaredOrbitMassVec R j := by
      rw [hextract]
    _ = pascalCenteredXiMellinCanonicalDetectorScalar R j := by
      rfl

/-! ## H6-G: paired canonical detector extraction -/

/-- The two canonical mirror endpoint detector sums are exact negatives. -/
theorem pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow_paired_extracts_neg
    {R ε : ℝ}
    (hε : 0 < ε)
    (τ : Fin (pascalCenteredXiSquaredOrbitIndexCard R) → ℝ)
    (hdet : (pascalCenteredXiMellinEvaluationMatrix R ε τ).det ≠ 0)
    (j : Fin (pascalCenteredXiSquaredOrbitIndexCard R)) :
    (∑ i,
      pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow R ε τ
          (pascalCenteredXiSquaredOrbitMirrorIndex R j) i *
        pascalCenteredXiMellinMomentVec R ε τ i) =
      -(∑ i,
        pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow R ε τ j i *
          pascalCenteredXiMellinMomentVec R ε τ i) := by
  rw [pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow_extracts
      hε τ hdet (pascalCenteredXiSquaredOrbitMirrorIndex R j),
    pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow_extracts
      hε τ hdet j,
    pascalCenteredXiMellinCanonicalDetectorScalar_mirror]

end DkMath.RH.CFBRCProjection
