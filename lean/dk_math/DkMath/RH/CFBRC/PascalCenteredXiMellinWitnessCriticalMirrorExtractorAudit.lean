/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.PascalCenteredXiMellinWitnessCriticalMirrorPairAudit
import Mathlib.Tactic

/-!
# GWSS-003H3: mirror Mellin matrix and extractor transport

This module audits the actual finite general-`τ` Mellin evaluation matrix
under the centered critical mirror.  The proof first establishes conjugation
covariance of the finite Mellin weight, then turns the existential coordinate
matching from GWSS-003H2 into a canonical involutive `Fin` map.  Equal-square
representatives are compared through the evenness of the Mellin weight, so no
choice of a zero representative is treated as mathematical data.

The final transport statement concerns only the canonical inverse-matrix
extractor row.  It does not multiply by a target imaginary part, transport an
off-critical coefficient row, or make a positivity/source-rank claim.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open DkMath.Analysis
open Filter
open scoped BigOperators ComplexConjugate Interval Matrix Topology

/-! ## H5-A: conjugation covariance of the finite Mellin weight -/

/-- The centered box Mellin spectral weight commutes with complex conjugation.
The proof is the exact finite logarithmic-average formula; no Mellin limit or
continuation is used. -/
theorem centeredMellinSpectralWeight_centeredMellinBoxApprox_conj
    {ε : ℝ} (hε : 0 < ε) (z : ℂ) :
    centeredMellinSpectralWeight (centeredMellinBoxApprox ε) (conj z) =
      conj (centeredMellinSpectralWeight (centeredMellinBoxApprox ε) z) := by
  rw [centeredMellinSpectralWeight_centeredMellinBoxApprox_eq_logAverage hε,
    centeredMellinSpectralWeight_centeredMellinBoxApprox_eq_logAverage hε]
  simp only [map_mul, map_inv₀, Complex.conj_ofReal]
  simp only [intervalIntegral.intervalIntegral_eq_integral_uIoc]
  have hne : -ε ≤ ε := by linarith
  simp only [ite_eq_left hne, one_smul]
  rw [← integral_conj]
  apply congrArg (fun x : ℂ => ((2 * ε : ℝ)⁻¹ : ℂ) * x)
  apply MeasureTheory.integral_congr_ae
  filter_upwards [] with t
  rw [← Complex.exp_conj]
  congr 1
  simp [Complex.conj_ofReal, mul_comm]

/-- The actual centered Mellin second-difference weight commutes with complex
conjugation for every real dilation parameter, including the patched `τ = 0`
branch. -/
theorem pascalCenteredXiMellinSecondDifferenceWeight_conj
    {ε τ : ℝ} (hε : 0 < ε) (z : ℂ) :
    pascalCenteredXiMellinSecondDifferenceWeight ε τ (conj z) =
      conj (pascalCenteredXiMellinSecondDifferenceWeight ε τ z) := by
  by_cases hτ : τ = 0
  · subst τ
    rw [pascalCenteredXiMellinSecondDifferenceWeight_tau_zero_eq_quadraticWeight
        hε (conj z),
      pascalCenteredXiMellinSecondDifferenceWeight_tau_zero_eq_quadraticWeight
        hε z,
      centeredMellinSpectralWeight_centeredMellinBoxApprox_conj hε]
    simp only [map_mul, map_pow, starRingEnd_apply]
  · rw [pascalCenteredXiMellinSecondDifferenceWeight_eq_kernel_mul hτ,
      pascalCenteredXiMellinSecondDifferenceWeight_eq_kernel_mul hτ,
      centeredMellinSpectralWeight_centeredMellinBoxApprox_conj hε]
    have hreal : (starRingEnd ℂ) (τ : ℂ) = (τ : ℂ) := by
      exact Complex.conj_ofReal τ
    have hτconj :
        (τ : ℂ) * conj z = conj ((τ : ℂ) * z) := by
      rw [map_mul]
      rw [hreal]
    have hτnegconj :
        -(τ : ℂ) * conj z = conj (-(τ : ℂ) * z) := by
      rw [map_mul, map_neg, hreal]
    have hkernel :
        (Complex.exp ((τ : ℂ) * (conj z)) - 2 +
            Complex.exp (-(τ : ℂ) * (conj z))) / (τ : ℂ) ^ 2 =
          conj ((Complex.exp ((τ : ℂ) * z) - 2 +
            Complex.exp (-(τ : ℂ) * z)) / (τ : ℂ) ^ 2) := by
      rw [hτconj, hτnegconj, Complex.exp_conj, Complex.exp_conj]
      simp only [map_div₀, map_sub, map_add, map_pow, map_ofNat,
        starRingEnd_apply]
      have hreal' : star (τ : ℂ) = (τ : ℂ) := Complex.conj_ofReal τ
      rw [hreal']
    rw [hkernel]
    simp only [map_mul]

/-! ## H5-B: canonical mirror permutation -/

/-- The canonical mirror index in the fixed `Fin` presentation of the actual
squared-orbit carrier. -/
noncomputable def pascalCenteredXiSquaredOrbitMirrorIndex
    (R : ℝ)
    (j : Fin (pascalCenteredXiSquaredOrbitIndexCard R)) :
    Fin (pascalCenteredXiSquaredOrbitIndexCard R) :=
  Classical.choose (exists_pascalCenteredXiSquaredOrbitMirrorIndex R j)

/-- The canonical mirror index has the expected conjugate coordinate. -/
theorem pascalCenteredXiSquaredOrbitMirrorIndex_spec
    (R : ℝ) (j : Fin (pascalCenteredXiSquaredOrbitIndexCard R)) :
    pascalCenteredXiSquaredOrbitCoordinate R
        (pascalCenteredXiSquaredOrbitMirrorIndex R j) =
      conj (pascalCenteredXiSquaredOrbitCoordinate R j) := by
  exact Classical.choose_spec
    (exists_pascalCenteredXiSquaredOrbitMirrorIndex R j)

/-- The canonical mirror index is an involution. -/
theorem pascalCenteredXiSquaredOrbitMirrorIndex_involutive
    (R : ℝ) (j : Fin (pascalCenteredXiSquaredOrbitIndexCard R)) :
    pascalCenteredXiSquaredOrbitMirrorIndex R
        (pascalCenteredXiSquaredOrbitMirrorIndex R j) = j := by
  apply pascalCenteredXiSquaredOrbitCoordinate_injective R
  rw [pascalCenteredXiSquaredOrbitMirrorIndex_spec,
    pascalCenteredXiSquaredOrbitMirrorIndex_spec]
  simp only [starRingEnd_apply, star_star]

/-! ## H5-C: representative-level column transport -/

/-- The selected representative at the mirror index has the conjugate square
of the original selected representative. -/
theorem pascalCenteredXiSquaredOrbitRepresentativeFin_mirror_sq
    (R : ℝ) (j : Fin (pascalCenteredXiSquaredOrbitIndexCard R)) :
    pascalCenteredXiSquaredOrbitRepresentativeFin R
        (pascalCenteredXiSquaredOrbitMirrorIndex R j) ^ 2 =
      conj (pascalCenteredXiSquaredOrbitRepresentativeFin R j ^ 2) := by
  rw [pascalCenteredXiSquaredOrbitRepresentativeFin_sq,
    pascalCenteredXiSquaredOrbitMirrorIndex_spec,
    pascalCenteredXiSquaredOrbitRepresentativeFin_sq]

private theorem complex_sq_eq_sq_iff_mirror
    {a b : ℂ} (hsq : a ^ 2 = b ^ 2) : a = b ∨ a = -b := by
  have hfac : (a - b) * (a + b) = 0 := by
    calc
      (a - b) * (a + b) = a ^ 2 - b ^ 2 := by ring
      _ = 0 := by rw [hsq, sub_self]
  rcases mul_eq_zero.mp hfac with hab | hab
  · exact Or.inl (sub_eq_zero.mp hab)
  · exact Or.inr (eq_neg_of_add_eq_zero_left hab)

private theorem pascalCenteredXiMellinSecondDifferenceWeight_eq_of_sq_eq_mirror
    {ε τ : ℝ} (hε : 0 < ε) {a b : ℂ}
    (hsq : a ^ 2 = b ^ 2) :
    pascalCenteredXiMellinSecondDifferenceWeight ε τ a =
      pascalCenteredXiMellinSecondDifferenceWeight ε τ b := by
  rcases complex_sq_eq_sq_iff_mirror hsq with rfl | rfl
  · rfl
  · exact pascalCenteredXiMellinSecondDifferenceWeight_even hε b

/-- The actual Mellin matrix column at a mirror index is the entrywise complex
conjugate of the original column.  The real row parameter `τ i` is unchanged. -/
theorem pascalCenteredXiMellinEvaluationMatrix_mirror_entry
    {R ε : ℝ} (hε : 0 < ε)
    (τ : Fin (pascalCenteredXiSquaredOrbitIndexCard R) → ℝ)
    (i j : Fin (pascalCenteredXiSquaredOrbitIndexCard R)) :
    pascalCenteredXiMellinEvaluationMatrix R ε τ i
        (pascalCenteredXiSquaredOrbitMirrorIndex R j) =
      conj (pascalCenteredXiMellinEvaluationMatrix R ε τ i j) := by
  unfold pascalCenteredXiMellinEvaluationMatrix
  have hrep_sq :
      pascalCenteredXiSquaredOrbitRepresentativeFin R
          (pascalCenteredXiSquaredOrbitMirrorIndex R j) ^ 2 =
        (conj (pascalCenteredXiSquaredOrbitRepresentativeFin R j)) ^ 2 := by
    rw [pascalCenteredXiSquaredOrbitRepresentativeFin_mirror_sq]
    simp only [pow_two, map_mul, starRingEnd_apply]
  calc
    pascalCenteredXiMellinSecondDifferenceWeight ε (τ i)
        (pascalCenteredXiSquaredOrbitRepresentativeFin R
          (pascalCenteredXiSquaredOrbitMirrorIndex R j)) =
        pascalCenteredXiMellinSecondDifferenceWeight ε (τ i)
          (conj (pascalCenteredXiSquaredOrbitRepresentativeFin R j)) :=
      pascalCenteredXiMellinSecondDifferenceWeight_eq_of_sq_eq_mirror hε hrep_sq
    _ = conj (pascalCenteredXiMellinSecondDifferenceWeight ε (τ i)
          (pascalCenteredXiSquaredOrbitRepresentativeFin R j)) :=
      pascalCenteredXiMellinSecondDifferenceWeight_conj hε _

/-! ## H5-D: finite matrix reindexing -/

/-- Reindexing the columns by the canonical mirror involution is exactly
entrywise conjugation of the finite Mellin matrix. -/
theorem pascalCenteredXiMellinEvaluationMatrix_mirror_columns_eq_conj
    {R ε : ℝ} (hε : 0 < ε)
    (τ : Fin (pascalCenteredXiSquaredOrbitIndexCard R) → ℝ) :
    (fun i j => pascalCenteredXiMellinEvaluationMatrix R ε τ i
      (pascalCenteredXiSquaredOrbitMirrorIndex R j)) =
      (fun i j => conj (pascalCenteredXiMellinEvaluationMatrix R ε τ i j)) := by
  funext i j
  exact pascalCenteredXiMellinEvaluationMatrix_mirror_entry hε τ i j

/-! ## H5-E: canonical inverse extractor row -/

/-- The canonical inverse-matrix row targeting a squared-orbit coordinate. -/
noncomputable def pascalCenteredXiMellinCanonicalExtractorRow
    (R ε : ℝ)
    (τ : Fin (pascalCenteredXiSquaredOrbitIndexCard R) → ℝ)
    (j : Fin (pascalCenteredXiSquaredOrbitIndexCard R)) :
    Fin (pascalCenteredXiSquaredOrbitIndexCard R) → ℂ :=
  fun i => (pascalCenteredXiMellinEvaluationMatrix R ε τ)⁻¹ j i

private theorem pascalCenteredXiMellinCanonicalExtractorRow_mul_eq_single
    {R ε : ℝ}
    (τ : Fin (pascalCenteredXiSquaredOrbitIndexCard R) → ℝ)
    (hdet : (pascalCenteredXiMellinEvaluationMatrix R ε τ).det ≠ 0)
    (j : Fin (pascalCenteredXiSquaredOrbitIndexCard R)) :
    pascalCenteredXiMellinCanonicalExtractorRow R ε τ j ᵥ*
        pascalCenteredXiMellinEvaluationMatrix R ε τ =
      fun k => if j = k then (1 : ℂ) else 0 := by
  let H := pascalCenteredXiMellinEvaluationMatrix R ε τ
  have hunit : IsUnit H.det := by
    apply isUnit_iff_ne_zero.mpr
    simpa [H] using hdet
  change (fun i => H⁻¹ j i) ᵥ* H = _
  ext k
  calc
    ((fun i => H⁻¹ j i) ᵥ* H) k = (H⁻¹ * H) j k := rfl
    _ = (1 : Matrix _ _ ℂ) j k := by
      rw [Matrix.nonsing_inv_mul H hunit]
    _ = if j = k then (1 : ℂ) else 0 := by
      simp [Matrix.one_apply]

/-- The canonical inverse row extracts its target coordinate from the finite
Mellin matrix. -/
theorem pascalCenteredXiMellinCanonicalExtractorRow_extracts
    {R ε : ℝ}
    (τ : Fin (pascalCenteredXiSquaredOrbitIndexCard R) → ℝ)
    (hdet : (pascalCenteredXiMellinEvaluationMatrix R ε τ).det ≠ 0)
    (j : Fin (pascalCenteredXiSquaredOrbitIndexCard R))
    (m : Fin (pascalCenteredXiSquaredOrbitIndexCard R) → ℂ) :
    ∑ i, pascalCenteredXiMellinCanonicalExtractorRow R ε τ j i *
        (pascalCenteredXiMellinEvaluationMatrix R ε τ *ᵥ m) i = m j := by
  let H := pascalCenteredXiMellinEvaluationMatrix R ε τ
  have hrow := pascalCenteredXiMellinCanonicalExtractorRow_mul_eq_single τ hdet j
  change pascalCenteredXiMellinCanonicalExtractorRow R ε τ j ⬝ᵥ (H *ᵥ m) = m j
  rw [Matrix.dotProduct_mulVec, hrow]
  simp [dotProduct]

private theorem pascalCenteredXiMellinCanonicalExtractorRow_conj_mul_eq_single
    {R ε : ℝ}
    (hε : 0 < ε)
    (τ : Fin (pascalCenteredXiSquaredOrbitIndexCard R) → ℝ)
    (hdet : (pascalCenteredXiMellinEvaluationMatrix R ε τ).det ≠ 0)
    (j : Fin (pascalCenteredXiSquaredOrbitIndexCard R)) :
    (fun i => conj (pascalCenteredXiMellinCanonicalExtractorRow R ε τ j i)) ᵥ*
        pascalCenteredXiMellinEvaluationMatrix R ε τ =
      fun k => if pascalCenteredXiSquaredOrbitMirrorIndex R j = k then
        (1 : ℂ) else 0 := by
  let H := pascalCenteredXiMellinEvaluationMatrix R ε τ
  let μ := pascalCenteredXiSquaredOrbitMirrorIndex R
  have hentry (i k : Fin (pascalCenteredXiSquaredOrbitIndexCard R)) :
      H i k = conj (H i (μ k)) := by
    have h := pascalCenteredXiMellinEvaluationMatrix_mirror_entry
      hε τ i (μ k)
    simpa [H, μ, pascalCenteredXiSquaredOrbitMirrorIndex_involutive]
      using h
  have hrow := pascalCenteredXiMellinCanonicalExtractorRow_mul_eq_single τ hdet j
  ext k
  have hsum :
      ∑ i, conj (pascalCenteredXiMellinCanonicalExtractorRow R ε τ j i) *
          H i k =
        conj (∑ i, pascalCenteredXiMellinCanonicalExtractorRow R ε τ j i *
          H i (μ k)) := by
    calc
      ∑ i, conj (pascalCenteredXiMellinCanonicalExtractorRow R ε τ j i) *
          H i k =
          ∑ i, conj (pascalCenteredXiMellinCanonicalExtractorRow R ε τ j i) *
            conj (H i (μ k)) := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [hentry]
      _ = conj (∑ i, pascalCenteredXiMellinCanonicalExtractorRow R ε τ j i *
          H i (μ k)) := by
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro i hi
        simp only [map_mul, starRingEnd_apply]
  change (∑ i, conj (pascalCenteredXiMellinCanonicalExtractorRow R ε τ j i) *
      H i k) = if μ j = k then (1 : ℂ) else 0
  rw [hsum]
  have hrow_at :
      (∑ i, pascalCenteredXiMellinCanonicalExtractorRow R ε τ j i *
          H i (μ k)) = if j = μ k then (1 : ℂ) else 0 := by
    simpa [H, Matrix.vecMul, dotProduct] using congrFun hrow (μ k)
  rw [hrow_at]
  have hiff : j = μ k ↔ μ j = k := by
    constructor
    · intro h
      subst j
      simpa [μ] using pascalCenteredXiSquaredOrbitMirrorIndex_involutive R k
    · intro h
      subst k
      simpa [μ] using (pascalCenteredXiSquaredOrbitMirrorIndex_involutive R j).symm
  simp [hiff]

/-- The canonical inverse extractor row transports by entrywise conjugation
under the canonical mirror permutation.  No target `q.im` factor is included. -/
theorem pascalCenteredXiMellinCanonicalExtractorRow_mirror
    {R ε : ℝ}
    (hε : 0 < ε)
    (τ : Fin (pascalCenteredXiSquaredOrbitIndexCard R) → ℝ)
    (hdet : (pascalCenteredXiMellinEvaluationMatrix R ε τ).det ≠ 0)
    (j : Fin (pascalCenteredXiSquaredOrbitIndexCard R)) (i : Fin _) :
    pascalCenteredXiMellinCanonicalExtractorRow R ε τ
        (pascalCenteredXiSquaredOrbitMirrorIndex R j) i =
      conj (pascalCenteredXiMellinCanonicalExtractorRow R ε τ j i) := by
  let H := pascalCenteredXiMellinEvaluationMatrix R ε τ
  let μ := pascalCenteredXiSquaredOrbitMirrorIndex R
  have hinj : Function.Injective (fun v : Fin _ → ℂ => v ᵥ* H) := by
    apply (Matrix.vecMul_injective_iff_isUnit (A := H)).mpr
    apply (Matrix.isUnit_iff_isUnit_det H).mpr
    exact isUnit_iff_ne_zero.mpr (by simpa [H] using hdet)
  have hleft := pascalCenteredXiMellinCanonicalExtractorRow_mul_eq_single τ hdet (μ j)
  have hright := pascalCenteredXiMellinCanonicalExtractorRow_conj_mul_eq_single
    hε τ hdet j
  have hrows :
      pascalCenteredXiMellinCanonicalExtractorRow R ε τ (μ j) ᵥ* H =
        (fun k => conj (pascalCenteredXiMellinCanonicalExtractorRow R ε τ j k)) ᵥ* H := by
    rw [hleft, hright]
  have heq := hinj hrows
  exact congrFun heq i

end DkMath.RH.CFBRCProjection
