/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberGeometry.Gauge

namespace DkMath.NumberGeometry
noncomputable section

/-!
# Similarity transport for the two-point gauge

An affine similarity is represented by a translation, a real scale, and a
linear isometry equivalence.  The transport API is stated first for square
mass, so it remains meaningful at the zero scale.
-/

/-- The affine similarity `P ↦ t + c • R P`. -/
def similarityMap
    (t : Point) (c : ℝ)
    (R : Point ≃ₗᵢ[ℝ] Point)
    (P : Point) : Point :=
  t + c • R P

/-- The oriented pair gap is transported by the scaled linear isometry. -/
theorem pairVec_similarity
    (t : Point) (c : ℝ)
    (R : Point ≃ₗᵢ[ℝ] Point)
    (A B : Point) :
    pairVec (similarityMap t c R A) (similarityMap t c R B)
      = c • R (pairVec A B) := by
  simp [pairVec, similarityMap, sub_eq_add_neg,
    add_assoc, add_left_comm, add_comm]

/-- Pair mass scales by the square of the real similarity scale. -/
theorem pairMass_similarity
    (t : Point) (c : ℝ)
    (R : Point ≃ₗᵢ[ℝ] Point)
    (A B : Point) :
    pairMass (similarityMap t c R A) (similarityMap t c R B)
      = c ^ 2 * pairMass A B := by
  calc
    pairMass (similarityMap t c R A) (similarityMap t c R B) =
        ‖c • R (pairVec A B)‖ ^ 2 := by
      rw [pairMass, pairVec_similarity]
    _ = (‖c‖ * ‖R (pairVec A B)‖) ^ 2 := by rw [norm_smul]
    _ = (|c| * ‖pairVec A B‖) ^ 2 := by rw [Real.norm_eq_abs, R.norm_map]
    _ = c ^ 2 * pairMass A B := by
      rw [mul_pow, sq_abs]
      rfl

/-- Translating both points leaves pair mass unchanged. -/
theorem pairMass_translation (t A B : Point) :
    pairMass (t + A) (t + B) = pairMass A B := by
  simpa [similarityMap] using
    (pairMass_similarity t 1 (LinearIsometryEquiv.refl ℝ Point) A B)

/-- A linear isometry equivalence preserves pair mass. -/
theorem pairMass_linearIsometry
    (R : Point ≃ₗᵢ[ℝ] Point) (A B : Point) :
    pairMass (R A) (R B) = pairMass A B := by
  simpa [similarityMap] using (pairMass_similarity 0 1 R A B)

/-- Scaling both points scales pair mass by the square of the scale. -/
theorem pairMass_scale (c : ℝ) (A B : Point) :
    pairMass (c • A) (c • B) = c ^ 2 * pairMass A B := by
  simpa [similarityMap] using
    (pairMass_similarity 0 c (LinearIsometryEquiv.refl ℝ Point) A B)

namespace TwoPointKernel

/-- Map a two-point kernel pointwise along a function. -/
def map (T : Point → Point) (K : TwoPointKernel) : TwoPointKernel where
  source := T K.source
  target := T K.target

/-- The source of a mapped kernel is the mapped source. -/
@[simp]
theorem map_source (T : Point → Point) (K : TwoPointKernel) :
    (K.map T).source = T K.source := rfl

/-- The target of a mapped kernel is the mapped target. -/
@[simp]
theorem map_target (T : Point → Point) (K : TwoPointKernel) :
    (K.map T).target = T K.target := rfl

end TwoPointKernel

/-- The mass gauge of a similarity-mapped kernel scales by `c ^ 2`. -/
theorem massGauge_similarity
    (t : Point) (c : ℝ)
    (R : Point ≃ₗᵢ[ℝ] Point)
    (K : TwoPointKernel) :
    massGauge (K.map (similarityMap t c R))
      = c ^ 2 * massGauge K := by
  exact pairMass_similarity t c R K.source K.target

/-- A nonzero-scale similarity preserves kernel activity in both directions. -/
theorem active_map_similarity_iff
    (t : Point) (c : ℝ)
    (R : Point ≃ₗᵢ[ℝ] Point)
    (K : TwoPointKernel)
    (hc : c ≠ 0) :
    (K.map (similarityMap t c R)).Active ↔ K.Active := by
  have hc2 : 0 < c ^ 2 := sq_pos_of_ne_zero hc
  constructor
  · intro hK'
    have hmass : 0 < massGauge (K.map (similarityMap t c R)) :=
      (massGauge_pos_iff_active _).2 hK'
    rw [massGauge_similarity] at hmass
    exact (massGauge_pos_iff_active K).1
      ((mul_pos_iff_of_pos_left hc2).mp hmass)
  · intro hK
    have hmass : 0 < massGauge K :=
      (massGauge_pos_iff_active K).2 hK
    have hmass' : 0 < c ^ 2 * massGauge K := mul_pos hc2 hmass
    apply (massGauge_pos_iff_active _).1
    have hmass_map : massGauge (K.map (similarityMap t c R)) = c ^ 2 * massGauge K := massGauge_similarity t c R K
    rw [hmass_map]
    exact hmass'

/-- Natural shell membership is preserved by every affine similarity. -/
theorem onNatShell_similarity
    (t : Point) (c : ℝ)
    (R : Point ≃ₗᵢ[ℝ] Point)
    (K : TwoPointKernel) {n : ℕ} {P : Point}
    (hP : OnNatShell K n P) :
    OnNatShell
      (K.map (similarityMap t c R))
      n
      (similarityMap t c R P) := by
  have hP' : pairMass K.source P = (n : ℝ) * massGauge K := by
    simpa [OnNatShell] using hP
  change pairMass (similarityMap t c R K.source) (similarityMap t c R P) =
    (n : ℝ) * massGauge (K.map (similarityMap t c R))
  rw [pairMass_similarity, massGauge_similarity, hP']
  ring

/-- Normalized mass is invariant under nonzero-scale similarities. -/
theorem normalizedMass_similarity
    (t : Point) (c : ℝ)
    (R : Point ≃ₗᵢ[ℝ] Point)
    (K : TwoPointKernel) (P : Point)
    (hK : K.Active) (hc : c ≠ 0) :
    normalizedMass
      (K.map (similarityMap t c R))
      (similarityMap t c R P)
      = normalizedMass K P := by
  change
    pairMass (similarityMap t c R K.source) (similarityMap t c R P) /
        massGauge (K.map (similarityMap t c R)) =
      pairMass K.source P / massGauge K
  rw [pairMass_similarity, massGauge_similarity]
  field_simp [pow_ne_zero 2 hc, massGauge_ne_zero_of_active K hK]

/-- Squared Euclidean distance obeys the same similarity scaling law as mass. -/
theorem dist_sq_similarity
    (t : Point) (c : ℝ)
    (R : Point ≃ₗᵢ[ℝ] Point)
    (A B : Point) :
    dist (similarityMap t c R A) (similarityMap t c R B) ^ 2 =
      c ^ 2 * dist A B ^ 2 := by
  calc
    dist (similarityMap t c R A) (similarityMap t c R B) ^ 2 =
        pairMass (similarityMap t c R A) (similarityMap t c R B) :=
      (pairMass_eq_dist_sq _ _).symm
    _ = c ^ 2 * pairMass A B := pairMass_similarity t c R A B
    _ = c ^ 2 * dist A B ^ 2 := by rw [pairMass_eq_dist_sq]

end
end DkMath.NumberGeometry
