/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberGeometry.Transport

namespace DkMath.NumberGeometry
noncomputable section

/-!
# Square-mass level sets and shared-point transport

`MassLevelSet` is the primitive point-centered square-mass boundary.  This
module records its transport and incidence behavior without making circles,
intersection existence, or point uniqueness primitive claims.
-/

/-- The point-centered level set of a prescribed square mass. -/
def MassLevelSet (A : Point) (rho : ℝ) : Set Point :=
  {P | pairMass A P = rho}

/-- Membership in a mass level set is its defining square-mass equation. -/
@[simp]
theorem mem_massLevelSet (A P : Point) (rho : ℝ) :
    P ∈ MassLevelSet A rho ↔ pairMass A P = rho := by
  rfl

/-- The zero-mass level set is the singleton containing its center. -/
@[simp]
theorem massLevelSet_zero (A : Point) :
    MassLevelSet A 0 = {A} := by
  ext P
  change pairMass A P = 0 ↔ P = A
  simpa [eq_comm] using (pairMass_eq_zero_iff A P)

/-- A natural shell is the mass level at its gauge-scaled natural index. -/
theorem onNatShell_iff_mem_massLevelSet
    (K : TwoPointKernel) (n : ℕ) (P : Point) :
    OnNatShell K n P ↔
      P ∈ MassLevelSet K.source ((n : ℝ) * massGauge K) := by
  rfl

/-- A transported point lies on the correspondingly scaled mass level. -/
theorem mem_massLevelSet_similarity
    (t : Point) (c : ℝ)
    (R : Point ≃ₗᵢ[ℝ] Point)
    {A P : Point} {rho : ℝ}
    (hP : P ∈ MassLevelSet A rho) :
    similarityMap t c R P ∈
      MassLevelSet
        (similarityMap t c R A)
        (c ^ 2 * rho) := by
  change pairMass A P = rho at hP
  change pairMass (similarityMap t c R A) (similarityMap t c R P) =
    c ^ 2 * rho
  rw [pairMass_similarity, hP]

/-- The image of a mass level set is contained in the scaled target level. -/
theorem image_massLevelSet_similarity_subset
    (t : Point) (c : ℝ)
    (R : Point ≃ₗᵢ[ℝ] Point)
    (A : Point) (rho : ℝ) :
    similarityMap t c R '' MassLevelSet A rho ⊆
      MassLevelSet
        (similarityMap t c R A)
        (c ^ 2 * rho) := by
  rintro Q ⟨P, hP, rfl⟩
  exact mem_massLevelSet_similarity t c R hP

/-- A nonzero-scale affine similarity is injective. -/
theorem similarityMap_injective
    (t : Point) (c : ℝ)
    (R : Point ≃ₗᵢ[ℝ] Point)
    (hc : c ≠ 0) :
    Function.Injective (similarityMap t c R) := by
  intro A B hAB
  have hmass :
      pairMass (similarityMap t c R A) (similarityMap t c R B) = 0 := by
    rw [hAB]
    simp
  rw [pairMass_similarity] at hmass
  have hpair : pairMass A B = 0 := by
    exact (mul_eq_zero.mp hmass).resolve_left (pow_ne_zero 2 hc)
  exact (pairMass_eq_zero_iff A B).mp hpair

/-- A nonzero-scale affine similarity is surjective on the point space. -/
theorem similarityMap_surjective
    (t : Point) (c : ℝ)
    (R : Point ≃ₗᵢ[ℝ] Point)
    (hc : c ≠ 0) :
    Function.Surjective (similarityMap t c R) := by
  intro Q
  refine ⟨c⁻¹ • R.symm (Q - t), ?_⟩
  simp [similarityMap, sub_eq_add_neg, smul_smul, hc]

/-- A mapped point lies on the scaled level exactly when its source lies on the original level. -/
theorem mem_massLevelSet_similarity_iff
    (t : Point) (c : ℝ)
    (R : Point ≃ₗᵢ[ℝ] Point)
    {A P : Point} {rho : ℝ}
    (hc : c ≠ 0) :
    similarityMap t c R P ∈
        MassLevelSet
          (similarityMap t c R A)
          (c ^ 2 * rho) ↔
      P ∈ MassLevelSet A rho := by
  change pairMass (similarityMap t c R A) (similarityMap t c R P) =
      c ^ 2 * rho ↔ pairMass A P = rho
  rw [pairMass_similarity]
  constructor
  · intro h
    exact mul_left_cancel₀ (pow_ne_zero 2 hc) h
  · intro h
    rw [h]

/-- For nonzero scale, a similarity maps a mass level set exactly onto its scaled level set. -/
theorem image_massLevelSet_similarity
    (t : Point) (c : ℝ)
    (R : Point ≃ₗᵢ[ℝ] Point)
    (A : Point) (rho : ℝ) (hc : c ≠ 0) :
    similarityMap t c R '' MassLevelSet A rho =
      MassLevelSet
        (similarityMap t c R A)
        (c ^ 2 * rho) := by
  apply Set.Subset.antisymm
  · exact image_massLevelSet_similarity_subset t c R A rho
  · intro Q hQ
    obtain ⟨P, rfl⟩ := similarityMap_surjective t c R hc Q
    exact ⟨P, (mem_massLevelSet_similarity_iff t c R hc).mp hQ, rfl⟩

/-- A shared point satisfies two set-membership constraints simultaneously. -/
def SharedPoint (S U : Set Point) (P : Point) : Prop :=
  P ∈ S ∧ P ∈ U

/-- Shared-point membership is equivalent to membership in the set intersection. -/
theorem sharedPoint_iff_mem_inter
    (S U : Set Point) (P : Point) :
    SharedPoint S U P ↔ P ∈ S ∩ U := by
  rfl

/-- A shared point of two mass levels transports to a shared point of both scaled levels. -/
theorem sharedPoint_massLevelSet_similarity
    (t : Point) (c : ℝ)
    (R : Point ≃ₗᵢ[ℝ] Point)
    {A B : Point} {rho sigma : ℝ} {P : Point}
    (hP :
      SharedPoint
        (MassLevelSet A rho)
        (MassLevelSet B sigma)
        P) :
    SharedPoint
      (MassLevelSet (similarityMap t c R A) (c ^ 2 * rho))
      (MassLevelSet (similarityMap t c R B) (c ^ 2 * sigma))
      (similarityMap t c R P) := by
  exact ⟨mem_massLevelSet_similarity t c R hP.1,
    mem_massLevelSet_similarity t c R hP.2⟩

/-- A nonzero-scale similarity preserves intersections under set image. -/
theorem image_inter_similarity
    (t : Point) (c : ℝ)
    (R : Point ≃ₗᵢ[ℝ] Point)
    (hc : c ≠ 0) (S U : Set Point) :
    similarityMap t c R '' (S ∩ U) =
      (similarityMap t c R '' S) ∩
        (similarityMap t c R '' U) := by
  exact Set.image_inter (similarityMap_injective t c R hc)

end
end DkMath.NumberGeometry
