/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.ABC.GNExcessCubicComplementPell

/-!
# Necessary incidence strength for the cubic realized modulus moment

This module records an exact obstruction theorem.  It does not bound the
realized modulus moment: it shows what a linear bound would force on a block
of points whose entire quadratic value is repeated.
-/

namespace DkMath.ABC

open DkMath.CosmicFormulaBinom DkMath.NumberTheory

/-- A full repeated part at a point is a realized large modulus.  This is a
safe converse for the actual full repeated part, not for an arbitrary
squareful divisor. -/
theorem mem_GNExcessCubicRealizedLargeModulusSpace_of_fullRepeatedPart
    {X a M : ℕ} (ha : a ∈ Finset.Icc 0 X)
    (he : GNNonExceptionalRepeatedPart 3 a 1 = M)
    (hlarge : X + 1 < M) :
    M ∈ GNExcessCubicRealizedLargeModulusSpace X := by
  have hm : GNExcessJointDepthModulus
      (GNNonExceptionalIntervalPrimeFamily 3 1 X)
      (GNExcessDepthProfileAt
        (GNNonExceptionalIntervalPrimeFamily 3 1 X) 3 1 a) = M := by
    rw [GNExcessJointDepthModulus_target_eq_repeatedPart
      Nat.prime_three ha (by simp), he]
  apply mem_GNExcessCubicRealizedLargeModulusSpace_iff.mpr
  refine ⟨_, ?_, hm⟩
  apply (mem_realizedLargeProfileSpace_iff_realized_and_large
    (by decide : 0 < (1 : ℕ))).mpr
  exact ⟨point_profile_mem_realizedProfileSpace ha, hm ▸ hlarge⟩

/-- The canonical quadratic is injective on natural numbers. -/
theorem cubicQuadratic_injective :
    Function.Injective (fun a : ℕ => a ^ 2 + 3 * a + 3) := by
  intro a b h
  rcases lt_trichotomy a b with hab | he | hba
  · nlinarith
  · exact he
  · nlinarith

/-- A dyadic block of points whose full quadratic values are repeated forces
an exact lower bound on the realized modulus `3/8` moment.  This is a
necessary-condition theorem, not an incidence estimate. -/
theorem cubicSquarefullBlock_card_mul_weight_le_realizedModulusMoment
    {X : ℕ} (hX : 0 < X) (A : Finset ℕ)
    (hA : ∀ a ∈ A, X ≤ a ∧ a ≤ 2 * X ∧
      GNNonExceptionalRepeatedPart 3 a 1 = a ^ 2 + 3 * a + 3) :
    (A.card : ℝ) * ((X : ℝ) ^ 2) ^ (3 / 8 : ℝ) ≤
      ∑ M ∈ GNExcessCubicRealizedLargeModulusSpace (2 * X),
        (M : ℝ) ^ (3 / 8 : ℝ) := by
  classical
  let f : ℕ → ℕ := fun a => a ^ 2 + 3 * a + 3
  have hsub : A.image f ⊆
      GNExcessCubicRealizedLargeModulusSpace (2 * X) := by
    intro M hM
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hM
    have hh := hA a ha
    exact mem_GNExcessCubicRealizedLargeModulusSpace_of_fullRepeatedPart
      (Finset.mem_Icc.mpr ⟨by omega, hh.2.1⟩) hh.2.2 (by
        dsimp [f]
        nlinarith)
  calc
    _ = ∑ _a ∈ A, ((X : ℝ) ^ 2) ^ (3 / 8 : ℝ) := by simp
    _ ≤ ∑ a ∈ A, (f a : ℝ) ^ (3 / 8 : ℝ) := by
      apply Finset.sum_le_sum
      intro a ha
      apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
      have hsq : X ^ 2 ≤ f a := by
        have hh := hA a ha
        dsimp [f]
        nlinarith
      exact_mod_cast hsq
    _ = ∑ M ∈ A.image f, (M : ℝ) ^ (3 / 8 : ℝ) := by
      symm
      apply Finset.sum_image
      intro a ha b hb he
      exact cubicQuadratic_injective he
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun M _ _ => Real.rpow_nonneg (Nat.cast_nonneg M) _)

end DkMath.ABC
