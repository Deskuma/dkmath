/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Kummer.ThreeGNDescent

#print "file: DkMathTest.FLT.Kummer.ThreeGNDescent"

open scoped NumberField
open DkMath.FLT.Three DkMath.FLT.Kummer
open DkMath.NumberTheory.TraceOneQuadratic

-- The sixth-root coordinate convention is material: ζ−1 and λ_E are different.
example : eisensteinZeta ^ 2 - 1 = -eisensteinRamifier := eisensteinZeta_sq_sub_one

example : eisensteinZeta - 1 ≠ eisensteinRamifier := by
  decide +kernel

example : -((2 : EisensteinInt) + eisensteinZeta ^ 2 * (-5)) =
    eisensteinCoord (-2) (-5) := eisenstein_second_phase 2 (-5)

section Equivalence
variable {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {3} ℚ K] {ζ : K} (hζ : IsPrimitiveRoot ζ 3)

example : DkMath.Lib.NumberTheory.eisensteinCyclotomicEquiv hζ eisensteinTau =
    1 + hζ.toInteger := by
  simp [eisensteinTau, tau]

example : (DkMath.Lib.NumberTheory.eisensteinCyclotomicEquiv hζ).symm hζ.toInteger =
    eisensteinZeta := by
  apply (DkMath.Lib.NumberTheory.eisensteinCyclotomicEquiv hζ).injective
  rw [RingEquiv.apply_symm_apply, eisensteinCyclotomicEquiv_zeta]

-- Test a nonconstant element and its cube, independently of a hypothetical FLT solution.
example : (DkMath.Lib.NumberTheory.eisensteinCyclotomicEquiv hζ).symm
    ((DkMath.Lib.NumberTheory.eisensteinCyclotomicEquiv hζ) (eisensteinCoord 2 (-5)) ^ 3) =
      eisensteinCoord 2 (-5) ^ 3 := by
  rw [← map_pow, RingEquiv.symm_apply_apply]

-- Units are transported in the unit group itself.
example (u : EisensteinIntˣ) :
    Units.map (DkMath.Lib.NumberTheory.eisensteinCyclotomicEquiv hζ).symm.toMonoidHom
      (Units.map (DkMath.Lib.NumberTheory.eisensteinCyclotomicEquiv hζ).toMonoidHom u) = u := by
  apply Units.ext
  exact (DkMath.Lib.NumberTheory.eisensteinCyclotomicEquiv hζ).symm_apply_apply _

example : Fintype.card (ClassGroup (𝓞 K)) = 1 := cubic_classGroup_card_eq_one hζ

-- The result concerns the supplied beta and retains its old arithmetic data.
example {a b c : ℕ} (q : EisensteinRamifierStrippedPacket a b c) :
    ∃ θ : EisensteinInt, q.beta = θ ^ 3 ∧
      q.beta.snd = 3 * (q.powerSplit.A : ℤ) ^ 3 ∧
      norm q.beta = (q.powerSplit.B : ℤ) ^ 3 ∧ ¬ 3 ∣ q.powerSplit.B := by
  obtain ⟨θ, hθ⟩ := exists_cube_eq_stripped_beta hζ q
  exact ⟨θ, hθ, q.beta_snd, q.beta_norm, q.powerSplit.three_not_dvd_B⟩

example {a b c : ℕ} (source : PrimitiveCubicPack a b c) :
    ∃ x y z : ℕ, PrimitiveCubicPack x y z ∧ x * y * z < a * b * c :=
  exists_smaller_primitiveCubicPack_via_GN hζ source
end Equivalence

-- No number field, class-number, or unit-power premise remains at the public endpoint.
example (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a ^ 3 + b ^ 3 ≠ c ^ 3 := fermatThree_no_positive_solution_via_GN a b c ha hb hc

#print axioms DkMath.Lib.NumberTheory.eisensteinCyclotomicEquiv
#print axioms DkMath.FLT.Kummer.exists_cube_eq_stripped_beta
#print axioms DkMath.FLT.Kummer.fermatThree_no_positive_solution_via_GN

run_cmd do
  for name in #[
    ``DkMath.Lib.NumberTheory.eisensteinEval,
    ``DkMath.Lib.NumberTheory.one_add_cubic_root_sq,
    ``DkMath.Lib.NumberTheory.eisensteinToCyclotomic,
    ``DkMath.Lib.NumberTheory.cyclotomicToEisenstein,
    ``DkMath.Lib.NumberTheory.cyclotomicToEisenstein_root,
    ``DkMath.Lib.NumberTheory.eisensteinCyclotomicEquiv,
    ``DkMath.Lib.NumberTheory.eisensteinCyclotomicEquiv_apply,
    ``eisensteinZeta, ``eisensteinZeta_sq, ``eisensteinZeta_sq_sub_one,
    ``eisenstein_second_phase, ``eisensteinCyclotomicEquiv_zeta,
    ``cubic_classGroup_card_eq_one,
    ``exists_eisenstein_factor_eq_ramifier_mul_cube,
    ``signedThreeAdicPacket_coordinates_coprime, ``signedThreeAdicPacket_cubic_equation,
    ``exists_cube_eq_stripped_beta, ``eisensteinExactCubePacket_of_stripped_cube,
    ``gnEisensteinDescentFactorSource, ``gnPrimitiveCubicStrictDescent,
    ``exists_smaller_primitiveCubicPack_via_GN, ``primitiveCubicPack_false_via_GN,
    ``fermatThree_no_positive_solution_via_GN_in, ``fermatThree_no_positive_solution_via_GN,
    ``nonempty_primitiveCubicStrictDescent_of_factors, ``primitiveCubicStrictDescent_of_factors] do
    for ax in ← Lean.collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {name}"
