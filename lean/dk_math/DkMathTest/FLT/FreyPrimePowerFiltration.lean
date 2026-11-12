/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyPrimePowerFiltration

namespace DkMathTest.FLT.FreyPrimePowerFiltration

open DkMath.Lib.Algebra DkMath.Lib.NumberTheory
open EllipticNodalReductionKernel

-- Actual residue characteristic 5, a node at (0,0), and a nondegenerate tangent cone.
private def nodal : WeierstrassCurve (ZMod 5) := ⟨0, 1, 0, 0, 0⟩
private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private theorem node_equation : nodal.toAffine.Equation 0 0 := by
  norm_num [WeierstrassCurve.Affine.equation_iff, nodal]

private theorem node_singular : ¬ nodal.toAffine.Nonsingular 0 0 := by
  simp [WeierstrassCurve.Affine.nonsingular_zero, nodal]

private theorem two_nonsingular : nodal.toAffine.Nonsingular (-1) 0 := by
  norm_num [WeierstrassCurve.Affine.nonsingular_iff', WeierstrassCurve.Affine.equation_iff, nodal]

example (m : ℕ) (P : nodal.toAffine.Point) (hP : 5 ^ m • P = 0) : P = 0 :=
  eq_zero_of_residue_characteristic_prime_power nodal 0 0 node_equation node_singular (by decide) m P hP

private def twoPoint : nodal.toAffine.Point := .some (-1) 0 two_nonsingular

example : 2 • twoPoint = 0 := by
  rw [two_nsmul]
  exact WeierstrassCurve.Affine.Point.add_self_of_Y_eq (by decide)

-- The group is not trivial: its concrete nonzero two-torsion point is not killed by 5^m.
example (m : ℕ) : 5 ^ m • twoPoint ≠ 0 := by
  intro h
  have hz := eq_zero_of_residue_characteristic_prime_power nodal 0 0
    node_equation node_singular (by decide) m twoPoint h
  exact WeierstrassCurve.Affine.Point.some_ne_zero two_nonsingular hz

-- Absorption alone does not imply the lower cardinality bound: the identity
-- action and the zero absorbing subgroup fail it. Nontrivial inertia is essential.
example : Nat.card (AbsorbingTorsionFiltration.stage 3 1 (⊥ : AddSubgroup (ZMod 9))) = 1 := by
  rw [AbsorbingTorsionFiltration.stage, inf_bot_eq, AddSubgroup.card_bot]

example : (∀ x : ZMod 9, AddMonoidHom.id (ZMod 9) x - x ∈ (⊥ : AddSubgroup (ZMod 9))) ∧
    ¬ (⊤ : AddSubgroup (ZMod 9)) ≤ ⊥ := by
  constructor
  · intro x
    simp
  · intro h
    have hz : (1 : ZMod 9) = 0 := (AddSubgroup.mem_bot).mp (h (AddSubgroup.mem_top 1))
    exact (by decide : (1 : ZMod 9) ≠ 0) hz

open DkMath.FLT.Frey.Source

#check primePowerReductionFiltration_cyclic_and_card
#check cyclic_tower_eq_primePowerReductionFiltration
#check residual_cofixed_cyclic_extension_locally_split_at_p
#check residual_cofixed_cyclic_tower_inertia_frobenius_impossible

#print axioms CyclotomicInertia.exists_inertia_cyclotomic_eq
#print axioms AbsorbingTorsionFiltration.cyclic_and_card
#print axioms AbsorbingTorsionFiltration.le_of_nontrivial_socle
#print axioms eq_zero_of_residue_characteristic_prime_power
#print axioms mem_kernel_of_smooth_prime_power_torsion
#print axioms pole_of_smooth_prime_power_torsion_of_model
#print axioms prime_power_reductionKernel_absorbs_at_p
#print axioms valuationReductionKernel_stable
#print axioms residual_cofixed_inertia_moves_base_at_p
#print axioms prime_reductionKernel_card_le
#print axioms primePowerReductionFiltration_cyclic_and_card
#print axioms cyclic_tower_eq_primePowerReductionFiltration
#print axioms residual_cofixed_cyclic_extension_locally_split_at_p
#print axioms prime_power_pointAction_sub_mem_cyclic_tower_at_p
#print axioms residual_cofixed_cyclic_tower_inertia_frobenius_impossible

end DkMathTest.FLT.FreyPrimePowerFiltration
