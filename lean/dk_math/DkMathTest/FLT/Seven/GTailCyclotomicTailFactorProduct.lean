/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.GTailCyclotomicTailFactorProduct

#print "file: DkMathTest.FLT.Seven.GTailCyclotomicTailFactorProduct"

namespace DkMathTest.FLT.Seven.GTailCyclotomicTailFactorProduct

open DkMath.FLT.Seven DkMath.Lib.NumberTheory DkMath.CosmicFormula
open SevenCyclotomicDegreeSixInt

local instance : Fact (Nat.Prime 43) := ⟨by decide⟩
local instance : Fact (Nat.Prime 13) := ⟨by decide⟩
local notation "K" => sixRootKernel (11 : ZMod 43) (by decide) (by decide) (by decide)

private theorem ratio11 : gtailSevenTailRatio 43 9 4 = 11 := by
  dsimp [gtailSevenTailRatio]
  apply (div_eq_iff (by decide : (9 : ZMod 43) ≠ 0)).mpr
  decide

private theorem incidence43 (i j : Fin 6) :
    gtailCyclotomicFactor 9 4 i ∈ K j ↔ j = sixInverseSlot i := by
  have h := gtailCyclotomicFactor_unique_slot (q := 43) 9 4
    (by decide) (by decide) (by decide) i j
  simpa only [ratio11] using h

-- Universal source identities, instantiated without any residue hypotheses.
example (X Y : SevenCyclotomicDegreeSixInt.Ring) :
    (∏ i : Fin 6, (X - zeta ^ (i.val + 1) * Y)) =
      ∑ j : Fin 7, X ^ (6 - j.val) * Y ^ j.val :=
  prod_six_zeta_factors_eq_shell X Y

example (c g : ℕ) : (∏ i : Fin 6, gtailCyclotomicFactor c g i) =
    ((GTail 7 1 g c : ℕ) : SevenCyclotomicDegreeSixInt.Ring) :=
  prod_six_gtailCyclotomicFactor_eq_GTail c g

example : GTail 7 1 (4 : ℕ) 9 = 14491387 := by decide
example : (43 : ℕ) ∣ GTail 7 1 (4 : ℕ) 9 := by decide
example : (∏ i : Fin 6, gtailCyclotomicFactor 9 4 i) =
    (14491387 : SevenCyclotomicDegreeSixInt.Ring) := by
  rw [prod_six_gtailCyclotomicFactor_eq_GTail]
  congr 1

example : gtailCyclotomicFactor 9 4 0 = gtailCyclotomicLinearFactor 9 4 :=
  gtailCyclotomicFactor_zero _ _
example : gtailCyclotomicFactor 9 4 0 = 13 - 9 * zeta := by
  simp [gtailCyclotomicFactor]
  ring
example : gtailCyclotomicFactor 9 4 0 ∈ K 0 := (incidence43 _ _).mpr rfl
example : gtailCyclotomicFactor 9 4 0 ∉ K 1 := by
  rw [incidence43]
  decide

example : ∀ i : Fin 6, sixInverseSlot i = ![0, 3, 4, 1, 2, 5] i := fun _ => rfl
example : Function.Involutive sixInverseSlot := sixInverseSlot_involutive
example : ∀ i j : Fin 6, gtailCyclotomicFactor 9 4 i ∈ K j ↔
    j = ![0, 3, 4, 1, 2, 5] i := incidence43
example : ∀ i : Fin 6, ∃! j : Fin 6, gtailCyclotomicFactor 9 4 i ∈ K j := by
  intro i
  exact ⟨sixInverseSlot i, (incidence43 _ _).mpr rfl,
    fun j h => (incidence43 _ _).mp h⟩
example : ∀ i j : Fin 6, j ≠ sixInverseSlot i → gtailCyclotomicFactor 9 4 i ∉ K j := by
  intro i j h
  exact fun hm => h ((incidence43 _ _).mp hm)

-- Every entry is an actual RingHom evaluation, including the nonzero crosses.
example : ∀ i j : Fin 6,
    evalCyclotomicFromSeventhRoot (sixSlotRoot (11 : ZMod 43) j)
      (sixSlotRoot_ne_zero _ (by decide) j) (sixSlotRoot_pow_seven _ (by decide) j)
      (sixSlotRoot_ne_one _ (by decide) (by decide) j) (gtailCyclotomicFactor 9 4 i) =
    (![![0, 42, 31, 39, 41, 20], ![42, 39, 20, 0, 31, 41],
      ![31, 20, 42, 41, 0, 39], ![39, 0, 41, 42, 20, 31],
      ![41, 31, 0, 20, 39, 42], ![20, 41, 39, 31, 42, 0]] : Fin 6 → Fin 6 → ZMod 43) i j := by
  intro i j
  rw [evalCyclotomic_gtailFactor]
  revert i j
  decide

example : ((GTail 7 1 4 9 : ℕ) : SevenCyclotomicDegreeSixInt.Ring) ∈
    cyclotomicScalarIdeal 43 := by
  rw [cyclotomicScalarIdeal, Ideal.mem_span_singleton]
  exact ⟨(337009 : SevenCyclotomicDegreeSixInt.Ring), by norm_num [GTail,
    Finset.sum_range_succ, Nat.choose]⟩
example : ∀ j : Fin 6,
    ((GTail 7 1 4 9 : ℕ) : SevenCyclotomicDegreeSixInt.Ring) ∈ K j := by
  intro j
  rw [mem_sixRootKernel_iff]
  simp only [map_natCast]
  exact (ZMod.natCast_eq_zero_iff _ _).mpr (by decide)
example : gtailCyclotomicFactor 9 4 0 ∉ cyclotomicScalarIdeal 43 := by
  rw [← iInf_sixRootKernel_eq_scalarIdeal (11 : ZMod 43) (by decide) (by decide) (by decide)]
  intro h
  have h1 := Ideal.mem_iInf.mp h (1 : Fin 6)
  exact (by decide : (1 : Fin 6) ≠ sixInverseSlot 0) ((incidence43 _ _).mp h1)
example : (∏ i : Fin 6, K i) = cyclotomicScalarIdeal 43 :=
  prod_sixRootKernel_eq_scalarIdeal _ _ _ _
example : ¬ Fermat7Equation 5 8 9 := by
  unfold Fermat7Equation
  decide

-- Zero gap and endpoints are part of the unconditional element theorem.
example (c : ℕ) : GTail 7 1 (0 : ℕ) c = 7 * c ^ 6 := by
  rw [GTail_seven_one_eq_homogeneous_sum]
  simp [Fin.sum_univ_succ]
  ring
example (c : ℕ) : (∏ i : Fin 6, gtailCyclotomicFactor c 0 i) =
    (7 * c ^ 6 : ℕ) := by
  rw [prod_six_gtailCyclotomicFactor_eq_GTail]
  congr 1
  rw [GTail_seven_one_eq_homogeneous_sum]
  simp [Fin.sum_univ_succ]
  ring
example : (∏ i : Fin 6, gtailCyclotomicFactor 0 1 i) = 1 := by
  rw [prod_six_gtailCyclotomicFactor_eq_GTail]
  norm_num [GTail, Finset.sum_range_succ, Nat.choose]
example : (∏ i : Fin 6, gtailCyclotomicFactor 1 0 i) = 7 := by
  rw [prod_six_gtailCyclotomicFactor_eq_GTail]
  norm_num [GTail, Finset.sum_range_succ, Nat.choose]
example : ∀ i : Fin 6, gtailCyclotomicFactor 0 0 i = 0 := by
  intro i
  simp [gtailCyclotomicFactor]
example : (∏ i : Fin 6, gtailCyclotomicFactor 0 0 i) = 0 := by
  rw [prod_six_gtailCyclotomicFactor_eq_GTail]
  norm_num [GTail, Finset.sum_range_succ, Nat.choose]
example : ∀ i j : Fin 6, gtailCyclotomicFactor 0 0 i ∈ K j := by
  intro i j
  simp [gtailCyclotomicFactor]
example : gtailSevenTailRatio 13 30 13 = 1 := by
  dsimp [gtailSevenTailRatio]
  apply (div_eq_iff (by decide : (30 : ZMod 13) ≠ 0)).mpr
  decide
example : (13 : ℕ) ∣ 13 ∧ ¬ (13 : ℕ) ∣ GTail 7 1 13 30 := by decide
example : ¬ ∃ r : ZMod 7, r ^ 7 = 1 ∧ r ≠ 1 := by decide
example : (∏ i : Fin 6, gtailCyclotomicFactor 7 1 i) =
    ((GTail 7 1 1 7 : ℕ) : SevenCyclotomicDegreeSixInt.Ring) :=
  prod_six_gtailCyclotomicFactor_eq_GTail _ _

#print axioms DkMath.FLT.Seven.gtailCyclotomicFactor
#print axioms DkMath.FLT.Seven.gtailCyclotomicFactor_zero
#print axioms DkMath.FLT.Seven.zeta_geom_sum
#print axioms DkMath.FLT.Seven.prod_six_zeta_factors_eq_shell
#print axioms DkMath.FLT.Seven.GTail_seven_one_eq_homogeneous_sum
#print axioms DkMath.FLT.Seven.prod_six_gtailCyclotomicFactor_eq_GTail
#print axioms DkMath.FLT.Seven.evalCyclotomic_gtailFactor
#print axioms DkMath.FLT.Seven.sixInverseSlot
#print axioms DkMath.FLT.Seven.sixInverseSlot_involutive
#print axioms DkMath.FLT.Seven.six_inverse_exponents
#print axioms DkMath.FLT.Seven.gtailCyclotomicFactor_mem_sixRootKernel_iff
#print axioms DkMath.FLT.Seven.gtailCyclotomicFactor_unique_slot

end DkMathTest.FLT.Seven.GTailCyclotomicTailFactorProduct
