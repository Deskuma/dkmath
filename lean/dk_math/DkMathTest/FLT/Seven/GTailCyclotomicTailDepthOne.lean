/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.GTailCyclotomicTailDepthOne

#print "file: DkMathTest.FLT.Seven.GTailCyclotomicTailDepthOne"

namespace DkMathTest.FLT.Seven.GTailCyclotomicTailDepthOne

open DkMath.FLT.Seven DkMath.Lib.NumberTheory DkMath.CosmicFormula
open SevenCyclotomicDegreeSixInt

local instance : Fact (Nat.Prime 43) := ⟨by decide⟩
local instance : Fact (Nat.Prime 13) := ⟨by decide⟩
local notation "K" => sixRootKernel (11 : ZMod 43) (by decide) (by decide) (by decide)

private theorem ratio11 : gtailSevenTailRatio 43 9 4 = 11 := by
  dsimp [gtailSevenTailRatio]
  apply (div_eq_iff (by decide : (9 : ZMod 43) ≠ 0)).mpr
  decide

private theorem cutoff43 (i : Fin 6) :
    gtailCyclotomicFactor 9 4 i ∈ K (sixInverseSlot i) ∧
    gtailCyclotomicFactor 9 4 i ∉ K (sixInverseSlot i) ^ 2 := by
  have h := gtailCyclotomicFactor_depth_one (q := 43) 9 4
    (by decide) (by decide) (by decide) (by decide) i
  simpa only [ratio11] using h

example (q : ℕ) (hq : q ≠ 0) (x y : SevenCyclotomicDegreeSixInt.Ring)
    (h : (q : SevenCyclotomicDegreeSixInt.Ring) * x = (q : _) * y) : x = y :=
  cyclotomic_natCast_mul_injective q hq h

example (x y : SevenCyclotomicDegreeSixInt.Ring)
    (h : (43 : SevenCyclotomicDegreeSixInt.Ring) * x = 43 * y) : x = y :=
  cyclotomic_natCast_mul_injective 43 (by decide) h

example (j : Fin 6) (n : ℕ) :
    (n : SevenCyclotomicDegreeSixInt.Ring) ∈ cyclotomicScalarIdeal 43 * K j ↔ 43 ^ 2 ∣ n :=
  natCast_mem_scalar_mul_sixRootKernel_iff _ _ _ _ j n
example : ∀ j : Fin 6,
    (1849 : SevenCyclotomicDegreeSixInt.Ring) ∈ cyclotomicScalarIdeal 43 * K j := by
  intro j
  exact (natCast_mem_scalar_mul_sixRootKernel_iff _ _ _ _ j 1849).mpr (by decide)
example : ∀ j : Fin 6,
    (43 : SevenCyclotomicDegreeSixInt.Ring) ∉ cyclotomicScalarIdeal 43 * K j := by
  intro j
  exact fun h => (by decide : ¬ (43 : ℕ) ^ 2 ∣ 43)
    ((natCast_mem_scalar_mul_sixRootKernel_iff _ _ _ _ j 43).mp h)
example : ∀ j : Fin 6,
    (0 : SevenCyclotomicDegreeSixInt.Ring) ∈ cyclotomicScalarIdeal 43 * K j := by
  intro j
  exact Ideal.zero_mem _

example {A ι : Type*} [CommRing A] [Fintype ι] (J : ι → Ideal A) (x : ι → A)
    (hx : ∀ j, x j ∈ J j) (i : ι) (hi : x i ∈ J i ^ 2) :
    (∏ j, x j) ∈ (∏ j, J j) * J i :=
  prod_mem_prod_mul_of_mem_square J x hx i hi
example : (∏ i : Fin 6, K (sixInverseSlot i)) = cyclotomicScalarIdeal 43 :=
  prod_inverseSlot_sixRootKernel_eq_scalarIdeal _ _ _ _

example : GTail 7 1 (4 : ℕ) 9 = 14491387 := by decide
example : (43 : ℕ) ∣ GTail 7 1 (4 : ℕ) 9 := by decide
example : ¬ (43 : ℕ) ^ 2 ∣ GTail 7 1 (4 : ℕ) 9 := by decide
example : (337009 : ℕ) % 43 = 18 := by decide
example : ∀ i : Fin 6, gtailCyclotomicFactor 9 4 i ∈ K (sixInverseSlot i) ∧
    gtailCyclotomicFactor 9 4 i ∉ K (sixInverseSlot i) ^ 2 := cutoff43
example : ∀ i : Fin 6, gtailCyclotomicFactor 9 4 i ∉ K (sixInverseSlot i) ^ 2 :=
  fun i => (cutoff43 i).2
example : ∀ i j : Fin 6, j ≠ sixInverseSlot i → gtailCyclotomicFactor 9 4 i ∉ K j := by
  intro i j h
  have hm := gtailCyclotomicFactor_unique_slot (q := 43) 9 4
    (by decide) (by decide) (by decide) i j
  have hm' : gtailCyclotomicFactor 9 4 i ∈ K j ↔ j = sixInverseSlot i := by
    simpa only [ratio11] using hm
  exact fun hf => h (hm'.mp hf)
example : ∀ i : Fin 6, sixInverseSlot i = ![0, 3, 4, 1, 2, 5] i := fun _ => rfl
example : (∏ i : Fin 6, gtailCyclotomicFactor 9 4 i) =
    ((GTail 7 1 4 9 : ℕ) : SevenCyclotomicDegreeSixInt.Ring) :=
  prod_six_gtailCyclotomicFactor_eq_GTail _ _
example : ((GTail 7 1 4 9 : ℕ) : SevenCyclotomicDegreeSixInt.Ring) ∈
    cyclotomicScalarIdeal 43 := by
  rw [cyclotomicScalarIdeal, Ideal.mem_span_singleton]
  refine ⟨(337009 : SevenCyclotomicDegreeSixInt.Ring), ?_⟩
  norm_num [GTail, Finset.sum_range_succ, Nat.choose]
example : ∀ j : Fin 6,
    ((GTail 7 1 4 9 : ℕ) : SevenCyclotomicDegreeSixInt.Ring) ∉
      cyclotomicScalarIdeal 43 * K j := by
  intro j
  exact fun h => (by decide : ¬ (43 : ℕ) ^ 2 ∣ GTail 7 1 (4 : ℕ) 9)
    ((natCast_mem_scalar_mul_sixRootKernel_iff _ _ _ _ j _).mp h)

-- A valid Tail input with square support: the new cutoff's scalar guard fails.
example : GTail 7 1 (1165 : ℕ) 9 = 2638461449052811747 := by decide
example : ¬ (43 : ℕ) ∣ 9 ∧ ¬ (43 : ℕ) ∣ 1165 ∧
    (43 : ℕ) ∣ GTail 7 1 (1165 : ℕ) 9 ∧ (43 : ℕ) ^ 2 ∣ GTail 7 1 (1165 : ℕ) 9 := by
  decide
example : ¬ (¬ (43 : ℕ) ^ 2 ∣ GTail 7 1 (1165 : ℕ) 9) := by decide
example : gtailSevenTailRatio 43 9 1165 = 11 := by
  dsimp [gtailSevenTailRatio]
  apply (div_eq_iff (by decide : (9 : ZMod 43) ≠ 0)).mpr
  decide

-- The unconditional source product survives excluded local-depth inputs.
example (c : ℕ) : (∏ i : Fin 6, gtailCyclotomicFactor c 0 i) =
    ((GTail 7 1 0 c : ℕ) : SevenCyclotomicDegreeSixInt.Ring) :=
  prod_six_gtailCyclotomicFactor_eq_GTail _ _
example : (43 : ℕ) ∣ 0 := by decide
example : (∏ i : Fin 6, gtailCyclotomicFactor 0 1 i) = 1 := by
  rw [prod_six_gtailCyclotomicFactor_eq_GTail]
  norm_num [GTail, Finset.sum_range_succ, Nat.choose]
example : (13 : ℕ) ∣ 13 ∧ ¬ (13 : ℕ) ∣ GTail 7 1 13 30 := by decide
example : gtailSevenTailRatio 13 30 13 = 1 := by
  dsimp [gtailSevenTailRatio]
  apply (div_eq_iff (by decide : (30 : ZMod 13) ≠ 0)).mpr
  decide
example : ¬ ∃ r : ZMod 7, r ^ 7 = 1 ∧ r ≠ 1 := by decide
example : ¬ Fermat7Equation 5 8 9 := by
  unfold Fermat7Equation
  decide

#print axioms DkMath.FLT.Seven.cyclotomic_natCast_mul_injective
#print axioms DkMath.FLT.Seven.natCast_mem_scalar_mul_sixRootKernel_iff
#print axioms DkMath.FLT.Seven.prod_mem_prod_mul_of_mem_square
#print axioms DkMath.FLT.Seven.prod_inverseSlot_sixRootKernel_eq_scalarIdeal
#print axioms DkMath.FLT.Seven.GTail_mem_scalar_mul_kernel_of_factor_mem_square
#print axioms DkMath.FLT.Seven.gtailCyclotomicFactor_not_mem_square
#print axioms DkMath.FLT.Seven.gtailCyclotomicFactor_depth_one

end DkMathTest.FLT.Seven.GTailCyclotomicTailDepthOne
