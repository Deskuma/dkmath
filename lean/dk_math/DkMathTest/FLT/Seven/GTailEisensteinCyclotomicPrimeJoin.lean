/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.GTailEisensteinCyclotomicPrimeJoin

#print "file: DkMathTest.FLT.Seven.GTailEisensteinCyclotomicPrimeJoin"

namespace DkMathTest.FLT.Seven.GTailEisensteinCyclotomicPrimeJoin

open DkMath.FLT.Seven DkMath.Lib.NumberTheory DkMath.NumberTheory.TraceOneQuadratic
open DkMath.FLT.Seven.GTailCommonReceiver DkMath.FLT.Seven.GTailPrimeGrid
open DkMath.FLT.Seven.GTailPrimeJoin

local instance : Fact (Nat.Prime 43) := ⟨by decide⟩
local notation "E" => TraceOneInt (-1)
local notation "R" => SevenCyclotomicDegreeSixInt.Ring
local notation "P37" => eisensteinResidueIdeal (37 : ZMod 43) (by decide)
local notation "K0" => sixRootKernel (11 : ZMod 43) (by decide) (by decide) (by decide) 0
local notation "α" => gtailSevenNormCoord 1166 1857
local notation "F0" => gtailCyclotomicFactor 1858 1165 (0 : Fin 6)

example (e : Fin 2) (x : Carrier) : x = fromCyclotomic (rowRemainder e x) +
    fromEisenstein (rowDifference e) * fromCyclotomic x.im := coordinate_decomposition e x
example (x : Carrier) : x = fromCyclotomic (rowRemainder 1 x) +
    fromEisenstein (rowDifference 1) * fromCyclotomic x.im := coordinate_decomposition 1 x
example (e : Fin 2) : rowDifference e ∈
    eisensteinResidueIdeal (eisenstein43Root e) (eisenstein43Root_relation e) := rowDifference_mem e
example (e : Fin 2) (j : Fin 6) (x : Carrier) (hx : x ∈ M e j) :
    rowRemainder e x ∈ sixRootKernel (11 : ZMod 43) (by decide) (by decide) (by decide) j :=
  rowRemainder_mem e j x hx
example (e : Fin 2) (j : Fin 6) : M e j = A e ⊔ B j :=
  M_eq_map_eisenstein_sup_map_cyclotomic e j
example : M43 = A 0 ⊔ B 0 := M43_eq_sup
example : M 0 0 = M43 := M_zero_zero
example : A 0 < M 0 0 := map_eisenstein_lt_zero_zero
example : B 0 < M 0 0 := map_cyclotomic_lt_zero_zero
example : A 0 < A 0 ⊔ B 0 := by
  rw [← M_eq_map_eisenstein_sup_map_cyclotomic]
  exact map_eisenstein_lt_zero_zero
example : B 0 < A 0 ⊔ B 0 := by
  rw [← M_eq_map_eisenstein_sup_map_cyclotomic]
  exact map_cyclotomic_lt_zero_zero
example (e : Fin 2) (j : Fin 6) : (A e ⊔ B j).IsMaximal := by
  rw [← M_eq_map_eisenstein_sup_map_cyclotomic]
  exact M_isMaximal e j
example : Function.Injective (fun x : Fin 2 × Fin 6 => A x.1 ⊔ B x.2) := by
  intro x y h
  apply M_injective
  simpa only [M_eq_map_eisenstein_sup_map_cyclotomic] using h
example (x y : Fin 2 × Fin 6) (h : x ≠ y) : M x.1 x.2 ≠ M y.1 y.2 :=
  fun he => h (M_injective he)
example (e : Fin 2) (j : Fin 6) : Ideal.comap fromEisenstein (M e j) =
    eisensteinResidueIdeal (eisenstein43Root e) (eisenstein43Root_relation e) := M_comap_eisenstein e j
example (e : Fin 2) (j : Fin 6) : Ideal.comap fromCyclotomic (M e j) =
    sixRootKernel (11 : ZMod 43) (by decide) (by decide) (by decide) j := M_comap_cyclotomic e j
example (e : Fin 2) (j : Fin 6) : (evGrid e j).comp fromEisenstein =
    eisensteinResidueRingHom (eisenstein43Root e) (eisenstein43Root_relation e) :=
  evGrid_comp_eisenstein e j
example (e : Fin 2) (j : Fin 6) : (evGrid e j).comp fromCyclotomic = evR43 j :=
  evGrid_comp_cyclotomic e j
example (e : Fin 2) (j : Fin 6) : fromEisenstein α ∈ M e j ↔ e = 0 := normCoord_mem_iff e j
example (e : Fin 2) (j : Fin 6) : fromCyclotomic F0 ∈ M e j ↔ j = 0 := factor_mem_iff e j
example : fromEisenstein α ≠ fromCyclotomic F0 := by
  intro h
  have hh : ((1857 : ℤ) : R) = 0 := by
    simpa [fromEisenstein, fromCyclotomic, QuadraticAlgebra.algebraMap_eq, gtailSevenNormCoord_eq]
      using congrArg (fun x : Carrier => x.im) h
  have he := congrArg (evR43 0) hh
  exact (by decide : ((1857 : ℤ) : ZMod 43) ≠ 0)
    (by simpa only [map_intCast, map_zero] using he)
example : ¬ Fermat7Equation 1166 1857 1858 := by unfold Fermat7Equation; decide
example : ¬ Nonempty (E →+* R) := not_nonempty_eisenstein_to_seven_cyclotomic
example : ¬ Nonempty (R →+* E) := not_nonempty_seven_cyclotomic_to_eisenstein

-- Native square support stays in its original source ring before transport.
private theorem eroot : gtailSevenResidueRoot 43 1166 1857 = 37 := by
  dsimp [gtailSevenResidueRoot]
  apply (div_eq_iff (by decide : (1857 : ZMod 43) ≠ 0)).mpr
  decide

private theorem rroot : gtailSevenTailRatio 43 1858 1165 = 11 := by
  dsimp [gtailSevenTailRatio]
  apply (div_eq_iff (by decide : (1858 : ZMod 43) ≠ 0)).mpr
  decide

private theorem alpha_mem : α ∈ P37 := by
  have h := gtailSevenNormCoord_mem_residueIdeal (q := 43) (a := 1166) (b := 1857)
    (by decide) (by decide)
  simpa only [eroot] using h

private theorem alpha_square : (α : E) ^ 2 ∈ P37 ^ 2 := by
  have h := gtailSevenNormCoord_split_square_address (q := 43) (a := 1166) (b := 1857)
    (by decide) (by decide) (by decide)
  simpa only [eroot, pow_two] using h.1

private theorem factor_square : F0 ∈ K0 ^ 2 := by
  have h := (gtailCyclotomicFactor_mem_square_iff (q := 43) 1858 1165
    (by decide) (by decide) (by decide) (0 : Fin 6)).mpr (by decide)
  simpa only [rroot, show sixInverseSlot (0 : Fin 6) = 0 from rfl] using h

example : α ∈ P37 := alpha_mem
example : (α : E) ^ 2 ∈ P37 ^ 2 := alpha_square
example : F0 ∈ K0 ^ 2 := factor_square
example (e : Fin 2) (j : Fin 6) (n : Fin 3) (z : E)
    (hz : z ∈ eisensteinResidueIdeal (eisenstein43Root e) (eisenstein43Root_relation e) ^ n.val) :
    fromEisenstein z ∈ A e ^ n.val ∧ fromEisenstein z ∈ M e j ^ n.val :=
  ⟨eisenstein_mem_A_pow e n z hz, eisenstein_mem_M_pow e j n z hz⟩
example (e : Fin 2) (j : Fin 6) (n : Fin 3) (u : R)
    (hu : u ∈ sixRootKernel (11 : ZMod 43) (by decide) (by decide) (by decide) j ^ n.val) :
    fromCyclotomic u ∈ B j ^ n.val ∧ fromCyclotomic u ∈ M e j ^ n.val :=
  ⟨cyclotomic_mem_B_pow j n u hu, cyclotomic_mem_M_pow e j n u hu⟩

private theorem alpha_image : fromEisenstein α ∈ M 0 0 := by
  have h := eisenstein_mem_M_pow 0 0 (1 : Fin 3) α (by simpa [eisenstein43Root] using alpha_mem)
  simpa only [Fin.val_one, pow_one] using h

private theorem alpha_image_square : fromEisenstein ((α : E) ^ 2) ∈ M 0 0 ^ 2 :=
  eisenstein_mem_M_pow 0 0 2 ((α : E) ^ 2) alpha_square

private theorem factor_image_square : fromCyclotomic F0 ∈ M 0 0 ^ 2 :=
  cyclotomic_mem_M_pow 0 0 2 F0 factor_square

example : fromEisenstein α ∈ M 0 0 := alpha_image
example : fromEisenstein ((α : E) ^ 2) ∈ M 0 0 ^ 2 := alpha_image_square
example : fromCyclotomic F0 ∈ M 0 0 ^ 2 := factor_image_square

-- These are lower bounds, with no assertion of exclusion from the next power.
example : fromEisenstein α * fromCyclotomic F0 ∈ M 0 0 ^ 3 := by
  rw [show (3 : ℕ) = 1 + 2 from rfl, pow_add, pow_one]
  exact Ideal.mul_mem_mul alpha_image factor_image_square
example : fromEisenstein ((α : E) ^ 2) * fromCyclotomic F0 ∈ M 0 0 ^ 4 := by
  rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add]
  exact Ideal.mul_mem_mul alpha_image_square factor_image_square

#check Ideal.map_le_iff_le_comap
#check Ideal.mem_map_of_mem
#check Ideal.map_pow
#check Ideal.mul_mem_mul
#check Ideal.pow_mem_pow
#check pow_le_pow_left'
#check QuadraticAlgebra.ext

#print axioms DkMath.FLT.Seven.GTailPrimeJoin.rowRemainder
#print axioms DkMath.FLT.Seven.GTailPrimeJoin.rowDifference
#print axioms DkMath.FLT.Seven.GTailPrimeJoin.coordinate_decomposition
#print axioms DkMath.FLT.Seven.GTailPrimeJoin.rowDifference_mem
#print axioms DkMath.FLT.Seven.GTailPrimeJoin.rowRemainder_mem
#print axioms DkMath.FLT.Seven.GTailPrimeJoin.A
#print axioms DkMath.FLT.Seven.GTailPrimeJoin.B
#print axioms DkMath.FLT.Seven.GTailPrimeJoin.sup_le_M
#print axioms DkMath.FLT.Seven.GTailPrimeJoin.M_le_sup
#print axioms DkMath.FLT.Seven.GTailPrimeJoin.M_eq_map_eisenstein_sup_map_cyclotomic
#print axioms DkMath.FLT.Seven.GTailPrimeJoin.M43_eq_sup
#print axioms DkMath.FLT.Seven.GTailPrimeJoin.eisenstein_mem_A_pow
#print axioms DkMath.FLT.Seven.GTailPrimeJoin.eisenstein_mem_M_pow
#print axioms DkMath.FLT.Seven.GTailPrimeJoin.cyclotomic_mem_B_pow
#print axioms DkMath.FLT.Seven.GTailPrimeJoin.cyclotomic_mem_M_pow

end DkMathTest.FLT.Seven.GTailEisensteinCyclotomicPrimeJoin
