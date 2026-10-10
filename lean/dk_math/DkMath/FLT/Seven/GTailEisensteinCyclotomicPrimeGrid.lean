/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.GTailEisensteinCyclotomicCommonReceiver

#print "file: DkMath.FLT.Seven.GTailEisensteinCyclotomicPrimeGrid"

/-!
# Twelve q43 prime addresses in the common receiver

Rows and columns contract to separately typed source ideals. This finite grid
also detects proper extensions and orthogonal support of the native witnesses;
it does not classify the spectrum or transport ideal-adic depths.
-/

namespace DkMath.FLT.Seven.GTailPrimeGrid

open DkMath.NumberTheory.TraceOneQuadratic DkMath.Lib.NumberTheory GTailCommonReceiver

local instance : Fact (Nat.Prime 43) := ⟨by decide⟩

/-- The two independent quadratic residue choices. -/
def eisenstein43Root : Fin 2 → ZMod 43 := ![37, 7]

/-- The existing six nonidentity seventh-root powers. -/
def seven43Root (j : Fin 6) : ZMod 43 := sixSlotRoot 11 j

/-- Both row choices satisfy the actual quadratic relation. -/
theorem eisenstein43Root_relation (e : Fin 2) :
    eisenstein43Root e ^ 2 - eisenstein43Root e + 1 = 0 := by
  fin_cases e <;> decide

/-- The two quadratic residue choices are distinct. -/
theorem eisenstein43Root_injective : Function.Injective eisenstein43Root := by
  intro e f h
  fin_cases e <;> fin_cases f <;> first | rfl | contradiction

/-- Each column retains the seventh-power relation. -/
theorem seven43Root_pow_seven (j : Fin 6) : seven43Root j ^ 7 = 1 :=
  sixSlotRoot_pow_seven 11 (by decide) j

/-- Each column root is nonzero. -/
theorem seven43Root_ne_zero (j : Fin 6) : seven43Root j ≠ 0 :=
  sixSlotRoot_ne_zero 11 (by decide) j

/-- Each column root is nonidentity. -/
theorem seven43Root_ne_one (j : Fin 6) : seven43Root j ≠ 1 :=
  sixSlotRoot_ne_one 11 (by decide) (by decide) j

/-- The existing order-seven proof distinguishes all columns. -/
theorem seven43Root_injective : Function.Injective seven43Root :=
  sixSlotRoot_injective 11 (by decide) (by decide)

/-- The actual coefficient-ring evaluation at a column root. -/
def evR43 (j : Fin 6) : SevenCyclotomicDegreeSixInt.Ring →+* ZMod 43 :=
  evalCyclotomicFromSeventhRoot (seven43Root j) (seven43Root_ne_zero j)
    (seven43Root_pow_seven j) (seven43Root_ne_one j)

/-- Each pair gives a unital evaluation of the unchanged third receiver. -/
def evGrid (e : Fin 2) (j : Fin 6) : Carrier →+* ZMod 43 where
  toFun x := evR43 j x.re + eisenstein43Root e * evR43 j x.im
  map_zero' := by simp
  map_one' := by simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  map_add' x y := by simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.im_add, map_add]; ring
  map_mul' x y := by
    simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, map_add, map_mul, map_neg, map_one]
    linear_combination -(evR43 j x.im * evR43 j y.im) * eisenstein43Root_relation e

/-- The coefficient restriction is the original column evaluation. -/
theorem evGrid_comp_cyclotomic (e : Fin 2) (j : Fin 6) :
    (evGrid e j).comp fromCyclotomic = evR43 j := by
  ext x
  simp [evGrid, fromCyclotomic, QuadraticAlgebra.algebraMap_eq]

/-- The quadratic restriction is the original row evaluation. -/
theorem evGrid_comp_eisenstein (e : Fin 2) (j : Fin 6) :
    (evGrid e j).comp fromEisenstein =
      eisensteinResidueRingHom (eisenstein43Root e) (eisenstein43Root_relation e) := by
  ext x
  simp [evGrid, fromEisenstein, eisensteinResidueRingHom, eisensteinResidueEval, mul_comm]

/-- The independent quadratic generator reads the row address. -/
theorem evGrid_tau (e : Fin 2) (j : Fin 6) :
    evGrid e j (fromEisenstein (tau (-1))) = eisenstein43Root e :=
  (DFunLike.congr_fun (evGrid_comp_eisenstein e j) _).trans
    (eisensteinResidueRingHom_tau _ _)

/-- The cyclotomic generator reads the column address. -/
theorem evGrid_zeta (e : Fin 2) (j : Fin 6) :
    evGrid e j (fromCyclotomic SevenCyclotomicDegreeSixInt.zeta) = seven43Root j :=
  (DFunLike.congr_fun (evGrid_comp_cyclotomic e j) _).trans
    (evalCyclotomicFromSeventhRoot_zeta _ _ _ _)

/-- Both scalar embeddings have their canonical integer residue. -/
theorem evGrid_scalar (e : Fin 2) (j : Fin 6) (n : ℤ) :
    evGrid e j (fromEisenstein (n : TraceOneInt (-1))) = (n : ZMod 43) ∧
    evGrid e j (fromCyclotomic (n : SevenCyclotomicDegreeSixInt.Ring)) = (n : ZMod 43) := by
  simp only [map_intCast, and_self]

/-- A grid address is an ideal in C, not an identification of source ideals. -/
def M (e : Fin 2) (j : Fin 6) : Ideal Carrier := RingHom.ker (evGrid e j)

/-- The coefficient restriction already covers the residue field. -/
theorem evGrid_surjective (e : Fin 2) (j : Fin 6) : Function.Surjective (evGrid e j) := by
  intro z
  obtain ⟨x, hx⟩ := evalCyclotomicFromSeventhRoot_surjective
    (seven43Root j) (seven43Root_ne_zero j) (seven43Root_pow_seven j) (seven43Root_ne_one j) z
  exact ⟨fromCyclotomic x, (DFunLike.congr_fun (evGrid_comp_cyclotomic e j) x).trans hx⟩

/-- Every grid kernel is maximal by surjectivity onto the prime field. -/
theorem M_isMaximal (e : Fin 2) (j : Fin 6) : (M e j).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _ (evGrid_surjective e j)

/-- Every maximal grid kernel is prime. -/
theorem M_isPrime (e : Fin 2) (j : Fin 6) : (M e j).IsPrime := (M_isMaximal e j).isPrime

/-- Contraction to E recovers the separately typed row ideal. -/
theorem M_comap_eisenstein (e : Fin 2) (j : Fin 6) :
    Ideal.comap fromEisenstein (M e j) =
      eisensteinResidueIdeal (eisenstein43Root e) (eisenstein43Root_relation e) := by
  ext x
  change ((evGrid e j).comp fromEisenstein) x = 0 ↔
    eisensteinResidueRingHom (eisenstein43Root e) (eisenstein43Root_relation e) x = 0
  rw [evGrid_comp_eisenstein]

/-- Contraction to R recovers the separately typed column ideal. -/
theorem M_comap_cyclotomic (e : Fin 2) (j : Fin 6) :
    Ideal.comap fromCyclotomic (M e j) =
      sixRootKernel (11 : ZMod 43) (by decide) (by decide) (by decide) j := by
  ext x
  change ((evGrid e j).comp fromCyclotomic) x = 0 ↔ evR43 j x = 0
  rw [evGrid_comp_cyclotomic]

/-- The first evaluation is exactly the unchanged Step034 evaluation. -/
theorem evGrid_zero_zero : evGrid 0 0 = eval43 := by
  ext x
  rfl

/-- The first grid ideal is exactly the unchanged Step034 kernel. -/
theorem M_zero_zero : M 0 0 = M43 := congrArg RingHom.ker evGrid_zero_zero

/-- Changing the column leaves the E contraction unchanged. -/
theorem M_comap_eisenstein_column (e : Fin 2) (j k : Fin 6) :
    Ideal.comap fromEisenstein (M e j) = Ideal.comap fromEisenstein (M e k) := by
  rw [M_comap_eisenstein, M_comap_eisenstein]

/-- Changing the row leaves the R contraction unchanged. -/
theorem M_comap_cyclotomic_row (e f : Fin 2) (j : Fin 6) :
    Ideal.comap fromCyclotomic (M e j) = Ideal.comap fromCyclotomic (M f j) := by
  rw [M_comap_cyclotomic, M_comap_cyclotomic]

/-- Kernel equality forces both source addresses to agree. -/
theorem M_injective : Function.Injective (fun x : Fin 2 × Fin 6 => M x.1 x.2) := by
  intro x y h
  have hj : x.2 = y.2 := by
    by_contra hn
    apply sixRootKernel_ne (11 : ZMod 43) (by decide) (by decide) (by decide) x.2 y.2 hn
    simpa only [M_comap_cyclotomic] using congrArg (Ideal.comap fromCyclotomic) h
  have he : x.1 = y.1 := by
    let w : Carrier := fromEisenstein (tau (-1)) - (eisenstein43Root x.1).val
    have hw : w ∈ M x.1 x.2 := by
      change evGrid x.1 x.2 w = 0
      simp [w, map_sub, evGrid_tau]
    have hy : w ∈ M y.1 y.2 := by
      change M x.1 x.2 = M y.1 y.2 at h
      rw [← h]
      exact hw
    have ht : eisenstein43Root y.1 = eisenstein43Root x.1 := by
      have hz : evGrid y.1 y.2 w = 0 := hy
      simpa only [w, map_sub, evGrid_tau, map_natCast, ZMod.natCast_zmod_val,
        sub_eq_zero] using hz
    exact (eisenstein43Root_injective ht).symm
  exact Prod.ext he hj

/-- A row ideal extends into every grid kernel in that row. -/
theorem map_eisenstein_le (e : Fin 2) (j : Fin 6) :
    Ideal.map fromEisenstein
      (eisensteinResidueIdeal (eisenstein43Root e) (eisenstein43Root_relation e)) ≤ M e j := by
  apply Ideal.map_le_iff_le_comap.mpr
  rw [M_comap_eisenstein]

/-- A column ideal extends into both grid kernels in that column. -/
theorem map_cyclotomic_le (e : Fin 2) (j : Fin 6) :
    Ideal.map fromCyclotomic
      (sixRootKernel (11 : ZMod 43) (by decide) (by decide) (by decide) j) ≤ M e j := by
  apply Ideal.map_le_iff_le_comap.mpr
  rw [M_comap_cyclotomic]

/-- The other row detects an element missing from the column-ideal extension. -/
theorem map_cyclotomic_lt_zero_zero :
    Ideal.map fromCyclotomic
      (sixRootKernel (11 : ZMod 43) (by decide) (by decide) (by decide) 0) < M 0 0 := by
  refine lt_iff_le_and_ne.mpr ⟨map_cyclotomic_le 0 0, ?_⟩
  intro h
  have hw : fromEisenstein (tau (-1)) - (37 : Carrier) ∈ M 0 0 := by
    change evGrid 0 0 _ = 0
    simp [map_sub, map_ofNat, evGrid_tau, eisenstein43Root]
  have hy := map_cyclotomic_le 1 0 (h.symm ▸ hw)
  change evGrid 1 0 _ = 0 at hy
  have hz : (7 : ZMod 43) - 37 = 0 := by
    simpa [map_sub, map_ofNat, evGrid_tau, eisenstein43Root] using hy
  exact (by decide : (7 : ZMod 43) - 37 ≠ 0) hz

/-- The other column detects an element missing from the row-ideal extension. -/
theorem map_eisenstein_lt_zero_zero :
    Ideal.map fromEisenstein (eisensteinResidueIdeal (37 : ZMod 43) (by decide)) < M 0 0 := by
  refine lt_iff_le_and_ne.mpr ⟨map_eisenstein_le 0 0, ?_⟩
  intro h
  have hw : fromCyclotomic SevenCyclotomicDegreeSixInt.zeta - (11 : Carrier) ∈ M 0 0 := by
    change evGrid 0 0 _ = 0
    simp [map_sub, map_ofNat, evGrid_zeta, seven43Root]
  have hy := map_eisenstein_le 0 1 (h.symm ▸ hw)
  change evGrid 0 1 _ = 0 at hy
  have hz : (35 : ZMod 43) - 11 = 0 := by
    have hs : seven43Root 1 = (35 : ZMod 43) := by decide
    simpa only [map_sub, map_ofNat, evGrid_zeta, hs] using hy
  exact (by decide : (35 : ZMod 43) - 11 ≠ 0) hz

/-- The actual non-Fermat Eisenstein witness occupies precisely the first row. -/
theorem normCoord_mem_iff (e : Fin 2) (j : Fin 6) :
    fromEisenstein (gtailSevenNormCoord 1166 1857) ∈ M e j ↔ e = 0 := by
  change gtailSevenNormCoord 1166 1857 ∈ Ideal.comap fromEisenstein (M e j) ↔ _
  rw [M_comap_eisenstein, mem_eisensteinResidueIdeal_iff]
  fin_cases e <;> norm_num [eisenstein43Root, eisensteinResidueEval, gtailSevenNormCoord_eq] <;> decide

/-- The actual non-Fermat cyclotomic factor occupies precisely the first column. -/
theorem factor_mem_iff (e : Fin 2) (j : Fin 6) :
    fromCyclotomic (gtailCyclotomicFactor 1858 1165 0) ∈ M e j ↔ j = 0 := by
  change gtailCyclotomicFactor 1858 1165 0 ∈ Ideal.comap fromCyclotomic (M e j) ↔ _
  rw [M_comap_cyclotomic]
  have hr : gtailSevenTailRatio 43 1858 1165 = (11 : ZMod 43) := by
    dsimp [gtailSevenTailRatio]
    apply (div_eq_iff (by decide : (1858 : ZMod 43) ≠ 0)).mpr
    decide
  have h := gtailCyclotomicFactor_unique_slot (q := 43) 1858 1165
    (by decide) (by decide) (by decide) (0 : Fin 6) j
  simpa only [hr, show sixInverseSlot (0 : Fin 6) = 0 from rfl] using h

end DkMath.FLT.Seven.GTailPrimeGrid
