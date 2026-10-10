/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.GTailEisensteinCyclotomicPrimeJoin

#print "file: DkMath.FLT.Seven.GTailFocusedGenericPrimeReceiver"

/-!
# Generic-prime receiver for native Q/T support

A supplied root pair gives one common maximal kernel in the unchanged C.
Natural Q/T inputs select the roots without a Fermat premise. The focused
adapter retains its exact equation premise and bounded one-way power scope;
none of these outputs reconstructs the old signed descent packets.
-/

namespace DkMath.FLT.Seven.GTailGenericPrimeReceiver

open DkMath.NumberTheory.TraceOneQuadratic DkMath.Lib.NumberTheory DkMath.CosmicFormula
open GTailCommonReceiver

private theorem coordinate_split (n : ℕ) (x : Carrier) :
    x = fromCyclotomic (x.re + (n : SevenCyclotomicDegreeSixInt.Ring) * x.im) +
      fromEisenstein (tau (-1) - (n : TraceOneInt (-1))) * fromCyclotomic x.im := by
  rw [map_sub, map_natCast, fromEisenstein_tau]
  apply QuadraticAlgebra.ext <;>
    simp only [fromCyclotomic, QuadraticAlgebra.algebraMap_eq, QuadraticAlgebra.re_add,
      QuadraticAlgebra.im_add, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul,
      QuadraticAlgebra.re_sub, QuadraticAlgebra.im_sub, QuadraticAlgebra.re_omega,
      QuadraticAlgebra.im_omega, QuadraticAlgebra.re_natCast, QuadraticAlgebra.im_natCast] <;> ring

section Pair

variable {q : ℕ} [Fact (Nat.Prime q)] (t r : ZMod q)
  (ht : t ^ 2 - t + 1 = 0) (hr0 : r ≠ 0) (hr7 : r ^ 7 = 1) (hr1 : r ≠ 1)

/-- A supplied pair of roots evaluates the unchanged common receiving ring. -/
def evPair : Carrier →+* ZMod q where
  toFun x := evalCyclotomicFromSeventhRoot r hr0 hr7 hr1 x.re +
    t * evalCyclotomicFromSeventhRoot r hr0 hr7 hr1 x.im
  map_zero' := by simp
  map_one' := by simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  map_add' x y := by simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.im_add, map_add]; ring
  map_mul' x y := by
    simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, map_add, map_mul, map_neg, map_one]
    linear_combination -(evalCyclotomicFromSeventhRoot r hr0 hr7 hr1 x.im *
      evalCyclotomicFromSeventhRoot r hr0 hr7 hr1 y.im) * ht

/-- Restriction to E is the actual Eisenstein root evaluation. -/
theorem evPair_comp_eisenstein : (evPair t r ht hr0 hr7 hr1).comp fromEisenstein =
    eisensteinResidueRingHom t ht := by
  ext x
  simp [evPair, fromEisenstein, eisensteinResidueRingHom, eisensteinResidueEval, mul_comm]

/-- Restriction to R is the actual cyclotomic root evaluation. -/
theorem evPair_comp_cyclotomic : (evPair t r ht hr0 hr7 hr1).comp fromCyclotomic =
    evalCyclotomicFromSeventhRoot r hr0 hr7 hr1 := by
  ext x
  simp [evPair, fromCyclotomic, QuadraticAlgebra.algebraMap_eq]

/-- The prime address belongs to C, with its two sources kept separate. -/
def pairedKernel : Ideal Carrier := RingHom.ker (evPair t r ht hr0 hr7 hr1)

/-- The coefficient restriction covers the prime field. -/
theorem evPair_surjective : Function.Surjective (evPair t r ht hr0 hr7 hr1) := by
  intro z
  obtain ⟨x, hx⟩ := evalCyclotomicFromSeventhRoot_surjective r hr0 hr7 hr1 z
  exact ⟨fromCyclotomic x, (DFunLike.congr_fun
    (evPair_comp_cyclotomic t r ht hr0 hr7 hr1) x).trans hx⟩

/-- The kernel is maximal for any prime admitting the supplied roots. -/
theorem pairedKernel_isMaximal : (pairedKernel t r ht hr0 hr7 hr1).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _ (evPair_surjective t r ht hr0 hr7 hr1)

/-- The same kernel is prime. -/
theorem pairedKernel_isPrime : (pairedKernel t r ht hr0 hr7 hr1).IsPrime :=
  (pairedKernel_isMaximal t r ht hr0 hr7 hr1).isPrime

/-- The E contraction is an equality of ideals in E. -/
theorem pairedKernel_comap_eisenstein :
    Ideal.comap fromEisenstein (pairedKernel t r ht hr0 hr7 hr1) = eisensteinResidueIdeal t ht := by
  ext x
  change ((evPair t r ht hr0 hr7 hr1).comp fromEisenstein) x = 0 ↔ eisensteinResidueRingHom t ht x = 0
  rw [evPair_comp_eisenstein]

/-- The R contraction is an equality of ideals in R. -/
theorem pairedKernel_comap_cyclotomic :
    Ideal.comap fromCyclotomic (pairedKernel t r ht hr0 hr7 hr1) =
      seventhRootKernel r hr0 hr7 hr1 := by
  ext x
  change ((evPair t r ht hr0 hr7 hr1).comp fromCyclotomic) x = 0 ↔
    evalCyclotomicFromSeventhRoot r hr0 hr7 hr1 x = 0
  rw [evPair_comp_cyclotomic]

/-- A single supplied pair generates its common kernel jointly, without a generic grid. -/
theorem pairedKernel_eq_sup : pairedKernel t r ht hr0 hr7 hr1 =
    Ideal.map fromEisenstein (eisensteinResidueIdeal t ht) ⊔
      Ideal.map fromCyclotomic (seventhRootKernel r hr0 hr7 hr1) := by
  let J := pairedKernel t r ht hr0 hr7 hr1
  let P := eisensteinResidueIdeal t ht
  let K := seventhRootKernel r hr0 hr7 hr1
  have leE : Ideal.map fromEisenstein P ≤ J := by
    apply Ideal.map_le_iff_le_comap.mpr
    rw [pairedKernel_comap_eisenstein]
  have leR : Ideal.map fromCyclotomic K ≤ J := by
    apply Ideal.map_le_iff_le_comap.mpr
    rw [pairedKernel_comap_cyclotomic]
  refine le_antisymm ?_ (sup_le leE leR)
  intro x hx
  let y := x.re + (t.val : SevenCyclotomicDegreeSixInt.Ring) * x.im
  let d := tau (-1) - (t.val : TraceOneInt (-1))
  have hy : y ∈ K := by
    change evalCyclotomicFromSeventhRoot r hr0 hr7 hr1 y = 0
    change evalCyclotomicFromSeventhRoot r hr0 hr7 hr1 x.re +
      t * evalCyclotomicFromSeventhRoot r hr0 hr7 hr1 x.im = 0 at hx
    simpa [y] using hx
  have hd : d ∈ P := by
    change eisensteinResidueRingHom t ht d = 0
    simp [d, map_sub, eisensteinResidueRingHom_tau]
  have hyMap := Ideal.mem_map_of_mem fromCyclotomic hy
  have hdMap := (Ideal.map fromEisenstein P).mul_mem_right (fromCyclotomic x.im)
    (Ideal.mem_map_of_mem fromEisenstein hd)
  change x ∈ Ideal.map fromEisenstein P ⊔ Ideal.map fromCyclotomic K
  rw [coordinate_split t.val x]
  exact (Ideal.map fromEisenstein P ⊔ Ideal.map fromCyclotomic K).add_mem
    ((show Ideal.map fromCyclotomic K ≤
      Ideal.map fromEisenstein P ⊔ Ideal.map fromCyclotomic K from le_sup_right) hyMap)
    ((show Ideal.map fromEisenstein P ≤
      Ideal.map fromEisenstein P ⊔ Ideal.map fromCyclotomic K from le_sup_left) hdMap)

end Pair

section Calibration

local instance : Fact (Nat.Prime 43) := ⟨by decide⟩

/-- The old q43 evaluation is literally the supplied-root special case. -/
theorem evPair_43 : evPair (37 : ZMod 43) 11 (by decide) (by decide) (by decide) (by decide) =
    eval43 := by
  ext x
  rfl

/-- The old q43 prime ideal has not been replaced by an isomorphic copy. -/
theorem pairedKernel_43 :
    pairedKernel (37 : ZMod 43) 11 (by decide) (by decide) (by decide) (by decide) = M43 :=
  congrArg RingHom.ker evPair_43

end Calibration

section Native

variable {q : ℕ} [Fact (Nat.Prime q)] (a b c g : ℕ)
  (hQ : q ∣ a ^ 2 + a * b + b ^ 2) (hb : ¬ q ∣ b) (hc : ¬ q ∣ c)
  (hg : ¬ q ∣ g) (hT : q ∣ GTail 7 1 g c)

/-- Natural Q/T data supply both roots; no Fermat equation or additive focus is assumed. -/
def nativeEval : Carrier →+* ZMod q :=
  evPair (gtailSevenResidueRoot q a b) (gtailSevenTailRatio q c g)
    (gtailSevenResidueRoot_polynomial hQ hb) (gtailSevenTailRatio_ne_zero hc hT)
    (gtailSevenTailRatio_pow_seven hc hT) (gtailSevenTailRatio_ne_one hc hg)

/-- The common kernel selected by actual natural source coordinates. -/
def nativeKernel : Ideal Carrier := RingHom.ker (nativeEval a b c g hQ hb hc hg hT)

/-- The source-linked common kernel is maximal. -/
theorem nativeKernel_isMaximal : (nativeKernel a b c g hQ hb hc hg hT).IsMaximal :=
  pairedKernel_isMaximal _ _ _ _ _ _

/-- Its E contraction is the actual natural quadratic residue ideal. -/
theorem nativeKernel_comap_eisenstein :
    Ideal.comap fromEisenstein (nativeKernel a b c g hQ hb hc hg hT) =
      eisensteinResidueIdeal (gtailSevenResidueRoot q a b) (gtailSevenResidueRoot_polynomial hQ hb) :=
  pairedKernel_comap_eisenstein _ _ _ _ _ _

/-- Its R contraction is the actual natural Tail root ideal. -/
theorem nativeKernel_comap_cyclotomic :
    Ideal.comap fromCyclotomic (nativeKernel a b c g hQ hb hc hg hT) =
      seventhRootKernel (gtailSevenTailRatio q c g) (gtailSevenTailRatio_ne_zero hc hT)
        (gtailSevenTailRatio_pow_seven hc hT) (gtailSevenTailRatio_ne_one hc hg) :=
  pairedKernel_comap_cyclotomic _ _ _ _ _ _

/-- The native Eisenstein coordinate belongs to its own source ideal. -/
theorem native_eisenstein_source_mem :
    gtailSevenNormCoord a b ∈ eisensteinResidueIdeal (gtailSevenResidueRoot q a b)
      (gtailSevenResidueRoot_polynomial hQ hb) := gtailSevenNormCoord_mem_residueIdeal hQ hb

/-- The actual slot-zero Tail factor belongs to its own source root ideal. -/
theorem native_factor_source_mem :
    gtailCyclotomicFactor c g 0 ∈ seventhRootKernel (gtailSevenTailRatio q c g)
      (gtailSevenTailRatio_ne_zero hc hT) (gtailSevenTailRatio_pow_seven hc hT)
      (gtailSevenTailRatio_ne_one hc hg) := by
  have hm := (gtailCyclotomicFactor_unique_slot c g hc hg hT (0 : Fin 6) 0).mpr rfl
  simpa only [sixRootKernel, sixSlotRoot_zero] using hm

/-- Typed E contraction transports the actual native coordinate into the common kernel. -/
theorem native_eisenstein_mem :
    fromEisenstein (gtailSevenNormCoord a b) ∈ nativeKernel a b c g hQ hb hc hg hT := by
  change gtailSevenNormCoord a b ∈ Ideal.comap fromEisenstein (nativeKernel a b c g hQ hb hc hg hT)
  rw [nativeKernel_comap_eisenstein]
  exact native_eisenstein_source_mem a b hQ hb

/-- Typed R contraction transports the actual selected factor into the common kernel. -/
theorem native_factor_mem :
    fromCyclotomic (gtailCyclotomicFactor c g 0) ∈ nativeKernel a b c g hQ hb hc hg hT := by
  change gtailCyclotomicFactor c g 0 ∈ Ideal.comap fromCyclotomic (nativeKernel a b c g hQ hb hc hg hT)
  rw [nativeKernel_comap_cyclotomic]
  exact native_factor_source_mem c g hc hg hT

/-- Both images have zero residue, without asserting equality in C. -/
theorem native_residue_zeros :
    nativeEval a b c g hQ hb hc hg hT (fromEisenstein (gtailSevenNormCoord a b)) = 0 ∧
    nativeEval a b c g hQ hb hc hg hT (fromCyclotomic (gtailCyclotomicFactor c g 0)) = 0 :=
  ⟨native_eisenstein_mem a b c g hQ hb hc hg hT, native_factor_mem a b c g hQ hb hc hg hT⟩

end Native

section Focused

variable {q : ℕ} [Fact (Nat.Prime q)] (a b c g : ℕ)

/-- Additional source square support gives only the four bounded common-power lower bounds. -/
theorem native_square_support (hQ : q ∣ a ^ 2 + a * b + b ^ 2) (hb : ¬ q ∣ b)
    (hc : ¬ q ∣ c) (hg : ¬ q ∣ g) (hT : q ∣ GTail 7 1 g c)
    (hq3 : q ≠ 3) (hT2 : q ^ 2 ∣ GTail 7 1 g c) :
    let J := nativeKernel a b c g hQ hb hc hg hT
    fromEisenstein ((gtailSevenNormCoord a b : TraceOneInt (-1)) ^ 2) ∈ J ^ 2 ∧
    fromCyclotomic (gtailCyclotomicFactor c g 0) ∈ J ^ 2 ∧
    fromEisenstein (gtailSevenNormCoord a b) * fromCyclotomic (gtailCyclotomicFactor c g 0) ∈ J ^ 3 ∧
    fromEisenstein ((gtailSevenNormCoord a b : TraceOneInt (-1)) ^ 2) *
      fromCyclotomic (gtailCyclotomicFactor c g 0) ∈ J ^ 4 := by
  let J := nativeKernel a b c g hQ hb hc hg hT
  let P := eisensteinResidueIdeal (gtailSevenResidueRoot q a b) (gtailSevenResidueRoot_polynomial hQ hb)
  let K := seventhRootKernel (gtailSevenTailRatio q c g) (gtailSevenTailRatio_ne_zero hc hT)
    (gtailSevenTailRatio_pow_seven hc hT) (gtailSevenTailRatio_ne_one hc hg)
  have leE : Ideal.map fromEisenstein P ≤ J := by
    apply Ideal.map_le_iff_le_comap.mpr
    rw [nativeKernel_comap_eisenstein]
  have leR : Ideal.map fromCyclotomic K ≤ J := by
    apply Ideal.map_le_iff_le_comap.mpr
    rw [nativeKernel_comap_cyclotomic]
  have he : (gtailSevenNormCoord a b : TraceOneInt (-1)) ^ 2 ∈ P ^ 2 := by
    simpa only [P, pow_two] using (gtailSevenNormCoord_split_square_address hq3 hQ hb).1
  have hf : gtailCyclotomicFactor c g 0 ∈ K ^ 2 := by
    have h := (gtailCyclotomicFactor_mem_square_iff c g hc hg hT (0 : Fin 6)).mpr hT2
    simpa only [K, sixRootKernel, sixSlotRoot_zero,
      show sixInverseSlot (0 : Fin 6) = 0 from rfl] using h
  have heMap : fromEisenstein ((gtailSevenNormCoord a b : TraceOneInt (-1)) ^ 2) ∈
      (Ideal.map fromEisenstein P) ^ 2 := by
    rw [← Ideal.map_pow]
    exact Ideal.mem_map_of_mem fromEisenstein he
  have hfMap : fromCyclotomic (gtailCyclotomicFactor c g 0) ∈ (Ideal.map fromCyclotomic K) ^ 2 := by
    rw [← Ideal.map_pow]
    exact Ideal.mem_map_of_mem fromCyclotomic hf
  have heJ := (pow_le_pow_left' leE 2) heMap
  have hfJ := (pow_le_pow_left' leR 2) hfMap
  refine ⟨heJ, hfJ, ?_, ?_⟩
  · rw [show (3 : ℕ) = 1 + 2 from rfl, pow_add, pow_one]
    exact Ideal.mul_mem_mul (native_eisenstein_mem a b c g hQ hb hc hg hT) hfJ
  · rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add]
    exact Ideal.mul_mem_mul heJ hfJ

/-- A conditional adapter derives all local units from the existing focused Fermat contract. -/
theorem focused_receiver (ha : 0 < a) (hbpos : 0 < b) (hcop : Nat.Coprime a b)
    (hEq : Fermat7Equation a b c) (hfocus : a + b = c + g)
    (hq7 : q ≠ 7) (hQ : q ∣ a ^ 2 + a * b + b ^ 2) (hT : q ∣ GTail 7 1 g c) :
    let hu := focused_norm_depth_guards hcop hEq hfocus hq7 hQ hT
    let J := nativeKernel a b c g hQ hu.2.1 hu.2.2.2.1 hu.2.2.2.2.1 hT
    J.IsMaximal ∧
    Ideal.comap fromEisenstein J = eisensteinResidueIdeal (gtailSevenResidueRoot q a b)
      (gtailSevenResidueRoot_polynomial hQ hu.2.1) ∧
    Ideal.comap fromCyclotomic J = seventhRootKernel (gtailSevenTailRatio q c g)
      (gtailSevenTailRatio_ne_zero hu.2.2.2.1 hT) (gtailSevenTailRatio_pow_seven hu.2.2.2.1 hT)
      (gtailSevenTailRatio_ne_one hu.2.2.2.1 hu.2.2.2.2.1) ∧
    fromEisenstein (gtailSevenNormCoord a b) ∈ J ∧
    fromCyclotomic (gtailCyclotomicFactor c g 0) ∈ J ∧
    padicValNat q (GTail 7 1 g c) = 2 * padicValNat q (a ^ 2 + a * b + b ^ 2) ∧
    Even (padicValNat q (GTail 7 1 g c)) ∧ q ^ 2 ∣ GTail 7 1 g c ∧
    (q ^ 4 ∣ GTail 7 1 g c ↔ q ^ 2 ∣ a ^ 2 + a * b + b ^ 2) ∧
    (q ^ 3 ∣ GTail 7 1 g c ↔ q ^ 4 ∣ GTail 7 1 g c) ∧
    fromEisenstein ((gtailSevenNormCoord a b : TraceOneInt (-1)) ^ 2) ∈ J ^ 2 ∧
    fromCyclotomic (gtailCyclotomicFactor c g 0) ∈ J ^ 2 ∧
    fromEisenstein (gtailSevenNormCoord a b) * fromCyclotomic (gtailCyclotomicFactor c g 0) ∈ J ^ 3 ∧
    fromEisenstein ((gtailSevenNormCoord a b : TraceOneInt (-1)) ^ 2) *
      fromCyclotomic (gtailCyclotomicFactor c g 0) ∈ J ^ 4 := by
  have hu := focused_norm_depth_guards hcop hEq hfocus hq7 hQ hT
  have hd := focused_norm_scalar_depth_readouts ha hbpos hcop hEq hfocus hq7 hQ hT
  have hp : Even (padicValNat q (GTail 7 1 g c)) :=
    ⟨padicValNat q (a ^ 2 + a * b + b ^ 2), by omega⟩
  have hs := native_square_support a b c g hQ hu.2.1 hu.2.2.2.1 hu.2.2.2.2.1 hT hu.2.2.2.2.2 hd.2.1
  exact ⟨nativeKernel_isMaximal a b c g hQ hu.2.1 hu.2.2.2.1 hu.2.2.2.2.1 hT,
    nativeKernel_comap_eisenstein a b c g hQ hu.2.1 hu.2.2.2.1 hu.2.2.2.2.1 hT,
    nativeKernel_comap_cyclotomic a b c g hQ hu.2.1 hu.2.2.2.1 hu.2.2.2.2.1 hT,
    native_eisenstein_mem a b c g hQ hu.2.1 hu.2.2.2.1 hu.2.2.2.2.1 hT,
    native_factor_mem a b c g hQ hu.2.1 hu.2.2.2.1 hu.2.2.2.2.1 hT,
    hd.1, hp, hd.2.1, hd.2.2.1, hd.2.2.2, hs⟩

end Focused

end DkMath.FLT.Seven.GTailGenericPrimeReceiver
