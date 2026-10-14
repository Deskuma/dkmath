/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.GTailFocusedGenericPrimeReceiver

#print "file: DkMathTest.FLT.Seven.GTailFocusedGenericPrimeReceiver"

namespace DkMathTest.FLT.Seven.GTailFocusedGenericPrimeReceiver

open DkMath.CosmicFormula DkMath.FLT.Seven DkMath.Lib.NumberTheory
open DkMath.NumberTheory.TraceOneQuadratic
open DkMath.FLT.Seven.GTailCommonReceiver DkMath.FLT.Seven.GTailGenericPrimeReceiver

section Generic

variable {q : ℕ} [Fact (Nat.Prime q)] (t r : ZMod q)
  (ht : t ^ 2 - t + 1 = 0) (hr0 : r ≠ 0) (hr7 : r ^ 7 = 1) (hr1 : r ≠ 1)

example : Carrier →+* ZMod q := evPair t r ht hr0 hr7 hr1
example : Function.Surjective (evPair t r ht hr0 hr7 hr1) := evPair_surjective t r ht hr0 hr7 hr1
example : (pairedKernel t r ht hr0 hr7 hr1).IsMaximal := pairedKernel_isMaximal t r ht hr0 hr7 hr1
example : (pairedKernel t r ht hr0 hr7 hr1).IsPrime := pairedKernel_isPrime t r ht hr0 hr7 hr1
example : (evPair t r ht hr0 hr7 hr1).comp fromEisenstein = eisensteinResidueRingHom t ht :=
  evPair_comp_eisenstein t r ht hr0 hr7 hr1
example : (evPair t r ht hr0 hr7 hr1).comp fromCyclotomic =
    evalCyclotomicFromSeventhRoot r hr0 hr7 hr1 := evPair_comp_cyclotomic t r ht hr0 hr7 hr1
example : Ideal.comap fromEisenstein (pairedKernel t r ht hr0 hr7 hr1) = eisensteinResidueIdeal t ht :=
  pairedKernel_comap_eisenstein t r ht hr0 hr7 hr1
example : Ideal.comap fromCyclotomic (pairedKernel t r ht hr0 hr7 hr1) =
    seventhRootKernel r hr0 hr7 hr1 := pairedKernel_comap_cyclotomic t r ht hr0 hr7 hr1
example (n : ℤ) : evPair t r ht hr0 hr7 hr1 (n : Carrier) = (n : ZMod q) := map_intCast _ n
example : evPair t r ht hr0 hr7 hr1 (fromEisenstein (tau (-1))) = t :=
  (DFunLike.congr_fun (evPair_comp_eisenstein t r ht hr0 hr7 hr1) _).trans
    (eisensteinResidueRingHom_tau t ht)
example : evPair t r ht hr0 hr7 hr1 (fromCyclotomic SevenCyclotomicDegreeSixInt.zeta) = r :=
  (DFunLike.congr_fun (evPair_comp_cyclotomic t r ht hr0 hr7 hr1) _).trans
    (evalCyclotomicFromSeventhRoot_zeta r hr0 hr7 hr1)

example : pairedKernel t r ht hr0 hr7 hr1 =
    Ideal.map fromEisenstein (eisensteinResidueIdeal t ht) ⊔
      Ideal.map fromCyclotomic (seventhRootKernel r hr0 hr7 hr1) :=
  pairedKernel_eq_sup t r ht hr0 hr7 hr1

end Generic

section Native

variable {q : ℕ} [Fact (Nat.Prime q)] (a b c g : ℕ)
  (hQ : q ∣ a ^ 2 + a * b + b ^ 2) (hb : ¬ q ∣ b) (hc : ¬ q ∣ c)
  (hg : ¬ q ∣ g) (hT : q ∣ GTail 7 1 g c)

example : (nativeKernel a b c g hQ hb hc hg hT).IsMaximal :=
  nativeKernel_isMaximal a b c g hQ hb hc hg hT
example : fromEisenstein (gtailSevenNormCoord a b) ∈ nativeKernel a b c g hQ hb hc hg hT :=
  native_eisenstein_mem a b c g hQ hb hc hg hT
example : fromCyclotomic (gtailCyclotomicFactor c g 0) ∈ nativeKernel a b c g hQ hb hc hg hT :=
  native_factor_mem a b c g hQ hb hc hg hT
example : nativeEval a b c g hQ hb hc hg hT (fromEisenstein (gtailSevenNormCoord a b)) =
    nativeEval a b c g hQ hb hc hg hT (fromCyclotomic (gtailCyclotomicFactor c g 0)) :=
  (native_residue_zeros a b c g hQ hb hc hg hT).1.trans
    (native_residue_zeros a b c g hQ hb hc hg hT).2.symm

example : nativeKernel a b c g hQ hb hc hg hT =
    Ideal.map fromEisenstein
      (eisensteinResidueIdeal (gtailSevenResidueRoot q a b) (gtailSevenResidueRoot_polynomial hQ hb)) ⊔
    Ideal.map fromCyclotomic (seventhRootKernel (gtailSevenTailRatio q c g)
      (gtailSevenTailRatio_ne_zero hc hT) (gtailSevenTailRatio_pow_seven hc hT)
      (gtailSevenTailRatio_ne_one hc hg)) := pairedKernel_eq_sup _ _ _ _ _ _

end Native

-- The Fermat-facing adapter remains symbolic and explicitly conditional.
example {q a b c g : ℕ} [Fact (Nat.Prime q)] (ha : 0 < a) (hbpos : 0 < b)
    (hcop : Nat.Coprime a b) (hEq : Fermat7Equation a b c) (hfocus : a + b = c + g)
    (hq7 : q ≠ 7) (hQ : q ∣ a ^ 2 + a * b + b ^ 2) (hT : q ∣ GTail 7 1 g c) :
    let hu := focused_norm_depth_guards hcop hEq hfocus hq7 hQ hT
    let J := nativeKernel a b c g hQ hu.2.1 hu.2.2.2.1 hu.2.2.2.2.1 hT
    J.IsMaximal ∧ fromEisenstein (gtailSevenNormCoord a b) ∈ J ∧
      fromCyclotomic (gtailCyclotomicFactor c g 0) ∈ J := by
  rcases focused_receiver a b c g ha hbpos hcop hEq hfocus hq7 hQ hT with
    ⟨hm, _, _, he, hr, _, _, _, _, _, _⟩
  exact ⟨hm, he, hr⟩
example {q a b c g : ℕ} [Fact (Nat.Prime q)] (ha : 0 < a) (hbpos : 0 < b)
    (hcop : Nat.Coprime a b) (hEq : Fermat7Equation a b c) (hfocus : a + b = c + g)
    (hq7 : q ≠ 7) (hQ : q ∣ a ^ 2 + a * b + b ^ 2) (hT : q ∣ GTail 7 1 g c) :
    Even (padicValNat q (GTail 7 1 g c)) := by
  rcases focused_receiver a b c g ha hbpos hcop hEq hfocus hq7 hQ hT with
    ⟨_, _, _, _, _, _, hp, _, _, _, _⟩
  exact hp

section Q43

local instance : Fact (Nat.Prime 43) := ⟨by decide⟩
local notation "E" => TraceOneInt (-1)
local notation "R" => SevenCyclotomicDegreeSixInt.Ring
local notation "J43" => nativeKernel 1166 1857 1858 1165
  (by decide : 43 ∣ 1166 ^ 2 + 1166 * 1857 + 1857 ^ 2) (by decide) (by decide) (by decide) (by decide)
local notation "Jsmall" => nativeKernel 5 8 9 4
  (by decide : 43 ∣ 5 ^ 2 + 5 * 8 + 8 ^ 2) (by decide) (by decide) (by decide) (by decide)
local notation "K0" => sixRootKernel (11 : ZMod 43) (by decide) (by decide) (by decide) 0
local notation "α" => gtailSevenNormCoord 1166 1857
local notation "F0" => gtailCyclotomicFactor 1858 1165 (0 : Fin 6)

private theorem eroot : gtailSevenResidueRoot 43 1166 1857 = 37 := by
  dsimp [gtailSevenResidueRoot]
  apply (div_eq_iff (by decide : (1857 : ZMod 43) ≠ 0)).mpr
  decide
private theorem rroot : gtailSevenTailRatio 43 1858 1165 = 11 := by
  dsimp [gtailSevenTailRatio]
  apply (div_eq_iff (by decide : (1858 : ZMod 43) ≠ 0)).mpr
  decide
private theorem esmall : gtailSevenResidueRoot 43 5 8 = 37 := by
  dsimp [gtailSevenResidueRoot]
  apply (div_eq_iff (by decide : (8 : ZMod 43) ≠ 0)).mpr
  decide
private theorem rsmall : gtailSevenTailRatio 43 9 4 = 11 := by
  dsimp [gtailSevenTailRatio]
  apply (div_eq_iff (by decide : (9 : ZMod 43) ≠ 0)).mpr
  decide

example : evPair (37 : ZMod 43) 11 (by decide) (by decide) (by decide) (by decide) = eval43 := evPair_43
example : pairedKernel (37 : ZMod 43) 11 (by decide) (by decide) (by decide) (by decide) = M43 :=
  pairedKernel_43
example : gtailSevenResidueRoot 43 1166 1857 = 37 ∧ gtailSevenTailRatio 43 1858 1165 = 11 :=
  ⟨eroot, rroot⟩
private theorem native43_eq : J43 = M43 := by
  unfold nativeKernel nativeEval
  simp only [eroot, rroot]
  exact pairedKernel_43
example : J43 = M43 := native43_eq
example : fromEisenstein α ∈ J43 := native_eisenstein_mem _ _ _ _ _ _ _ _ _
example : fromCyclotomic F0 ∈ J43 := native_factor_mem _ _ _ _ _ _ _ _ _
example : (J43).IsMaximal := nativeKernel_isMaximal _ _ _ _ _ _ _ _ _
example : fromEisenstein α ≠ fromCyclotomic F0 := by
  intro h
  have hh : ((1857 : ℤ) : R) = 0 := by
    simpa [fromEisenstein, fromCyclotomic, QuadraticAlgebra.algebraMap_eq, gtailSevenNormCoord_eq]
      using congrArg (fun x : Carrier => x.im) h
  have he := congrArg (evalCyclotomicFromSeventhRoot (11 : ZMod 43)
    (by decide) (by decide) (by decide)) hh
  exact (by decide : ((1857 : ℤ) : ZMod 43) ≠ 0)
    (by simpa only [map_intCast, map_zero] using he)
example : (1166 + 1857 : ℕ) = 1858 + 1165 ∧ Nat.Coprime 1166 1857 := by decide
example : (43 : ℕ) ∣ 1166 ^ 2 + 1166 * 1857 + 1857 ^ 2 ∧
    (43 : ℕ) ∣ GTail 7 1 1165 1858 ∧ ¬ (43 : ℕ) ∣ 1857 ∧
    ¬ (43 : ℕ) ∣ 1858 ∧ ¬ (43 : ℕ) ∣ 1165 := by decide
example : ¬ Fermat7Equation 1166 1857 1858 := by unfold Fermat7Equation; decide
example : ¬ ((1165 : ℕ) * GTail 7 1 1165 1858 =
    7 * 1166 * 1857 * (1166 + 1857) * (1166 ^ 2 + 1166 * 1857 + 1857 ^ 2) ^ 2) := by decide
example : fromEisenstein ((α : E) ^ 2) ∈ J43 ^ 2 ∧ fromCyclotomic F0 ∈ J43 ^ 2 ∧
    fromEisenstein α * fromCyclotomic F0 ∈ J43 ^ 3 ∧
    fromEisenstein ((α : E) ^ 2) * fromCyclotomic F0 ∈ J43 ^ 4 :=
  native_square_support _ _ _ _ _ _ _ _ _ (by decide) (by decide)

-- The small tuple IS additive-focused, but has only the first Tail power.
example : (5 + 8 : ℕ) = 9 + 4 ∧ Nat.Coprime 5 8 := by decide
example : gtailSevenResidueRoot 43 5 8 = 37 ∧ gtailSevenTailRatio 43 9 4 = 11 := ⟨esmall, rsmall⟩
example : Jsmall = M43 := by
  unfold nativeKernel nativeEval
  simp only [esmall, rsmall]
  exact pairedKernel_43
example : fromEisenstein (gtailSevenNormCoord 5 8) ∈ Jsmall := native_eisenstein_mem _ _ _ _ _ _ _ _ _
example : fromCyclotomic (gtailCyclotomicFactor 9 4 0) ∈ Jsmall := native_factor_mem _ _ _ _ _ _ _ _ _
example : (43 : ℕ) ∣ GTail 7 1 4 9 ∧ ¬ (43 : ℕ) ^ 2 ∣ GTail 7 1 4 9 := by decide
example : gtailCyclotomicFactor 9 4 0 ∉ K0 ^ 2 := by
  have h := gtailCyclotomicFactor_mem_square_iff (q := 43) 9 4 (by decide) (by decide) (by decide) 0
  simp only [rsmall, show sixInverseSlot (0 : Fin 6) = 0 from rfl] at h
  exact fun hm => (by decide : ¬ (43 : ℕ) ^ 2 ∣ GTail 7 1 4 9) (h.mp hm)
example : ¬ (padicValNat 43 4 + padicValNat 43 (GTail 7 1 4 9) =
    2 * padicValNat 43 (5 ^ 2 + 5 * 8 + 8 ^ 2)) := by
  intro hbgt
  have h := scalar_budget_depth_readouts 43 4 (GTail 7 1 4 9)
    (5 ^ 2 + 5 * 8 + 8 ^ 2) (by decide) (by decide) (by decide) (by decide) hbgt
  exact (by decide : ¬ (43 : ℕ) ^ 2 ∣ GTail 7 1 4 9) (h.1.mpr (by decide))
example : ¬ Fermat7Equation 5 8 9 := by unfold Fermat7Equation; decide
example : GTailPrimeJoin.A 0 < GTailPrimeGrid.M 0 0 := GTailPrimeGrid.map_eisenstein_lt_zero_zero
example : GTailPrimeJoin.B 0 < GTailPrimeGrid.M 0 0 := GTailPrimeGrid.map_cyclotomic_lt_zero_zero
example : GTailPrimeGrid.M 0 0 = GTailPrimeJoin.A 0 ⊔ GTailPrimeJoin.B 0 :=
  GTailPrimeJoin.M_eq_map_eisenstein_sup_map_cyclotomic 0 0
example : ¬ Nonempty (E →+* R) := not_nonempty_eisenstein_to_seven_cyclotomic
example : ¬ Nonempty (R →+* E) := not_nonempty_seven_cyclotomic_to_eisenstein

end Q43

section Q127

local instance : Fact (Nat.Prime 127) := ⟨by decide⟩
local notation "J127" => pairedKernel (20 : ZMod 127) 2 (by decide) (by decide) (by decide) (by decide)
local notation "ev127" => evPair (20 : ZMod 127) 2 (by decide) (by decide) (by decide) (by decide)

example : (20 : ZMod 127) ^ 2 - 20 + 1 = 0 := by decide
example : (2 : ZMod 127) ^ 7 = 1 ∧ (2 : ZMod 127) ≠ 0 ∧ (2 : ZMod 127) ≠ 1 := by decide
example : (J127).IsMaximal := pairedKernel_isMaximal _ _ _ _ _ _
example : (J127).IsPrime := pairedKernel_isPrime _ _ _ _ _ _
example : Function.Surjective ev127 := evPair_surjective _ _ _ _ _ _
example : Ideal.comap fromEisenstein J127 = eisensteinResidueIdeal (20 : ZMod 127) (by decide) :=
  pairedKernel_comap_eisenstein _ _ _ _ _ _
example : Ideal.comap fromCyclotomic J127 =
    seventhRootKernel (2 : ZMod 127) (by decide) (by decide) (by decide) :=
  pairedKernel_comap_cyclotomic _ _ _ _ _ _
example : ev127 (fromEisenstein (tau (-1))) = 20 :=
  (DFunLike.congr_fun (evPair_comp_eisenstein (20 : ZMod 127) 2 (by decide) (by decide) (by decide) (by decide)) _).trans
    (eisensteinResidueRingHom_tau _ _)
example : ev127 (fromCyclotomic SevenCyclotomicDegreeSixInt.zeta) = 2 :=
  (DFunLike.congr_fun (evPair_comp_cyclotomic (20 : ZMod 127) 2 (by decide) (by decide) (by decide) (by decide)) _).trans
    (evalCyclotomicFromSeventhRoot_zeta _ _ _ _)

end Q127

-- Excluded characteristic and Gap-only inputs do not supply the root contracts.
example : ¬ ∃ r : ZMod 7, r ^ 7 = 1 ∧ r ≠ 1 := by decide
example : ¬ ∃ r : ZMod 3, r ^ 7 = 1 ∧ r ≠ 1 := by decide
example : ¬ ∃ r : ZMod 13, r ^ 7 = 1 ∧ r ≠ 1 := by decide
example : (14 + 29 : ℕ) = 30 + 13 ∧ (13 : ℕ) ∣ 14 ^ 2 + 14 * 29 + 29 ^ 2 ∧
    (13 : ℕ) ∣ 13 ∧ ¬ (13 : ℕ) ∣ GTail 7 1 13 30 := by decide

#check DkMath.FLT.Seven.GTailGenericPrimeReceiver.evPair
#print axioms DkMath.FLT.Seven.GTailGenericPrimeReceiver.evPair
#check DkMath.FLT.Seven.GTailGenericPrimeReceiver.evPair_comp_eisenstein
#print axioms DkMath.FLT.Seven.GTailGenericPrimeReceiver.evPair_comp_eisenstein
#check DkMath.FLT.Seven.GTailGenericPrimeReceiver.evPair_comp_cyclotomic
#print axioms DkMath.FLT.Seven.GTailGenericPrimeReceiver.evPair_comp_cyclotomic
#check DkMath.FLT.Seven.GTailGenericPrimeReceiver.pairedKernel
#print axioms DkMath.FLT.Seven.GTailGenericPrimeReceiver.pairedKernel
#check DkMath.FLT.Seven.GTailGenericPrimeReceiver.evPair_surjective
#print axioms DkMath.FLT.Seven.GTailGenericPrimeReceiver.evPair_surjective
#check DkMath.FLT.Seven.GTailGenericPrimeReceiver.pairedKernel_isMaximal
#print axioms DkMath.FLT.Seven.GTailGenericPrimeReceiver.pairedKernel_isMaximal
#check DkMath.FLT.Seven.GTailGenericPrimeReceiver.pairedKernel_isPrime
#print axioms DkMath.FLT.Seven.GTailGenericPrimeReceiver.pairedKernel_isPrime
#check DkMath.FLT.Seven.GTailGenericPrimeReceiver.pairedKernel_comap_eisenstein
#print axioms DkMath.FLT.Seven.GTailGenericPrimeReceiver.pairedKernel_comap_eisenstein
#check DkMath.FLT.Seven.GTailGenericPrimeReceiver.pairedKernel_comap_cyclotomic
#print axioms DkMath.FLT.Seven.GTailGenericPrimeReceiver.pairedKernel_comap_cyclotomic
#check DkMath.FLT.Seven.GTailGenericPrimeReceiver.pairedKernel_eq_sup
#print axioms DkMath.FLT.Seven.GTailGenericPrimeReceiver.pairedKernel_eq_sup
#check DkMath.FLT.Seven.GTailGenericPrimeReceiver.evPair_43
#print axioms DkMath.FLT.Seven.GTailGenericPrimeReceiver.evPair_43
#check DkMath.FLT.Seven.GTailGenericPrimeReceiver.pairedKernel_43
#print axioms DkMath.FLT.Seven.GTailGenericPrimeReceiver.pairedKernel_43
#check DkMath.FLT.Seven.GTailGenericPrimeReceiver.nativeEval
#print axioms DkMath.FLT.Seven.GTailGenericPrimeReceiver.nativeEval
#check DkMath.FLT.Seven.GTailGenericPrimeReceiver.nativeKernel
#print axioms DkMath.FLT.Seven.GTailGenericPrimeReceiver.nativeKernel
#check DkMath.FLT.Seven.GTailGenericPrimeReceiver.nativeKernel_isMaximal
#print axioms DkMath.FLT.Seven.GTailGenericPrimeReceiver.nativeKernel_isMaximal
#check DkMath.FLT.Seven.GTailGenericPrimeReceiver.nativeKernel_comap_eisenstein
#print axioms DkMath.FLT.Seven.GTailGenericPrimeReceiver.nativeKernel_comap_eisenstein
#check DkMath.FLT.Seven.GTailGenericPrimeReceiver.nativeKernel_comap_cyclotomic
#print axioms DkMath.FLT.Seven.GTailGenericPrimeReceiver.nativeKernel_comap_cyclotomic
#check DkMath.FLT.Seven.GTailGenericPrimeReceiver.native_eisenstein_source_mem
#print axioms DkMath.FLT.Seven.GTailGenericPrimeReceiver.native_eisenstein_source_mem
#check DkMath.FLT.Seven.GTailGenericPrimeReceiver.native_factor_source_mem
#print axioms DkMath.FLT.Seven.GTailGenericPrimeReceiver.native_factor_source_mem
#check DkMath.FLT.Seven.GTailGenericPrimeReceiver.native_eisenstein_mem
#print axioms DkMath.FLT.Seven.GTailGenericPrimeReceiver.native_eisenstein_mem
#check DkMath.FLT.Seven.GTailGenericPrimeReceiver.native_factor_mem
#print axioms DkMath.FLT.Seven.GTailGenericPrimeReceiver.native_factor_mem
#check DkMath.FLT.Seven.GTailGenericPrimeReceiver.native_residue_zeros
#print axioms DkMath.FLT.Seven.GTailGenericPrimeReceiver.native_residue_zeros
#check DkMath.FLT.Seven.GTailGenericPrimeReceiver.native_square_support
#print axioms DkMath.FLT.Seven.GTailGenericPrimeReceiver.native_square_support
#check DkMath.FLT.Seven.GTailGenericPrimeReceiver.focused_receiver
#print axioms DkMath.FLT.Seven.GTailGenericPrimeReceiver.focused_receiver

end DkMathTest.FLT.Seven.GTailFocusedGenericPrimeReceiver
