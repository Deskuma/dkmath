/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.GTailFocusedPrimeRoute

#print "file: DkMathTest.FLT.Seven.GTailFocusedPrimeRoute"

namespace DkMathTest.FLT.Seven.GTailFocusedPrimeRoute

open DkMath.CosmicFormula DkMath.FLT.Seven DkMath.Lib.NumberTheory
open DkMath.NumberTheory.TraceOneQuadratic
open DkMath.FLT.Seven.GTailCommonReceiver DkMath.FLT.Seven.GTailGenericPrimeReceiver

open DkMath.FLT.Seven.GTailFocusedPrimeRoute

section Symbolic

variable {q a b c g : ℕ} [Fact (Nat.Prime q)]

example (hc : ¬ q ∣ c) (hg : q ∣ g) : gtailSevenTailRatio q c g = 1 := gap_ratio_eq_one hc hg
example (hc : ¬ q ∣ c) (hg : q ∣ g) : ¬ (gtailSevenTailRatio q c g ≠ 1) :=
  gap_nonidentity_guard_unavailable hc hg
example (hcop : Nat.Coprime a b) (hEq : Fermat7Equation a b c)
    (hQ : q ∣ a ^ 2 + a * b + b ^ 2) :
    (¬ q ∣ a) ∧ (¬ q ∣ b) ∧ (¬ q ∣ a + b) ∧ (¬ q ∣ c) :=
  focused_coordinate_units hcop hEq hQ
example (ha : 0 < a) (hb : 0 < b) (hcop : Nat.Coprime a b)
    (hEq : Fermat7Equation a b c) (hfocus : a + b = c + g)
    (hq7 : q ≠ 7) (hQ : q ∣ a ^ 2 + a * b + b ^ 2) :
    (q ^ 2 ∣ g ∧ ¬ q ∣ GTail 7 1 g c ∧ gtailSevenTailRatio q c g = 1) ∨
      (q ^ 2 ∣ GTail 7 1 g c ∧ ¬ q ∣ g ∧ q ∣ GTail 7 1 g c) :=
  focused_prime_route ha hb hcop hEq hfocus hq7 hQ

example (ha : 0 < a) (hbpos : 0 < b) (hcop : Nat.Coprime a b)
    (hEq : Fermat7Equation a b c) (hfocus : a + b = c + g)
    (hq7 : q ≠ 7) (hQ : q ∣ a ^ 2 + a * b + b ^ 2) (hT2 : q ^ 2 ∣ GTail 7 1 g c) :
    let hT : q ∣ GTail 7 1 g c := (dvd_pow_self q (by decide : 2 ≠ 0)).trans hT2
    let hu := focused_norm_depth_guards hcop hEq hfocus hq7 hQ hT
    let J := nativeKernel a b c g hQ hu.2.1 hu.2.2.2.1 hu.2.2.2.2.1 hT
    (J = Ideal.map fromEisenstein
      (eisensteinResidueIdeal (gtailSevenResidueRoot q a b) (gtailSevenResidueRoot_polynomial hQ hu.2.1)) ⊔
      Ideal.map fromCyclotomic (seventhRootKernel (gtailSevenTailRatio q c g)
        (gtailSevenTailRatio_ne_zero hu.2.2.2.1 hT) (gtailSevenTailRatio_pow_seven hu.2.2.2.1 hT)
        (gtailSevenTailRatio_ne_one hu.2.2.2.1 hu.2.2.2.2.1))) ∧
    (J.IsMaximal ∧
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
      fromCyclotomic (gtailCyclotomicFactor c g 0) ∈ J ^ 4) :=
  tail_receiver ha hbpos hcop hEq hfocus hq7 hQ hT2

example (hcop : Nat.Coprime a b) (hEq : Fermat7Equation a b c)
    (hfocus : a + b = c + g) (hq7 : q ≠ 7)
    (hQ : q ∣ a ^ 2 + a * b + b ^ 2) (hT : q ∣ GTail 7 1 g c) :
    fromEisenstein (gtailSevenNormCoord a b) ≠ fromCyclotomic (gtailCyclotomicFactor c g 0) :=
  tail_source_images_ne hcop hEq hfocus hq7 hQ hT
example (r : ZMod q) (hr0 : r ≠ 0) (hr7 : r ^ 7 = 1) (hr1 : r ≠ 1)
    (hb : ¬ q ∣ b) (u : SevenCyclotomicDegreeSixInt.Ring) :
    fromEisenstein (gtailSevenNormCoord a b) ≠ fromCyclotomic u :=
  norm_image_ne_cyclotomic r hr0 hr7 hr1 a b hb u
example (hfocus : a + b = c + g) :
    Fermat7Equation a b c ↔ g * GTail 7 1 g c =
      7 * a * b * (a + b) * (a ^ 2 + a * b + b ^ 2) ^ 2 :=
  fermat7Equation_iff_focused_scalar_balance hfocus

end Symbolic

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

section GapControls

local instance : Fact (Nat.Prime 13) := ⟨by decide⟩
example : gtailSevenTailRatio 13 30 13 = 1 := gap_ratio_eq_one (by decide) (by decide)
example : ¬ (gtailSevenTailRatio 13 30 13 ≠ 1) :=
  gap_nonidentity_guard_unavailable (by decide) (by decide)
example : ¬ (13 : ℕ) ∣ 30 ∧ ¬ (13 : ℕ) ^ 2 ∣ 13 := by decide
example : ¬ Fermat7Equation 14 29 30 := by unfold Fermat7Equation; decide

end GapControls

section ArtificialSuppliedRoot

local instance : Fact (Nat.Prime 43) := ⟨by decide⟩
-- This supplied root differs from the actual Gap ratio; no native Tail tuple is asserted.
example : gtailSevenTailRatio 43 1 43 = 1 := gap_ratio_eq_one (by decide) (by decide)
example : (11 : ZMod 43) ≠ gtailSevenTailRatio 43 1 43 := by
  rw [gap_ratio_eq_one (by decide : ¬ (43 : ℕ) ∣ 1) (by decide : (43 : ℕ) ∣ 43)]
  decide
example : (pairedKernel (37 : ZMod 43) 11 (by decide) (by decide) (by decide) (by decide)).IsMaximal :=
  pairedKernel_isMaximal _ _ _ _ _ _
example : fromEisenstein (gtailSevenNormCoord 1166 1857) ≠
    fromCyclotomic (gtailCyclotomicFactor 1858 1165 0) :=
  norm_image_ne_cyclotomic (11 : ZMod 43) (by decide) (by decide) (by decide)
    1166 1857 (by decide) _
example : ¬ ((4 : ℕ) * GTail 7 1 4 9 = 7 * 5 * 8 * (5 + 8) * (5 ^ 2 + 5 * 8 + 8 ^ 2) ^ 2) :=
  by decide

end ArtificialSuppliedRoot

section RamifiedGap
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩
example : gtailSevenTailRatio 7 1 7 = 1 := gap_ratio_eq_one (by decide) (by decide)
end RamifiedGap

section RepeatedQuadraticGap
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩
example : gtailSevenTailRatio 3 1 3 = 1 := gap_ratio_eq_one (by decide) (by decide)
example : (2 : ZMod 3) ^ 2 - 2 + 1 = 0 := by decide
end RepeatedQuadraticGap

#check DkMath.FLT.Seven.GTailFocusedPrimeRoute.gap_ratio_eq_one
#print axioms DkMath.FLT.Seven.GTailFocusedPrimeRoute.gap_ratio_eq_one
#check DkMath.FLT.Seven.GTailFocusedPrimeRoute.gap_nonidentity_guard_unavailable
#print axioms DkMath.FLT.Seven.GTailFocusedPrimeRoute.gap_nonidentity_guard_unavailable
#check DkMath.FLT.Seven.GTailFocusedPrimeRoute.focused_coordinate_units
#print axioms DkMath.FLT.Seven.GTailFocusedPrimeRoute.focused_coordinate_units
#check DkMath.FLT.Seven.GTailFocusedPrimeRoute.focused_prime_route
#print axioms DkMath.FLT.Seven.GTailFocusedPrimeRoute.focused_prime_route
#check DkMath.FLT.Seven.GTailFocusedPrimeRoute.tail_receiver
#print axioms DkMath.FLT.Seven.GTailFocusedPrimeRoute.tail_receiver
#check DkMath.FLT.Seven.GTailFocusedPrimeRoute.norm_image_ne_cyclotomic
#print axioms DkMath.FLT.Seven.GTailFocusedPrimeRoute.norm_image_ne_cyclotomic
#check DkMath.FLT.Seven.GTailFocusedPrimeRoute.tail_source_images_ne
#print axioms DkMath.FLT.Seven.GTailFocusedPrimeRoute.tail_source_images_ne

end DkMathTest.FLT.Seven.GTailFocusedPrimeRoute
