/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Kummer.SevenRealUnitObstruction

#print "file: DkMath.FLT.Kummer.SevenRealPrimaryUnit"

/-!
# 実三次係数との一次合同が消す障害、残す障害

`delta ≡ ofReal(b) mod 7` は共役位相を消すが、実ノルムの二成分を自動では消さない。
整数合同による単元補題の入力と混同せず、任意の実三次係数を保持する。
-/

namespace DkMath.FLT.Kummer.SevenRealGN

open scoped NumberField
open DkMath.FLT.Seven DkMath.FLT.Kummer.SevenPrimaryNorm

noncomputable section

/-- 実三次係数 b と mod 7 で合同な六次単元。b の単元性は仮定しない。 -/
def RealPrimary (u : Cˣ) (b : R) : Prop :=
  (7 : C) ∣ (u : C) - SevenCyclotomicDegreeSixInt.ofReal b

/-- 実係数は二次共役で固定される。 -/
theorem star_ofReal (b : R) :
    star (SevenCyclotomicDegreeSixInt.ofReal b) = SevenCyclotomicDegreeSixInt.ofReal b := by
  apply QuadraticAlgebra.ext <;> simp [SevenCyclotomicDegreeSixInt.ofReal, QuadraticAlgebra.algebraMap_eq]

/-- 具体的六次環に運んだ ±ζ^i の mod 7 識別。任意の元を七乗と仮定しない。 -/
theorem signed_root_eq_one_of_congruent (r : Cˣ)
    (hr : ∃ i < 7, r = SevenCyclotomicDegreeSixInt.zetaUnit ^ i ∨
      r = -SevenCyclotomicDegreeSixInt.zetaUnit ^ i)
    (hd : (7 : C) ∣ (r : C) - 1) : r = 1 := by
  have hz : integralEquiv.symm SevenCyclotomicDegreeSixInt.zeta = septicRoot_spec.toInteger := by
    apply integralEquiv.injective
    rw [RingEquiv.apply_symm_apply, integralEquiv_septicRoot]
  have hm := map_dvd integralEquiv.symm.toRingHom hd
  change integralEquiv.symm (7 : C) ∣ integralEquiv.symm ((r : C) - 1) at hm
  have h7 : (7 : 𝓞 (CyclotomicField 7 ℚ)) ∣ integralEquiv.symm (r : C) - 1 := by
    simpa only [map_ofNat, map_sub, map_one] using hm
  have hx : ∃ i < 7, integralEquiv.symm (r : C) = septicRoot_spec.toInteger ^ i ∨
      integralEquiv.symm (r : C) = -septicRoot_spec.toInteger ^ i := by
    obtain ⟨i, hi, h | h⟩ := hr
    · refine ⟨i, hi, Or.inl ?_⟩
      have hv : (r : C) = SevenCyclotomicDegreeSixInt.zeta ^ i := congrArg Units.val h
      simpa only [map_pow, hz] using congrArg integralEquiv.symm hv
    · refine ⟨i, hi, Or.inr ?_⟩
      have hv : (r : C) = -SevenCyclotomicDegreeSixInt.zeta ^ i := congrArg Units.val h
      simpa only [map_neg, map_pow, hz] using congrArg integralEquiv.symm hv
  apply Units.ext
  change (r : C) = 1
  apply integralEquiv.symm.injective
  simpa only [map_one] using septic_rootOfUnity_eq_one_of_congruent hx h7

/-- 実係数との合同から共役比も1と合同になる。分母は単元であり b で割らない。 -/
theorem unitRatio_congruent_one_of_realPrimary (u : Cˣ) (b : R) (h : RealPrimary u b) :
    (7 : C) ∣ (unitRatio u : C) - 1 := by
  have hm := map_dvd (starRingAut : C ≃+* C).toRingHom h
  have hc : (7 : C) ∣ star (u : C) - SevenCyclotomicDegreeSixInt.ofReal b := by
    change star (7 : C) ∣ star ((u : C) - SevenCyclotomicDegreeSixInt.ofReal b) at hm
    simpa only [star_ofNat, star_sub, star_ofReal] using hm
  have hd : (7 : C) ∣ (u : C) - (unitConj u : C) := by
    change (7 : C) ∣ (u : C) - star (u : C)
    convert dvd_sub h hc using 1
    ring
  convert dvd_mul_of_dvd_left hd (↑(unitConj u)⁻¹ : C) using 1
  change (u : C) * (↑(unitConj u)⁻¹ : C) - 1 =
    ((u : C) - (unitConj u : C)) * (↑(unitConj u)⁻¹ : C)
  rw [sub_mul]
  have hh : (unitConj u : C) * (↑(unitConj u)⁻¹ : C) = 1 := (unitConj u).val_inv
  rw [hh]

/-- 実三次一次合同は共役位相そのものを固定する。整数係数への降下は使わない。 -/
theorem unitRatio_eq_one_of_realPrimary (u : Cˣ) (b : R) (h : RealPrimary u b) : unitRatio u = 1 :=
  signed_root_eq_one_of_congruent _ (unitRatio_signed_root u)
    (unitRatio_congruent_one_of_realPrimary u b h)

/-- 実三次一次単元では位相障害は消える。ノルム障害の零性は別条件として残る。 -/
theorem realPrimary_phase_eq_one (u : Cˣ) (b : R) (h : RealPrimary u b) : phaseCharacter u = 1 := by
  apply Subtype.ext
  change unitRatio u ^ 8 = 1
  rw [unitRatio_eq_one_of_realPrimary u b h, one_pow]

/-- 実三次一次単元の七乗性を決めるのは、残ったノルムの二成分である。 -/
theorem realPrimary_seventh_iff_norm_zero (u : Cˣ) (b : R) (h : RealPrimary u b) :
    (∃ k : Cˣ, u = k ^ 7) ↔ normCoordinates u = 0 := by
  rw [unit_seventh_iff_obstruction]
  exact and_iff_left (realPrimary_phase_eq_one u b h)

/-- 実三次係数の合同を二次ノルムに移す有限恒等式。合同先は b² になる。 -/
theorem relativeNorm_congruent_real {x : C} {b : R}
    (h : (7 : C) ∣ x - SevenCyclotomicDegreeSixInt.ofReal b) :
    (7 : R) ∣ relativeNorm x - b ^ 2 := by
  obtain ⟨w, hw⟩ := h
  have hx : x = SevenCyclotomicDegreeSixInt.ofReal b + 7 * w := by linear_combination hw
  refine ⟨b * (2 * w.re + (SevenRealCubicInt.alpha - 1) * w.im) + 7 * relativeNorm w, ?_⟩
  rw [hx]
  simp only [relativeNorm, QuadraticAlgebra.norm_def, SevenCyclotomicDegreeSixInt.ofReal,
    QuadraticAlgebra.algebraMap_eq, QuadraticAlgebra.re_add, QuadraticAlgebra.im_add,
    QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat]
  ring

/-- 係数を整数と取り違えると消してしまう、具体的な残留障害。 -/
def alphaEmbeddedUnit : Cˣ := Units.map SevenCyclotomicDegreeSixInt.ofReal.toMonoidHom SevenRealCubicInt.alphaUnit

/-- 埋め込んだ alpha は実三次一次単元である。仮想的な FLT 解を使わない実例。 -/
theorem alphaEmbeddedUnit_primary : RealPrimary alphaEmbeddedUnit SevenRealCubicInt.alpha := by
  change (7 : C) ∣ SevenCyclotomicDegreeSixInt.ofReal (SevenRealCubicInt.alphaUnit : R) -
    SevenCyclotomicDegreeSixInt.ofReal SevenRealCubicInt.alpha
  rw [SevenRealCubicInt.alphaUnit_val, sub_self]
  exact dvd_zero _

/-- alpha の実ノルム障害は (3,3)。位相は消えても二成分は非零のまま残る。 -/
theorem alphaEmbeddedUnit_normCoordinates : normCoordinates alphaEmbeddedUnit = (3, 3) := by
  have hn : Units.map relativeNorm alphaEmbeddedUnit = SevenRealCubicInt.alphaUnit ^ 2 := by
    apply Units.ext
    change QuadraticAlgebra.norm (SevenCyclotomicDegreeSixInt.ofReal (SevenRealCubicInt.alphaUnit : R)) = _
    exact QuadraticAlgebra.norm_algebraMap _
  unfold normCoordinates
  rw [hn, ofMul_pow, map_nsmul, SevenRealCubicInt.projectiveLog_alpha]
  decide +kernel

/-- 実三次一次合同だけでは七乗性は得られない、実際の単元の反例。 -/
theorem alphaEmbeddedUnit_not_seventh : ¬ ∃ k : Cˣ, alphaEmbeddedUnit = k ^ 7 := by
  intro hk
  have hz := (unit_seventh_iff_obstruction alphaEmbeddedUnit).mp hk
  rw [alphaEmbeddedUnit_normCoordinates] at hz
  have hf := congrArg Prod.fst hz.1
  exact (by decide : (3 : ZMod 7) ≠ 0) hf

end

end DkMath.FLT.Kummer.SevenRealGN
