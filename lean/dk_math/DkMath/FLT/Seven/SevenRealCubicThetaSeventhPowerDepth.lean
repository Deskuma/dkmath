/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.FLT.Seven.SevenRealCubicUnitClass
import DkMath.FLT.Seven.SevenRealCubicThetaSeventhPower

#print "file: DkMath.FLT.Seven.SevenRealCubicThetaSeventhPowerDepth"

namespace DkMath.FLT.Seven

open SevenRealCubicInt

noncomputable section

local instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

/-- Simultaneous 7-adic divisibility of the two nilpotent theta
coordinates.  This is a finite-depth predicate, not a valuation. -/
def ThetaNilpotentDepth (n : ℕ) (x : SevenRealCubicInt) : Prop :=
  (7 : ℤ) ^ n ∣ thetaLinearInt x ∧
    (7 : ℤ) ^ n ∣ thetaSquareInt x

theorem thetaNilpotentDepth_mono {m n : ℕ} (hmn : m ≤ n)
    {x : SevenRealCubicInt} :
    ThetaNilpotentDepth n x → ThetaNilpotentDepth m x := by
  intro h
  exact ⟨dvd_trans (pow_dvd_pow 7 hmn) h.1,
    dvd_trans (pow_dvd_pow 7 hmn) h.2⟩

theorem seventhThetaLinearBFactor_not_seven_dvd
    {A B C : ℤ} (hA : ¬(7 : ℤ) ∣ A) :
    ¬(7 : ℤ) ∣ seventhThetaLinearBFactor A B C := by
  intro h
  have hz :
      (seventhThetaLinearBFactor A B C : ZMod 7) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ 7).mpr h
  rw [seventhThetaLinearBFactor_modSeven] at hz
  have hA0 : (A : ZMod 7) = 0 :=
    (pow_eq_zero_iff (by norm_num : 6 ≠ 0)).mp hz
  exact hA ((ZMod.intCast_zmod_eq_zero_iff_dvd _ 7).mp hA0)

theorem seventhThetaSquareCFactor_not_seven_dvd
    {A B C : ℤ} (hA : ¬(7 : ℤ) ∣ A) :
    ¬(7 : ℤ) ∣ seventhThetaSquareCFactor A B C := by
  intro h
  have hz :
      (seventhThetaSquareCFactor A B C : ZMod 7) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ 7).mpr h
  rw [seventhThetaSquareCFactor_modSeven] at hz
  have hA0 : (A : ZMod 7) = 0 :=
    (pow_eq_zero_iff (by norm_num : 6 ≠ 0)).mp hz
  exact hA ((ZMod.intCast_zmod_eq_zero_iff_dvd _ 7).mp hA0)

private theorem ofInt_pow (a : ℤ) (n : ℕ) :
    ofInt (a ^ n) = (ofInt a : SevenRealCubicInt) ^ n := by
  induction n with
  | zero =>
      simp only [pow_zero]
      apply SevenRealCubicInt.ext <;> rfl
  | succ n ih =>
      rw [pow_succ, pow_succ, ← ih]
      apply SevenRealCubicInt.ext <;>
        norm_num [ofInt, SevenRealCubicInt.mul]

theorem eisensteinAxis_pow_three_mul_dvd_imp_ofInt_pow
    {m : ℕ} {x : SevenRealCubicInt}
    (hx : eisensteinAxis ^ (3 * m) ∣ x) :
    ofInt ((7 : ℤ) ^ m) ∣ x := by
  rcases hx with ⟨c, hc⟩
  let t : SevenRealCubicIntˣ := thetaSevenUnit_isUnit.unit
  have hseven : (7 : SevenRealCubicInt) =
      eisensteinAxis ^ 3 * (t : SevenRealCubicInt) := by
    simpa [t] using seven_eq_eisensteinAxis_cube_mul_unit
  have hpow : ofInt ((7 : ℤ) ^ m) =
      eisensteinAxis ^ (3 * m) * (t : SevenRealCubicInt) ^ m := by
    rw [ofInt_pow]
    change (7 : SevenRealCubicInt) ^ m = _
    rw [hseven]
    rw [mul_pow, ← pow_mul]
  have hinv : (t : SevenRealCubicInt) ^ m *
      ((t⁻¹ : SevenRealCubicIntˣ) : SevenRealCubicInt) ^ m = 1 := by
    rw [← mul_pow, ← Units.val_mul]
    simp
  refine ⟨((t⁻¹ : SevenRealCubicIntˣ) : SevenRealCubicInt) ^ m * c, ?_⟩
  rw [hpow, hc]
  calc
    eisensteinAxis ^ (3 * m) * c =
        eisensteinAxis ^ (3 * m) * 1 * c := by simp
    _ = eisensteinAxis ^ (3 * m) *
        ((t : SevenRealCubicInt) ^ m *
          (((t⁻¹ : SevenRealCubicIntˣ) : SevenRealCubicInt) ^ m)) * c := by
      rw [hinv]
    _ = eisensteinAxis ^ (3 * m) *
        ((t : SevenRealCubicInt) ^ m *
          (((t⁻¹ : SevenRealCubicIntˣ) : SevenRealCubicInt) ^ m * c)) := by
      ring
    _ = eisensteinAxis ^ (3 * m) * (t : SevenRealCubicInt) ^ m *
        (((t⁻¹ : SevenRealCubicIntˣ) : SevenRealCubicInt) ^ m * c) := by
      rw [mul_assoc]

set_option maxHeartbeats 2000000 in
-- The recursive divisibility induction needs more elaboration time than the default.
theorem thetaNilpotentDepth_pow_seven_drop
    (x : SevenRealCubicInt) (n : ℕ)
    (hA : ¬(7 : ℤ) ∣ thetaConstInt x)
    (hdepth : ThetaNilpotentDepth (n + 1) (x ^ 7)) :
    ThetaNilpotentDepth n x := by
  let A : ℤ := thetaConstInt x
  let B : ℤ := thetaLinearInt x
  let C : ℤ := thetaSquareInt x
  have hx : x = ofThetaCoordinates A B C := by
    exact theta_coordinate_decomposition x
  have hlin : thetaLinearInt (x ^ 7) =
      7 * seventhThetaLinearQuotient A B C := by
    rw [hx]
    exact thetaLinear_pow_seven A B C
  have hsq : thetaSquareInt (x ^ 7) =
      7 * seventhThetaSquareQuotient A B C := by
    rw [hx]
    exact thetaSquare_pow_seven A B C
  revert hdepth
  induction n with
  | zero =>
      intro _
      constructor <;> simp
  | succ n ih =>
      intro hdepth
      have hweak : ThetaNilpotentDepth (n + 1) (x ^ 7) :=
        thetaNilpotentDepth_mono (Nat.le_succ (n + 1)) hdepth
      have hprev := ih hweak
      have hBprev : (7 : ℤ) ^ n ∣ B := by simpa [A, B] using hprev.1
      have hCprev : (7 : ℤ) ^ n ∣ C := by simpa [A, B, C] using hprev.2
      have hQlin : (7 : ℤ) ^ (n + 1) ∣
          seventhThetaLinearQuotient A B C := by
        rcases hdepth.1 with ⟨q, hq⟩
        refine ⟨q, ?_⟩
        rw [hlin] at hq
        apply mul_left_cancel₀ (by norm_num : (7 : ℤ) ≠ 0)
        have hp : (7 : ℤ) ^ (n + 1 + 1) =
            7 * (7 : ℤ) ^ (n + 1) := by
          rw [show n + 1 + 1 = (n + 1) + 1 by omega, pow_succ]
          ring
        rw [hq, hp]
        ring
      let GB := seventhThetaLinearBFactor A B C
      let GC := seventhThetaLinearCFactor A C
      have hterm : (7 : ℤ) ^ (n + 1) ∣ 7 * C ^ 2 * GC := by
        rcases hCprev with ⟨c, hc⟩
        refine ⟨(7 : ℤ) ^ n * c ^ 2 * GC, ?_⟩
        rw [hc, pow_succ]
        ring
      have hprod : (7 : ℤ) ^ (n + 1) ∣ B * GB := by
        have hsum : B * GB + 7 * C ^ 2 * GC =
            seventhThetaLinearQuotient A B C := by
          rfl
        rw [← hsum] at hQlin
        convert dvd_sub hQlin hterm using 1
        ring
      have hcop : IsCoprime ((7 : ℤ) ^ (n + 1)) GB :=
        ((show Prime (7 : ℤ) by norm_num).coprime_iff_not_dvd.mpr
          (seventhThetaLinearBFactor_not_seven_dvd hA)).pow_left
      have hBnext : (7 : ℤ) ^ (n + 1) ∣ B :=
        hcop.dvd_of_dvd_mul_right hprod
      have hQsq : (7 : ℤ) ^ (n + 1) ∣
          seventhThetaSquareQuotient A B C := by
        rcases hdepth.2 with ⟨q, hq⟩
        refine ⟨q, ?_⟩
        rw [hsq] at hq
        apply mul_left_cancel₀ (by norm_num : (7 : ℤ) ≠ 0)
        have hp : (7 : ℤ) ^ (n + 1 + 1) =
            7 * (7 : ℤ) ^ (n + 1) := by
          rw [show n + 1 + 1 = (n + 1) + 1 by omega, pow_succ]
          ring
        rw [hq, hp]
        ring
      let HC := seventhThetaSquareCFactor A B C
      let HB := seventhThetaSquareBFactor A B
      have hBsq : (7 : ℤ) ^ (n + 1) ∣ B ^ 2 := by
        simpa [pow_two] using (dvd_mul_of_dvd_left hBnext B)
      have hprodC : (7 : ℤ) ^ (n + 1) ∣ C * HC := by
        have hsum : C * HC + B ^ 2 * HB =
            seventhThetaSquareQuotient A B C := by
          rfl
        have hBterm : (7 : ℤ) ^ (n + 1) ∣ B ^ 2 * HB :=
          dvd_mul_of_dvd_left hBsq HB
        have heq : C * HC =
            seventhThetaSquareQuotient A B C - B ^ 2 * HB := by
          linarith [hsum]
        rw [heq]
        exact dvd_sub hQsq hBterm
      have hcopC : IsCoprime ((7 : ℤ) ^ (n + 1)) HC :=
        ((show Prime (7 : ℤ) by norm_num).coprime_iff_not_dvd.mpr
          (seventhThetaSquareCFactor_not_seven_dvd hA)).pow_left
      have hCnext : (7 : ℤ) ^ (n + 1) ∣ C :=
        hcopC.dvd_of_dvd_mul_right hprodC
      exact ⟨by simpa [B] using hBnext, by simpa [C] using hCnext⟩

theorem thetaNilpotentDepth_one_projectiveLog_zero
    (u : SevenRealCubicIntˣ)
    (hdepth : ThetaNilpotentDepth 1 (u : SevenRealCubicInt)) :
    projectiveLog (Additive.ofMul u) = 0 := by
  have hlin : thetaLinearModSeven (u : SevenRealCubicInt) = 0 := by
    change ((thetaLinearInt (u : SevenRealCubicInt) : ℤ) : ZMod 7) = 0
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 7).mpr hdepth.1
  have hsq : thetaSquareModSeven (u : SevenRealCubicInt) = 0 := by
    change ((thetaSquareInt (u : SevenRealCubicInt) : ℤ) : ZMod 7) = 0
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 7).mpr hdepth.2
  have hx : unitNilpotentX u = 0 := by
    simp [unitNilpotentX, hlin]
  have hy : unitNilpotentY u = 0 := by
    simp [unitNilpotentY, hsq]
  rw [projectiveLog_apply]
  simp [hx, hy]

theorem thetaNilpotentDepth_one_unit_is_seventh_power
    (u : SevenRealCubicIntˣ)
    (hdepth : ThetaNilpotentDepth 1 (u : SevenRealCubicInt)) :
    ∃ r : SevenRealCubicIntˣ, u = r ^ 7 := by
  apply (SevenRealCubic.unit_isSeventhPower_iff_projectiveLog_eq_zero u).mpr
  exact thetaNilpotentDepth_one_projectiveLog_zero u hdepth

theorem unit_is_pow_seven_pow_of_inverse_depth
    (u : SevenRealCubicIntˣ) (n : ℕ)
    (hdepth : ThetaNilpotentDepth n
      ((u⁻¹ : SevenRealCubicIntˣ) : SevenRealCubicInt)) :
    ∃ t : SevenRealCubicIntˣ, u = t ^ (7 ^ n) := by
  revert u
  induction n with
  | zero =>
      intro u _
      refine ⟨u, ?_⟩
      simp
  | succ n ih =>
      intro u hdepth
      have hone : ThetaNilpotentDepth 1
          ((u⁻¹ : SevenRealCubicIntˣ) : SevenRealCubicInt) :=
        thetaNilpotentDepth_mono (Nat.succ_le_succ (Nat.zero_le n)) hdepth
      obtain ⟨r, hr⟩ := thetaNilpotentDepth_one_unit_is_seventh_power
        u⁻¹ hone
      let s : SevenRealCubicIntˣ := r⁻¹
      have hus : u = s ^ 7 := by
        calc
          u = (u⁻¹)⁻¹ := by simp
          _ = (r ^ 7)⁻¹ := by rw [hr]
          _ = s ^ 7 := by simp [s, inv_pow]
      have hrdepth : ThetaNilpotentDepth n (r : SevenRealCubicInt) := by
        apply thetaNilpotentDepth_pow_seven_drop r n
        · intro hdiv
          apply (thetaConstModSeven_unit_ne_zero r)
          change ((thetaConstInt (r : SevenRealCubicInt) : ℤ) : ZMod 7) = 0
          exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 7).mpr hdiv
        simpa only [Units.val_pow_eq_pow_val, hr] using hdepth
      have hs_inv : s⁻¹ = r := by simp [s]
      obtain ⟨t, ht⟩ := ih s (by
        rw [hs_inv]
        exact hrdepth)
      refine ⟨t, ?_⟩
      calc
        u = s ^ 7 := hus
        _ = (t ^ (7 ^ n)) ^ 7 := by rw [ht]
        _ = t ^ (7 ^ n * 7) := by rw [← pow_mul]
        _ = t ^ (7 ^ (n + 1)) := by
          congr 1

end
end DkMath.FLT.Seven
