/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenRealCubicThetaSeventhPower

#print "file: DkMath.FLT.Seven.SevenRamifiedThetaJetLifting"

namespace DkMath.FLT.Seven

open SevenRealCubicInt

local instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

private theorem linearBFactor_not_seven_dvd
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

private theorem squareCFactor_not_seven_dvd
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

/-- One division-free triangular theta-jet lift:
`(k,2k)` advances to `(k+1,2k+2)` while the source linear coordinate
still has total depth three. -/
theorem triangularJet_depth_step
    {A B C M sign : ℤ} (k : ℕ) (hk : k < 3)
    (hA : ¬(7 : ℤ) ∣ A)
    (hG : seventhThetaLinearQuotient A B C =
      sign * 7 ^ 3 * M ^ 7)
    (hH : seventhThetaSquareQuotient A B C = 0)
    (hB : (7 : ℤ) ^ k ∣ B)
    (hC : (7 : ℤ) ^ (2 * k) ∣ C) :
    (7 : ℤ) ^ (k + 1) ∣ B ∧
      (7 : ℤ) ^ (2 * (k + 1)) ∣ C := by
  let GB := seventhThetaLinearBFactor A B C
  let GC := seventhThetaLinearCFactor A C
  let HC := seventhThetaSquareCFactor A B C
  let HB := seventhThetaSquareBFactor A B
  have hGB : ¬(7 : ℤ) ∣ GB :=
    linearBFactor_not_seven_dvd hA
  have hHC : ¬(7 : ℤ) ∣ HC :=
    squareCFactor_not_seven_dvd hA
  have hD3 : (7 : ℤ) ^ (k + 1) ∣ (7 : ℤ) ^ 3 :=
    pow_dvd_pow 7 (by omega)
  have hDright :
      (7 : ℤ) ^ (k + 1) ∣ sign * 7 ^ 3 * M ^ 7 :=
    by
      simpa [mul_assoc] using
        dvd_mul_of_dvd_right
          (dvd_mul_of_dvd_left hD3 (M ^ 7)) sign
  have hDCsquare :
      (7 : ℤ) ^ (k + 1) ∣ 7 * C ^ 2 * GC := by
    interval_cases k
    · exact ⟨C ^ 2 * GC, by ring⟩
    · norm_num at hC ⊢
      rcases hC with ⟨c, hc⟩
      refine ⟨7 ^ 3 * c ^ 2 * GC, ?_⟩
      rw [hc]
      ring
    · norm_num at hC ⊢
      rcases hC with ⟨c, hc⟩
      refine ⟨7 ^ 6 * c ^ 2 * GC, ?_⟩
      rw [hc]
      ring
  have hDBG :
      (7 : ℤ) ^ (k + 1) ∣ B * GB := by
    have hsum :
        B * GB + 7 * C ^ 2 * GC =
          sign * 7 ^ 3 * M ^ 7 := by
      simpa [seventhThetaLinearQuotient, GB, GC] using hG
    rw [← hsum] at hDright
    convert dvd_sub hDright hDCsquare using 1
    all_goals first | rfl | ring
  have hcopGB : IsCoprime ((7 : ℤ) ^ (k + 1)) GB :=
    ((show Prime (7 : ℤ) by norm_num).coprime_iff_not_dvd.mpr hGB).pow_left
  have hBnext : (7 : ℤ) ^ (k + 1) ∣ B :=
    hcopGB.dvd_of_dvd_mul_right hDBG
  refine ⟨hBnext, ?_⟩
  have hDBsquare :
      (7 : ℤ) ^ (2 * (k + 1)) ∣ B ^ 2 := by
    have := pow_dvd_pow_of_dvd hBnext 2
    convert this using 1
    all_goals first | rfl | (rw [← pow_mul]; congr 1; omega)
  have hDCHC :
      (7 : ℤ) ^ (2 * (k + 1)) ∣ C * HC := by
    have hzero : C * HC + B ^ 2 * HB = 0 := by
      simpa [seventhThetaSquareQuotient, HC, HB] using hH
    have hBH :
        (7 : ℤ) ^ (2 * (k + 1)) ∣ B ^ 2 * HB :=
      dvd_mul_of_dvd_left hDBsquare HB
    have heq : C * HC = -(B ^ 2 * HB) := by
      linarith
    rw [heq]
    exact dvd_neg.mpr hBH
  have hcopHC : IsCoprime ((7 : ℤ) ^ (2 * (k + 1))) HC :=
    ((show Prime (7 : ℤ) by norm_num).coprime_iff_not_dvd.mpr hHC).pow_left
  exact hcopHC.dvd_of_dvd_mul_right hDCHC

/-- Three applications of the triangular step give the `(3,6)` lower
depths without introducing a valuation layer. -/
theorem triangularJet_depth_three_six
    {A B C M sign : ℤ}
    (hA : ¬(7 : ℤ) ∣ A)
    (hG : seventhThetaLinearQuotient A B C =
      sign * 7 ^ 3 * M ^ 7)
    (hH : seventhThetaSquareQuotient A B C = 0) :
    (7 : ℤ) ^ 3 ∣ B ∧ (7 : ℤ) ^ 6 ∣ C := by
  have h0 := triangularJet_depth_step 0 (by omega) hA hG hH
    (by simp) (by simp)
  have h1 := triangularJet_depth_step 1 (by omega) hA hG hH
    h0.1 (by simpa using h0.2)
  have h2 := triangularJet_depth_step 2 (by omega) hA hG hH
    (by simpa using h1.1) (by simpa using h1.2)
  simpa using h2

/-- Exact normalized output of the triangular lift. -/
structure TriangularThetaJetExactPacket
    (A B C M sign : ℤ) : Type where
  linearCore : ℤ
  squareCore : ℤ
  linear_eq : B = 7 ^ 3 * linearCore
  square_eq : C = 7 ^ 6 * squareCore
  linearCore_modSeven :
    (linearCore : ZMod 7) = (sign : ZMod 7) * (M : ZMod 7)
  quadraticJet_modSeven :
    ((A * squareCore + 3 * linearCore ^ 2 : ℤ) : ZMod 7) = 0
  linearCore_not_seven_dvd : ¬(7 : ℤ) ∣ linearCore
  squareCore_not_seven_dvd : ¬(7 : ℤ) ∣ squareCore

theorem nonempty_triangularThetaJetExact
    {A B C M sign : ℤ}
    (hA : ¬(7 : ℤ) ∣ A) (hM : ¬(7 : ℤ) ∣ M)
    (hsign : sign = 1 ∨ sign = -1)
    (hG : seventhThetaLinearQuotient A B C =
      sign * 7 ^ 3 * M ^ 7)
    (hH : seventhThetaSquareQuotient A B C = 0) :
    Nonempty (TriangularThetaJetExactPacket A B C M sign) := by
  rcases triangularJet_depth_three_six hA hG hH with
    ⟨⟨U, hU⟩, ⟨V, hV⟩⟩
  have hUint :
      U * seventhThetaLinearBFactor A B C +
          7 ^ 10 * V ^ 2 * seventhThetaLinearCFactor A C =
        sign * M ^ 7 := by
    apply mul_left_cancel₀ (by norm_num : (7 ^ 3 : ℤ) ≠ 0)
    calc
      7 ^ 3 *
          (U * seventhThetaLinearBFactor A B C +
            7 ^ 10 * V ^ 2 * seventhThetaLinearCFactor A C) =
          seventhThetaLinearQuotient A B C := by
            rw [hU, hV]
            simp [seventhThetaLinearQuotient]
            ring
      _ = sign * 7 ^ 3 * M ^ 7 := hG
      _ = 7 ^ 3 * (sign * M ^ 7) := by ring
  have hHint :
      V * seventhThetaSquareCFactor A B C +
          U ^ 2 * seventhThetaSquareBFactor A B = 0 := by
    apply mul_left_cancel₀ (by norm_num : (7 ^ 6 : ℤ) ≠ 0)
    calc
      7 ^ 6 *
          (V * seventhThetaSquareCFactor A B C +
            U ^ 2 * seventhThetaSquareBFactor A B) =
          seventhThetaSquareQuotient A B C := by
            rw [hU, hV]
            simp [seventhThetaSquareQuotient]
            ring
      _ = 0 := hH
      _ = 7 ^ 6 * 0 := by ring
  have hA0 : (A : ZMod 7) ≠ 0 := by
    intro hz
    exact hA ((ZMod.intCast_zmod_eq_zero_iff_dvd _ 7).mp hz)
  have hM0 : (M : ZMod 7) ≠ 0 := by
    intro hz
    exact hM ((ZMod.intCast_zmod_eq_zero_iff_dvd _ 7).mp hz)
  have hUmod :
      (U : ZMod 7) = (sign : ZMod 7) * (M : ZMod 7) := by
    have h := congrArg (fun z : ℤ => (z : ZMod 7)) hUint
    push_cast at h
    rw [seventhThetaLinearBFactor_modSeven,
      seventhThetaLinearCFactor_modSeven] at h
    have hbig : (282475249 : ZMod 7) = 0 := by decide
    simp only [hbig, zero_mul, add_zero] at h
    rw [ZMod.pow_card,
      ZMod.pow_card_sub_one_eq_one hA0,
      mul_one] at h
    exact h
  have hquad :
      ((A * V + 3 * U ^ 2 : ℤ) : ZMod 7) = 0 := by
    have h := congrArg (fun z : ℤ => (z : ZMod 7)) hHint
    push_cast at h
    rw [seventhThetaSquareCFactor_modSeven,
      seventhThetaSquareBFactor_modSeven] at h
    have hA5 : (A : ZMod 7) ^ 5 ≠ 0 := pow_ne_zero 5 hA0
    apply mul_left_cancel₀ hA5
    simpa [pow_succ, mul_add, mul_assoc, mul_left_comm,
      mul_comm] using h
  have hU0 : (U : ZMod 7) ≠ 0 := by
    rw [hUmod]
    rcases hsign with rfl | rfl <;>
      simp [hM0]
  have hV0 : (V : ZMod 7) ≠ 0 := by
    intro hVz
    have hq := hquad
    push_cast at hq
    rw [hVz, mul_zero, zero_add] at hq
    have hthree : (3 : ZMod 7) ≠ 0 := by decide
    exact hU0
      ((pow_eq_zero_iff (by norm_num : 2 ≠ 0)).mp
        (mul_eq_zero.mp hq |>.resolve_left hthree))
  exact ⟨{
    linearCore := U
    squareCore := V
    linear_eq := hU
    square_eq := hV
    linearCore_modSeven := hUmod
    quadraticJet_modSeven := hquad
    linearCore_not_seven_dvd := by
      intro hd
      exact hU0 ((ZMod.intCast_zmod_eq_zero_iff_dvd _ 7).mpr hd)
    squareCore_not_seven_dvd := by
      intro hd
      exact hV0 ((ZMod.intCast_zmod_eq_zero_iff_dvd _ 7).mpr hd) }⟩

/-- Determinant of the modulo-seven Jacobian of the normalized triangular
jet equations in the variables `(U,V)`. -/
def triangularJetJacobianDet (A U : ZMod 7) : ZMod 7 :=
  A ^ 6 * A ^ 6 - 0 * (6 * A ^ 5 * U)

theorem triangularJetJacobianDet_eq
    (A U : ZMod 7) :
    triangularJetJacobianDet A U = A ^ 12 := by
  simp [triangularJetJacobianDet]
  ring

theorem triangularJetJacobianDet_ne_zero
    {A U : ZMod 7} (hA : A ≠ 0) :
    triangularJetJacobianDet A U ≠ 0 := by
  rw [triangularJetJacobianDet_eq]
  exact pow_ne_zero 12 hA

#print axioms triangularJet_depth_step
#print axioms triangularJet_depth_three_six
#print axioms nonempty_triangularThetaJetExact
#print axioms triangularJetJacobianDet_ne_zero

end DkMath.FLT.Seven
