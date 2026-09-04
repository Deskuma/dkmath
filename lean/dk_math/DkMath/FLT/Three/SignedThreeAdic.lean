/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Three.EisensteinSubstrate
import DkMath.Petal.GcdBridge

#print "file: DkMath.FLT.Three.SignedThreeAdic"

namespace DkMath.FLT.Three

open DkMath.FLT
open DkMath.FLT.PetalDetect
open DkMath.NumberTheory.TraceOneQuadratic
open DkMath.Petal

/-!
# Signed three-adic routing

This module only performs the mod-nine routing and packages the resulting
positive factorization in the fixed trace-one Eisenstein coordinates.  It does
not divide by the ramifier or construct a descent.
-/

/-- The subtraction-safe natural form of `a^2 - a*b + b^2`. -/
def signedThreeAdicResidual (a b : ℕ) : ℕ := a ^ 2 + b ^ 2 - a * b

/-- The three possible locations of the ramified factor in a primitive triple. -/
inductive SignedThreeAdicOrientation where
  | a
  | b
  | c
  deriving DecidableEq, Repr

/-- The common signed packet produced by the mod-nine routing. -/
structure SignedThreeAdicPacket (a b c : ℕ) : Type where
  orientation : SignedThreeAdicOrientation
  carrier : ℕ
  residual : ℕ
  distinguished : ℕ
  alpha : EisensteinInt
  carrier_pos : 0 < carrier
  residual_pos : 0 < residual
  distinguished_pos : 0 < distinguished
  factorization : carrier * residual = distinguished ^ 3
  alpha_norm : norm alpha = (residual : ℤ)
  alpha_signed_gap : alpha.snd - alpha.fst = (carrier : ℤ)
  three_dvd_carrier : 3 ∣ carrier
  three_dvd_distinguished : 3 ∣ distinguished
  residual_mod_nine : residual % 9 = 3
  gcd_eq_three : Nat.gcd carrier residual = 3

private theorem mod_nine_at_least_one_divisible_by_three :
    ∀ x y z : Fin 9,
      (x.1 ^ 3 + y.1 ^ 3) % 9 = z.1 ^ 3 % 9 →
      3 ∣ x.1 ∨ 3 ∣ y.1 ∨ 3 ∣ z.1 := by
  decide +kernel

private theorem mod_nine_difference_residual :
    ∀ x y : Fin 9,
      ¬ 3 ∣ x.1 → ¬ 3 ∣ y.1 →
      x.1 ^ 3 % 9 = y.1 ^ 3 % 9 →
      (x.1 ^ 2 + x.1 * y.1 + y.1 ^ 2) % 9 = 3 ∧
        x.1 % 3 = y.1 % 3 := by
  decide +kernel

private theorem mod_nine_sum_residual :
    ∀ x y : Fin 9,
      ¬ 3 ∣ x.1 → ¬ 3 ∣ y.1 →
      (x.1 ^ 3 + y.1 ^ 3) % 9 = 0 →
      (x.1 ^ 2 + y.1 ^ 2 - x.1 * y.1) % 9 = 3 ∧
        (x.1 + y.1) % 3 = 0 := by
  decide +kernel

private theorem mod_nine_cube_zero_iff_three_dvd {x : ℕ} :
    x ^ 3 % 9 = 0 ↔ 3 ∣ x := by
  constructor
  · intro hx
    have h9 : 9 ∣ x ^ 3 := Nat.dvd_of_mod_eq_zero hx
    exact Nat.prime_three.dvd_of_dvd_pow
      (dvd_trans (by norm_num : 3 ∣ 9) h9)
  · rintro ⟨k, rfl⟩
    apply Nat.mod_eq_zero_of_dvd
    refine ⟨3 * k ^ 3, ?_⟩
    ring

private theorem exact_one_three_dvd_of_fermat_cube
    {a b c : ℕ} (hEq : a ^ 3 + b ^ 3 = c ^ 3)
    (hab : Nat.Coprime a b) :
    (3 ∣ a ∧ ¬ 3 ∣ b ∧ ¬ 3 ∣ c) ∨
      (¬ 3 ∣ a ∧ 3 ∣ b ∧ ¬ 3 ∣ c) ∨
        (¬ 3 ∣ a ∧ ¬ 3 ∣ b ∧ 3 ∣ c) := by
  have hEqMod :
      ((a % 9) ^ 3 + (b % 9) ^ 3) % 9 = c ^ 3 % 9 := by
    have h := congrArg (fun n : ℕ => n % 9) hEq
    simpa [Nat.add_mod, Nat.pow_mod] using h
  have hsome : 3 ∣ a ∨ 3 ∣ b ∨ 3 ∣ c := by
    let ar : Fin 9 := ⟨a % 9, Nat.mod_lt _ (by decide)⟩
    let br : Fin 9 := ⟨b % 9, Nat.mod_lt _ (by decide)⟩
    let cr : Fin 9 := ⟨c % 9, Nat.mod_lt _ (by decide)⟩
    have hf := mod_nine_at_least_one_divisible_by_three ar br cr
    have hfinite : 3 ∣ ar.1 ∨ 3 ∣ br.1 ∨ 3 ∣ cr.1 := by
      apply hf
      have hcmod : c ^ 3 % 9 = (c % 9) ^ 3 % 9 := by
        rw [Nat.pow_mod]
      simpa [ar, br, cr] using hEqMod.trans hcmod
    rcases hfinite with h | h | h
    · exact Or.inl ((Nat.dvd_mod_iff (by norm_num : 3 ∣ 9)).mp h)
    · exact Or.inr (Or.inl ((Nat.dvd_mod_iff (by norm_num : 3 ∣ 9)).mp h))
    · exact Or.inr (Or.inr ((Nat.dvd_mod_iff (by norm_num : 3 ∣ 9)).mp h))
  have hnotboth_ab : ¬ (3 ∣ a ∧ 3 ∣ b) := by
    rintro ⟨ha, hb⟩
    exact (Nat.not_coprime_of_dvd_of_dvd (by norm_num : 1 < 3) ha hb) hab
  have hnotboth_ac : ¬ (3 ∣ a ∧ 3 ∣ c) := by
    rintro ⟨ha, hc⟩
    have ha3 : 3 ∣ a ^ 3 := ha.trans (dvd_pow_self a (by decide))
    have hc3 : 3 ∣ c ^ 3 := hc.trans (dvd_pow_self c (by decide))
    have hb3 : 3 ∣ b ^ 3 := by
      have hsub : c ^ 3 - a ^ 3 = b ^ 3 := by omega
      simpa [hsub] using (Nat.dvd_sub hc3 ha3)
    have hb : 3 ∣ b := Nat.prime_three.dvd_of_dvd_pow hb3
    exact (Nat.not_coprime_of_dvd_of_dvd (by norm_num : 1 < 3) ha hb) hab
  have hnotboth_bc : ¬ (3 ∣ b ∧ 3 ∣ c) := by
    rintro ⟨hb, hc⟩
    have hb3 : 3 ∣ b ^ 3 := hb.trans (dvd_pow_self b (by decide))
    have hc3 : 3 ∣ c ^ 3 := hc.trans (dvd_pow_self c (by decide))
    have ha3 : 3 ∣ a ^ 3 := by
      have hsub : c ^ 3 - b ^ 3 = a ^ 3 := by omega
      simpa [hsub] using (Nat.dvd_sub hc3 hb3)
    have ha : 3 ∣ a := Nat.prime_three.dvd_of_dvd_pow ha3
    exact (Nat.not_coprime_of_dvd_of_dvd (by norm_num : 1 < 3) ha hb) hab
  by_cases ha : 3 ∣ a
  · have hnb : ¬ 3 ∣ b := by
      intro hb
      exact hnotboth_ab ⟨ha, hb⟩
    have hnc : ¬ 3 ∣ c := by
      intro hc
      exact hnotboth_ac ⟨ha, hc⟩
    exact Or.inl ⟨ha, hnb, hnc⟩
  · by_cases hb : 3 ∣ b
    · have hnc : ¬ 3 ∣ c := by
        intro hc
        exact hnotboth_bc ⟨hb, hc⟩
      exact Or.inr (Or.inl ⟨ha, hb, hnc⟩)
    · have hc : 3 ∣ c := by
        rcases hsome with h | h | h
        · exact (ha h).elim
        · exact (hb h).elim
        · exact h
      exact Or.inr (Or.inr ⟨ha, hb, hc⟩)

private theorem residual_mod_nine_difference
    {x y : ℕ} (hx : ¬ 3 ∣ x) (hy : ¬ 3 ∣ y)
    (hxy : x ^ 3 % 9 = y ^ 3 % 9) :
    (x ^ 2 + x * y + y ^ 2) % 9 = 3 ∧ x % 3 = y % 3 := by
  let xr : Fin 9 := ⟨x % 9, Nat.mod_lt _ (by decide)⟩
  let yr : Fin 9 := ⟨y % 9, Nat.mod_lt _ (by decide)⟩
  have hx' : ¬ 3 ∣ xr.1 := by
    intro h
    exact hx ((Nat.dvd_mod_iff (by norm_num : 3 ∣ 9)).mp h)
  have hy' : ¬ 3 ∣ yr.1 := by
    intro h
    exact hy ((Nat.dvd_mod_iff (by norm_num : 3 ∣ 9)).mp h)
  have hxy' : xr.1 ^ 3 % 9 = yr.1 ^ 3 % 9 := by
    simpa [xr, yr, Nat.pow_mod] using hxy
  have hf := mod_nine_difference_residual xr yr hx' hy' hxy'
  constructor
  · have hmod :
        x ^ 2 + x * y + y ^ 2 ≡
          xr.1 ^ 2 + xr.1 * yr.1 + yr.1 ^ 2 [MOD 9] := by
      simpa [xr, yr, add_assoc] using
        (((Nat.mod_modEq x 9).symm.pow 2).add
          ((Nat.mod_modEq x 9).symm.mul (Nat.mod_modEq y 9).symm)).add
            ((Nat.mod_modEq y 9).symm.pow 2)
    simpa [Nat.ModEq, hf.1] using hmod
  · simpa [xr, yr, Nat.ModEq] using hf.2

private theorem residual_mod_nine_sum
    {x y : ℕ} (hx : ¬ 3 ∣ x) (hy : ¬ 3 ∣ y)
    (hxy : (x ^ 3 + y ^ 3) % 9 = 0) :
    signedThreeAdicResidual x y % 9 = 3 ∧ (x + y) % 3 = 0 := by
  let xr : Fin 9 := ⟨x % 9, Nat.mod_lt _ (by decide)⟩
  let yr : Fin 9 := ⟨y % 9, Nat.mod_lt _ (by decide)⟩
  have hx' : ¬ 3 ∣ xr.1 := by
    intro h
    exact hx ((Nat.dvd_mod_iff (by norm_num : 3 ∣ 9)).mp h)
  have hy' : ¬ 3 ∣ yr.1 := by
    intro h
    exact hy ((Nat.dvd_mod_iff (by norm_num : 3 ∣ 9)).mp h)
  have hxy' : (xr.1 ^ 3 + yr.1 ^ 3) % 9 = 0 := by
    simpa [xr, yr, Nat.add_mod, Nat.pow_mod] using hxy
  have hf := mod_nine_sum_residual xr yr hx' hy' hxy'
  constructor
  · have hab_le : x * y ≤ x ^ 2 + y ^ 2 := by
      have h : (x : ℤ) * y ≤ (x : ℤ) ^ 2 + (y : ℤ) ^ 2 := by
        nlinarith [sq_nonneg ((x : ℤ) - y)]
      exact_mod_cast h
    have hxy_le : xr.1 * yr.1 ≤ xr.1 ^ 2 + yr.1 ^ 2 := by
      have h : (xr.1 : ℤ) * yr.1 ≤ (xr.1 : ℤ) ^ 2 + (yr.1 : ℤ) ^ 2 := by
        nlinarith [sq_nonneg ((xr.1 : ℤ) - yr.1)]
      exact_mod_cast h
    have hmod :
        signedThreeAdicResidual x y ≡
          xr.1 ^ 2 + yr.1 ^ 2 - xr.1 * yr.1 [MOD 9] := by
      unfold signedThreeAdicResidual
      exact (((Nat.mod_modEq x 9).symm.pow 2).add
        ((Nat.mod_modEq y 9).symm.pow 2)).sub
          hab_le hxy_le
          (((Nat.mod_modEq x 9).symm.mul (Nat.mod_modEq y 9).symm))
    simpa [Nat.ModEq, hf.1] using hmod
  · have hmod : x + y ≡ xr.1 + yr.1 [MOD 3] := by
      simpa [xr, yr] using
        ((Nat.mod_modEq x 9).symm.of_dvd (by norm_num : 3 ∣ 9)).add
          ((Nat.mod_modEq y 9).symm.of_dvd (by norm_num : 3 ∣ 9))
    have hzero : (xr.1 + yr.1) % 3 = 0 := hf.2
    simpa [Nat.ModEq, hzero] using hmod

private theorem three_dvd_sub_of_mod_three_eq
    {x y : ℕ} (hxy : x % 3 = y % 3) :
    3 ∣ x - y := by
  apply Nat.dvd_of_mod_eq_zero
  exact Nat.sub_mod_eq_zero_of_mod_eq hxy

private theorem three_dvd_sum_of_mod_three_zero
    {x y : ℕ} (hxy : (x + y) % 3 = 0) : 3 ∣ x + y :=
  Nat.dvd_of_mod_eq_zero hxy

private theorem residual_positive_sum {x y : ℕ} (hx : 0 < x) (hy : 0 < y) :
    0 < signedThreeAdicResidual x y := by
  have hle : x * y ≤ x ^ 2 + y ^ 2 := by
    have h : (x : ℤ) * y ≤ (x : ℤ) ^ 2 + (y : ℤ) ^ 2 := by
      nlinarith [sq_nonneg ((x : ℤ) - y)]
    exact_mod_cast h
  unfold signedThreeAdicResidual
  have hstrict : x * y < x ^ 2 + y ^ 2 := by
    have h : (x : ℤ) * y < (x : ℤ) ^ 2 + (y : ℤ) ^ 2 := by
      nlinarith [sq_nonneg ((x : ℤ) - y), mul_pos (show (0 : ℤ) < x by exact_mod_cast hx)
        (show (0 : ℤ) < y by exact_mod_cast hy)]
    exact_mod_cast h
  omega

private def packet_of_a
    {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : Nat.Coprime a b) (hEq : a ^ 3 + b ^ 3 = c ^ 3)
    (h3a : 3 ∣ a) (h3b : ¬ 3 ∣ b) (h3c : ¬ 3 ∣ c) :
    SignedThreeAdicPacket a b c := by
  have hcop : Nat.Coprime c b := coprime_cb_of_eq hab hEq
  have hbc : b < c := by
    have hlt : b ^ 3 < c ^ 3 := by
      rw [← hEq]
      exact Nat.lt_add_of_pos_left (pow_pos ha 3)
    exact (Nat.pow_lt_pow_iff_left (by norm_num)).mp hlt
  have hsub : c ^ 3 - b ^ 3 = a ^ 3 := cube_sub_eq_of_add_eq hEq
  have hfact : (c - b) * DkMath.FLT.PetalDetect.S0_nat c b = a ^ 3 := by
    rw [← cube_sub_eq_mul_sub_S0 hbc]
    exact hsub
  have hrespos : 0 < DkMath.FLT.PetalDetect.S0_nat c b := by
    unfold DkMath.FLT.PetalDetect.S0_nat
    positivity
  have hresmod : DkMath.FLT.PetalDetect.S0_nat c b % 9 = 3 := by
    have ha0 : a ^ 3 % 9 = 0 :=
      (mod_nine_cube_zero_iff_three_dvd).2 h3a
    have hcube : c ^ 3 % 9 = b ^ 3 % 9 := by
      have h := congrArg (fun n : ℕ => n % 9) hEq
      simpa [Nat.add_mod, ha0] using h.symm
    exact (residual_mod_nine_difference h3c h3b hcube).1
  have h3gap : 3 ∣ c - b := by
    have hmod : c % 3 = b % 3 := by
      have ha0 : a ^ 3 % 3 = 0 := by
        exact Nat.mod_eq_zero_of_dvd (h3a.trans (dvd_pow_self a (by decide)))
      have h := congrArg (fun n : ℕ => n % 3) hEq
      have hcube : c ^ 3 % 3 = b ^ 3 % 3 := by
        simpa [Nat.add_mod, ha0] using h.symm
      have hcubes : c % 3 = b % 3 := by
        have hclt : c % 3 < 3 := Nat.mod_lt _ (by decide)
        have hblt : b % 3 < 3 := Nat.mod_lt _ (by decide)
        interval_cases hcv : c % 3 <;> interval_cases hbv : b % 3 <;>
          simp_all [Nat.pow_mod]
      exact hcubes
    exact three_dvd_sub_of_mod_three_eq hmod
  refine {
    orientation := .a
    carrier := c - b
    residual := DkMath.FLT.PetalDetect.S0_nat c b
    distinguished := a
    alpha := eisensteinCoord (-c) (-b)
    carrier_pos := Nat.sub_pos_of_lt hbc
    residual_pos := hrespos
    distinguished_pos := ha
    factorization := hfact
    alpha_norm := by
      rw [eisenstein_norm_coords]
      simp [DkMath.FLT.PetalDetect.S0_nat]
    alpha_signed_gap := by
      change (- (b : ℤ)) - (- (c : ℤ)) = (c - b : ℕ)
      rw [Nat.cast_sub hbc.le]
      ring
    three_dvd_carrier := h3gap
    three_dvd_distinguished := h3a
    residual_mod_nine := hresmod
    gcd_eq_three := by
      have hg := gcd_sub_S0_nat_eq_gcd_sub_three hbc hcop
      rw [hg]
      apply Nat.dvd_antisymm
      · exact Nat.gcd_dvd_right (c - b) 3
      · exact Nat.dvd_gcd h3gap (dvd_refl 3) }

private def packet_of_b
    {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : Nat.Coprime a b) (hEq : a ^ 3 + b ^ 3 = c ^ 3)
    (h3a : ¬ 3 ∣ a) (h3b : 3 ∣ b) (h3c : ¬ 3 ∣ c) :
    SignedThreeAdicPacket a b c := by
  have hEq' : b ^ 3 + a ^ 3 = c ^ 3 := by simpa [Nat.add_comm] using hEq
  have hba : Nat.Coprime b a := hab.symm
  have p := packet_of_a hb ha hc hba hEq' h3b h3a h3c
  exact { p with orientation := .b }

private def packet_of_c
    {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : Nat.Coprime a b) (hEq : a ^ 3 + b ^ 3 = c ^ 3)
    (h3a : ¬ 3 ∣ a) (h3b : ¬ 3 ∣ b) (h3c : 3 ∣ c) :
    SignedThreeAdicPacket a b c := by
  have h3c3 : 3 ∣ c ^ 3 := h3c.trans (dvd_pow_self c (by decide))
  have h3sum : 3 ∣ a ^ 3 + b ^ 3 := by simpa [hEq] using h3c3
  have h3carrier : 3 ∣ a + b := by
    have hmod : (a ^ 3 + b ^ 3) % 3 = 0 := Nat.mod_eq_zero_of_dvd h3sum
    have hpow_a : a ^ 3 % 3 = a % 3 := by
      rw [Nat.pow_mod]
      have halt : a % 3 < 3 := Nat.mod_lt _ (by decide)
      interval_cases h : a % 3 <;> simp
    have hpow_b : b ^ 3 % 3 = b % 3 := by
      rw [Nat.pow_mod]
      have hblt : b % 3 < 3 := Nat.mod_lt _ (by decide)
      interval_cases h : b % 3 <;> simp
    apply three_dvd_sum_of_mod_three_zero
    simpa [Nat.add_mod, hpow_a, hpow_b] using hmod
  have hrespos : 0 < signedThreeAdicResidual a b := residual_positive_sum ha hb
  have hresmod : signedThreeAdicResidual a b % 9 = 3 := by
    have hmod : (a ^ 3 + b ^ 3) % 9 = 0 := by
      have h := congrArg (fun n : ℕ => n % 9) hEq
      have hc0 : c ^ 3 % 9 = 0 := by
        exact (mod_nine_cube_zero_iff_three_dvd).2 h3c
      simpa [Nat.add_mod, hc0] using h
    exact (residual_mod_nine_sum h3a h3b hmod).1
  have hfact : (a + b) * signedThreeAdicResidual a b = c ^ 3 := by
    have hle : a * b ≤ a ^ 2 + b ^ 2 := by
      have h : (a : ℤ) * b ≤ (a : ℤ) ^ 2 + (b : ℤ) ^ 2 := by
        nlinarith [sq_nonneg ((a : ℤ) - b)]
      exact_mod_cast h
    have hInt : (((a + b) * signedThreeAdicResidual a b : ℕ) : ℤ) =
        (a ^ 3 + b ^ 3 : ℕ) := by
      unfold signedThreeAdicResidual
      rw [Nat.cast_mul, Nat.cast_add, Nat.cast_sub hle]
      push_cast
      ring
    have hNat : (a + b) * signedThreeAdicResidual a b = a ^ 3 + b ^ 3 := by
      exact_mod_cast hInt
    rw [hNat, hEq]
  refine {
    orientation := .c
    carrier := a + b
    residual := signedThreeAdicResidual a b
    distinguished := c
    alpha := eisensteinCoord (-a) b
    carrier_pos := by omega
    residual_pos := hrespos
    distinguished_pos := hc
    factorization := hfact
    alpha_norm := by
      rw [eisenstein_norm_coords]
      unfold signedThreeAdicResidual
      rw [Nat.cast_sub (by
        have h : (a : ℤ) * b ≤ (a : ℤ) ^ 2 + (b : ℤ) ^ 2 := by
          nlinarith [sq_nonneg ((a : ℤ) - b)]
        exact_mod_cast h)]
      push_cast
      ring
    alpha_signed_gap := by
      change (b : ℤ) - (- (a : ℤ)) = (a + b : ℕ)
      push_cast
      ring
    three_dvd_carrier := h3carrier
    three_dvd_distinguished := h3c
    residual_mod_nine := hresmod
    gcd_eq_three := by
      let g := Nat.gcd (a + b) (signedThreeAdicResidual a b)
      have hsum_a : Nat.Coprime (a + b) a := by
        simpa [Nat.add_comm] using (Nat.coprime_add_self_left).2 hab.symm
      have hsum_b : Nat.Coprime (a + b) b :=
        (Nat.coprime_add_self_left).2 hab
      have hsum_ab : Nat.Coprime (a + b) (a * b) :=
        Nat.Coprime.mul_right hsum_a hsum_b
      have hg_car : g ∣ a + b := by
        exact Nat.gcd_dvd_left _ _
      have hg_res : g ∣ signedThreeAdicResidual a b := by
        exact Nat.gcd_dvd_right _ _
      have hle : a * b ≤ a ^ 2 + b ^ 2 := by
        have h : (a : ℤ) * b ≤ (a : ℤ) ^ 2 + (b : ℤ) ^ 2 := by
          nlinarith [sq_nonneg ((a : ℤ) - b)]
        exact_mod_cast h
      have hidentity : (a + b) ^ 2 =
          signedThreeAdicResidual a b + 3 * (a * b) := by
        calc
          (a + b) ^ 2 = (a ^ 2 + b ^ 2) + 2 * (a * b) := by ring
          _ = (a ^ 2 + b ^ 2 - a * b) + a * b + 2 * (a * b) := by
            rw [Nat.sub_add_cancel hle]
          _ = signedThreeAdicResidual a b + 3 * (a * b) := by
            unfold signedThreeAdicResidual
            ring
      have hgsq : g ∣ (a + b) ^ 2 := hg_car.trans (dvd_pow_self _ (by decide))
      have hg3ab : g ∣ 3 * (a * b) := by
        apply (Nat.dvd_add_iff_left hg_res).mpr
        rw [add_comm]
        rw [← hidentity]
        exact hgsq
      have hgg3 : g ∣ 3 := by
        exact hsum_ab.of_dvd_left hg_car |>.dvd_of_dvd_mul_right hg3ab
      have h3res : 3 ∣ signedThreeAdicResidual a b := by
        refine ⟨3 * (signedThreeAdicResidual a b / 9) + 1, ?_⟩
        have hs := Nat.mod_add_div (signedThreeAdicResidual a b) 9
        omega
      apply Nat.dvd_antisymm
      · exact hgg3
      · exact Nat.dvd_gcd h3carrier h3res }

/-- Every positive primitive cubic solution has exactly one signed 3-adic orientation. -/
theorem exists_signedThreeAdicPacket_of_primitive_solution
    {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : Nat.Coprime a b) (hEq : a ^ 3 + b ^ 3 = c ^ 3) :
    Nonempty (SignedThreeAdicPacket a b c) := by
  rcases exact_one_three_dvd_of_fermat_cube hEq hab with h | h | h
  · exact ⟨packet_of_a ha hb hc hab hEq h.1 h.2.1 h.2.2⟩
  · exact ⟨packet_of_b ha hb hc hab hEq h.1 h.2.1 h.2.2⟩
  · exact ⟨packet_of_c ha hb hc hab hEq h.1 h.2.1 h.2.2⟩

/-- A chosen packet for a positive primitive cubic solution. -/
noncomputable def signedThreeAdicPacket_of_primitive_solution
    {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : Nat.Coprime a b) (hEq : a ^ 3 + b ^ 3 = c ^ 3) :
    SignedThreeAdicPacket a b c :=
  Classical.choice (exists_signedThreeAdicPacket_of_primitive_solution ha hb hc hab hEq)

end DkMath.FLT.Three
