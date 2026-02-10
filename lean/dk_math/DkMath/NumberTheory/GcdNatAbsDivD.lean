/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

-- import Mathlib
import DkMath.Algebra.DiffPow
import DkMath.NumberTheory.GcdLemmas

namespace DkMath.NumberTheory.GcdDiffPow

open scoped BigOperators
open Finset
open DkMath.Algebra.DiffPow

/-!
素因子補題：もし素数 p が `a - b` と `diffPowSum (a,b,d)` 両方を割るなら、かつ `gcd a b = 1` のとき p は d を割る。
これは `gcd (a-b, S_d(a,b)) | d` の核心部分となる補題である。
-/

/-- Nat-level補題：|a-b| と |S| の自然数 gcd が d を割る。 -/
theorem gcd_natAbs_divides_d {a b : ℤ} {d : ℕ} (hd : 1 ≤ d) (hab : Int.gcd a b = 1)
    (hab_ne : a ≠ b) :
    (a - b).natAbs.gcd (diffPowSum a b d).natAbs ∣ d := by
  let g := (a - b).natAbs.gcd (diffPowSum a b d).natAbs

  -- gcd は常にpositive（a ≠ b より (a-b).natAbs > 0）
  have hg_pos : 0 < g := by
    -- 背理法：g = 0 と仮定すると矛盾
    by_contra h
    push_neg at h
    simp only [Nat.le_zero] at h
    -- g = 0 なら gcd(|a-b|, |S|) = 0
    -- つまり |a-b| = 0 and |S| = 0
    have hab_eq : (a - b).natAbs = 0 := by
      have := Nat.eq_zero_of_gcd_eq_zero_left h
      exact this
    -- |a-b| = 0 なら a = b
    have hab_eq_int : (a - b : ℤ) = 0 := Int.natAbs_eq_zero.mp hab_eq
    have hab_eq_final : a = b := by omega
    -- しかし hab_ne : a ≠ b に矛盾
    exact hab_ne hab_eq_final

  -- prime power版の key：p^k が g を割るなら p^k が d を割る
  have key_pow : ∀ p k : ℕ, Nat.Prime p → p^k ∣ g → p^k ∣ d := by
    intro p k hp_prime hpk_dvd_g
    -- p^k が g = gcd(|a-b|, |S|) を割る
    -- gcd の性質：p^k | gcd(a,b) なら p^k は a, b の公約数
    have hpk_dvd_ab : p^k ∣ (a - b).natAbs :=
      Nat.dvd_trans hpk_dvd_g (Nat.gcd_dvd_left _ _)
    have hpk_dvd_S : p^k ∣ (diffPowSum a b d).natAbs :=
      Nat.dvd_trans hpk_dvd_g (Nat.gcd_dvd_right _ _)

    -- natAbs から Int へ変換
    have hpk_dvd_ab_int : (p : ℤ)^k ∣ (a - b) := by
      rw [← Int.natAbs_dvd_natAbs]
      exact_mod_cast hpk_dvd_ab
    have hpk_dvd_S_int : (p : ℤ)^k ∣ diffPowSum a b d := by
      rw [← Int.natAbs_dvd_natAbs]
      exact_mod_cast hpk_dvd_S

    -- gcd の性質から (p:ℤ)^k が Int.gcd(a-b, diffPowSum a b d) を割る
    -- （両方の公約数が gcd を割る）
    have hpk_dvd_gcd : (p : ℤ)^k ∣ Int.gcd (a - b) (diffPowSum a b d) := by
      sorry

    -- prime_pow_dividing_gcd_divides_d_pow を使う
    have hpk_dvd_d_int : (p : ℤ)^k ∣ (d : ℤ) :=
      prime_pow_dividing_gcd_divides_d_pow hp_prime hab hpk_dvd_gcd

    -- Nat へ戻す
    exact_mod_cast hpk_dvd_d_int

  -- prime power 版の gcd_divides_d を使って g ∣ d を得る
  exact gcd_divides_d hg_pos key_pow

end DkMath.NumberTheory.GcdDiffPow
