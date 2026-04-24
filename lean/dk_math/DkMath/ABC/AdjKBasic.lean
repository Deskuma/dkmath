/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/


import DkMath.Basic.Nat
import DkMath.ABC.AdjacentBadDensity

#print "file: DkMath.ABC.AdjKBasic"

set_option linter.style.longLine false
set_option linter.style.emptyLine false

/- Note:
※細分化前にエラー／警告を出さない補題・定理ファイル。
  ABC.lean で定義されるべき定理のうち、ABC.lean 内で定義されていた定理をここに移動している。
-/

namespace DkMath.ABC

open DkMath.Basic.Nat
open scoped BigOperators

open Nat Real Rat Filter Finset
-- Final Theorems --

/-
  k-対角 (AdjK) 系の定義と基本補題群。
  この節は対角 (k=1) の結果を k に一般化する雛形を与える。
  主要構成：AdjK, AdjK', AdjK_eq_AdjK', Bad の decidable 構成、
  分母正性の eventually 補題、および adjKBadCount の定義。
-/

/- k-diagonal triple: (n, n+k, 2n+k) -/
/-- Construct an AdjK Triple when a coprimality witness is available: if n and n+k are
  coprime then (n, n+k, 2n+k) is a valid Triple. This lets callers supply the coprime
  hypothesis instead of relying on an unconditional `ad#mit`. -/
def AdjK_of_coprime (k n : Nat) (hcop : Nat.Coprime n (n + k)) : Triple :=
  Triple.mk n (n + k) (2 * n + k) (by ring) (by exact hcop)

@[simp]
theorem AdjK_of_coprime_a (k n : Nat) (hcop : Nat.Coprime n (n + k)) :
  (AdjK_of_coprime k n hcop).a = n := by
  rfl

@[simp]
theorem AdjK_of_coprime_b (k n : Nat) (hcop : Nat.Coprime n (n + k)) :
  (AdjK_of_coprime k n hcop).b = n + k := by
  rfl

@[simp]
theorem AdjK_of_coprime_c (k n : Nat) (hcop : Nat.Coprime n (n + k)) :
  (AdjK_of_coprime k n hcop).c = 2 * n + k := by
  rfl

@[simp]
theorem Adj_eq_AdjK_of_coprime (n : ℕ) : Adj n = AdjK_of_coprime 1 n (coprime_succ n) := by
  rfl

-- 改訂: 以前は `AdjK (k n)` を無条件に構成し coprimality を `ad#mit` で塞いでいたが、
-- 一般には gcd(n, n+k)=1 は成り立たないため不正確であった。ここで interface を
-- 明示的に (hcop : Nat.Coprime n (n + k)) を要求する形に変更し、`ad#mit` を除去する。
-- 既存のコードで無条件版を参照している箇所は `AdjK_of_coprime` を利用するか、
-- 必要な前提を明示的に渡すように順次移行すること。
/-- k-diagonal triple: (n, n+k, 2n+k) with an explicit coprimality witness. -/
def AdjK (k n : Nat) (hcop : Nat.Coprime n (n + k)) : Triple :=
  Triple.mk n (n + k) (2 * n + k) (by ring) hcop

-- 使われていない補題・定義だが同値性を示しておく（あとで統一化する）
lemma Adj_eq_AdjK (n : ℕ) : Adj n = AdjK 1 n (coprime_succ n) := by rfl

lemma AdjK_eq_AdjK_of_coprime (k n : ℕ) (h : Nat.Coprime n (n + k)) :
  AdjK k n h = AdjK_of_coprime k n h := by rfl

@[simp]
theorem AdjK_a (k n : Nat) (h : Nat.Coprime n (n + k)) : (AdjK k n h).a = n := by
  rfl

@[simp]
theorem AdjK_b (k n : Nat) (h : Nat.Coprime n (n + k)) : (AdjK k n h).b = n + k := by
  rfl

@[simp]
theorem AdjK_c (k n : Nat) (h : Nat.Coprime n (n + k)) : (AdjK k n h).c = 2 * n + k := by
  rfl

def AdjK' (k n : Nat) (h : Nat.Coprime n (n + k)) : Triple := AdjK k n h

@[simp]
theorem AdjK_eq_AdjK' (k n : Nat) (h : Nat.Coprime n (n + k)) : AdjK k n h = AdjK' k n h := rfl

/-- decidability of Bad on AdjK (noncomputable) -/
-- 旧 `AdjK` に依存した decidable instance はシグネチャ変更に伴い直接は定義できない。
-- 必要なら `(fun n => ∀ h : Nat.Coprime n (n + k), Bad δ (AdjK k n h))` 形式で与える。
noncomputable instance Bad_adjK_decidable (δ : ℝ) (k : Nat) :
  ∀ n, Decidable (∀ h : Nat.Coprime n (n + k), Bad δ (AdjK k n h)) := fun _ => Classical.dec _

/-- 0.435 に対する AdjK の decidable predicate -/
noncomputable instance Bad_adjK_pred (k : Nat) :
  DecidablePred (fun n => (∀ h : Nat.Coprime n (n + k), Bad (0.435 : ℝ) (AdjK k n h))) :=
  fun n => Bad_adjK_decidable _ _ n

/-- general decidable predicate for arbitrary δ -/
noncomputable instance Bad_adjK_pred_general (δ : ℝ) (k : Nat) :
  DecidablePred (fun n => (∀ h : Nat.Coprime n (n + k), Bad δ (AdjK k n h))) :=
  fun n => Bad_adjK_decidable δ k n

/-- rad の下限（大きな n で積が ≥ 2 となる） -/
lemma rad_ge_two_of_two_le (m : Nat) (hm : 2 ≤ m) : 2 ≤ rad m := by
  -- m ≥ 2 ⇒ m ≠ 0, m ≠ 1
  have hm0 : m ≠ 0 := by
    exact Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hm)
  have hm1 : m ≠ 1 := by
    exact Nat.ne_of_gt (lt_of_lt_of_le (by decide : 1 < 2) hm)
  -- 存在する素因子 p（p ≥ 2, p ∣ m）を取り出す
  obtain ⟨p, hp_prime, hp_dvd⟩ := Nat.exists_prime_and_dvd hm1
  have hp_ge_two : 2 ≤ p := Nat.Prime.two_le hp_prime
  -- p は factorization.support に現れるので rad m を割る
  have hmem : p ∈ m.factorization.support := by
    rw [mem_support_factorization_iff]
    exact ⟨hm0, hp_prime, hp_dvd⟩
  have hpd : p ∣ rad m := Finset.dvd_prod_of_mem (fun q => q) hmem
  -- rad m > 0 （m ≠ 0 なら rad m ≥ 1）
  have rad_pos_m : 0 < rad m := by
    have h1 : 1 ≤ rad m := abc_one_le_rad hm0
    exact Nat.succ_le_iff.mp h1
  -- 2 ≤ p ≤ rad m
  exact hp_ge_two.trans (Nat.le_of_dvd rad_pos_m hpd)

/-- k-対角の log(rad) が正であること -/
theorem eventually_log_rad_pos_adjK (k : Nat) :
  ∀ᶠ n in atTop, 0 < Real.log (rad n * rad (n + k) * rad (2 * n + k)) := by
  have h_n : ∀ᶠ n in atTop, 2 ≤ n := Filter.eventually_atTop.2 ⟨2, fun n hn => hn⟩
  filter_upwards [h_n] with n hn
  have ha_rad : 2 ≤ rad n := rad_ge_two_of_two_le n hn
  have hb_rad : 2 ≤ rad (n + k) := by
    have : 2 ≤ n + k := by linarith
    exact rad_ge_two_of_two_le (n + k) this
  have hc_rad : 2 ≤ rad (2 * n + k) := by
    have : 2 ≤ 2 * n + k := by linarith
    exact rad_ge_two_of_two_le (2 * n + k) this
  have four_le : 4 ≤ rad n * rad (n + k) := Nat.mul_le_mul ha_rad hb_rad
  have eight_le : 8 ≤ rad n * rad (n + k) * rad (2 * n + k) := Nat.mul_le_mul four_le hc_rad
  have one_lt_prod_nat : 1 < rad n * rad (n + k) * rad (2 * n + k) := by
    have : 1 < 8 := by norm_num
    exact lt_of_lt_of_le this eight_le
  have one_lt_prod : (1 : ℝ) < ((rad n * rad (n + k) * rad (2 * n + k)) : ℝ) := by
    exact_mod_cast one_lt_prod_nat
  exact Real.log_pos one_lt_prod

end DkMath.ABC
