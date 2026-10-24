/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.PadicValNat
import DkMath.Lib.Algebra.BinomTail
import Mathlib.Data.Nat.Factorization.Basic

#print "file: DkMath.Lib.NumberTheory.PerfectPowerValuation"

/-!
# 完全冪の局所判定と有限集合の外への付値障害

[DkMath.Lib] GN-LIB-007a。非零自然数の素因数分解を用い、全素数で指数kが付値を
割り切ることとk乗表示を同一視する。有限集合上での検査は、その集合の外の付値を制御しない。
全体がk乗でないことを別の証明から受け取って初めて、集合外の不整合素数が存在する。
`padicValNat q 0 = 0` の規約があるため、非零条件を型に残す。
-/

namespace DkMath.Lib.NumberTheory

open scoped BigOperators

/-- [DkMath.Lib] 非零自然数の全素因数で付値がkの倍数なら、k乗根を有限積で構成する。
根は各素因数の指数をkで割って掛ける。k=0でも、仮定がn=1を強制するため成立する。 -/
theorem exists_pow_eq_of_dvd_padicValNat {n k : ℕ} (hn : n ≠ 0)
    (h : ∀ q, q.Prime → q ∣ n → k ∣ padicValNat q n) :
    ∃ a : ℕ, a ^ k = n := by
  classical
  refine ⟨∏ q ∈ n.primeFactors, q ^ (n.factorization q / k), ?_⟩
  rw [← Finset.prod_pow]
  calc
    (∏ q ∈ n.primeFactors, (q ^ (n.factorization q / k)) ^ k) =
        ∏ q ∈ n.primeFactors, q ^ n.factorization q := by
      apply Finset.prod_congr rfl
      intro q hq
      have hp := Nat.prime_of_mem_primeFactors hq
      have hd : k ∣ n.factorization q := by
        rw [Nat.factorization_def n hp]
        exact h q hp (Nat.dvd_of_mem_primeFactors hq)
      rw [← pow_mul, Nat.div_mul_cancel hd]
    _ = n := (Nat.prod_primeFactors_pow_factorization hn).symm

/-- [DkMath.Lib] 完全冪の全素数付値判定。素数の存在と付値の深さを区別する。
非零性は素因数分解から元の数を再構成するために必要である。 -/
theorem exists_pow_eq_iff_dvd_padicValNat {n k : ℕ} (hn : n ≠ 0) :
    (∃ a : ℕ, a ^ k = n) ↔ ∀ q, q.Prime → q ∣ n → k ∣ padicValNat q n := by
  constructor
  · rintro ⟨a, rfl⟩ q hq _
    let : Fact q.Prime := ⟨hq⟩
    rw [padicValNat.pow]
    exact dvd_mul_right k _
  · exact exists_pow_eq_of_dvd_padicValNat hn

/-- [DkMath.Lib] 非完全冪には、指数で割り切れない付値を持つ素因数がある。
この結論は付値が1だとは主張しない。 -/
theorem exists_prime_padicValNat_not_dvd {n k : ℕ} (hn : n ≠ 0)
    (hpow : ¬ ∃ a : ℕ, a ^ k = n) :
    ∃ q, q.Prime ∧ q ∣ n ∧ ¬ k ∣ padicValNat q n := by
  by_contra! h
  exact hpow (exists_pow_eq_of_dvd_padicValNat hn h)

/-- [DkMath.Lib] 有限集合上の局所完済と、全体の非完全冪性から集合外へ脱出する。
局所完済だけから非完全冪性を導く循環論法は使わない。 -/
theorem exists_prime_outside_of_local_power {S : Finset ℕ} {n k : ℕ} (hn : n ≠ 0)
    (hpow : ¬ ∃ a : ℕ, a ^ k = n)
    (hlocal : ∀ q ∈ S, q.Prime → k ∣ padicValNat q n) :
    ∃ q, q.Prime ∧ q ∣ n ∧ q ∉ S ∧ ¬ k ∣ padicValNat q n := by
  obtain ⟨q, hq, hqn, hv⟩ := exists_prime_padicValNat_not_dvd hn hpow
  exact ⟨q, hq, hqn, fun hmem => hv (hlocal q hmem hq), hv⟩

/-- [DkMath.Lib] 隣接するk乗の間の自然数はk乗でない。
底の順序だけを使い、素数性やFLTを入力にしない。 -/
theorem not_pow_of_between_consecutive_powers {n a k : ℕ}
    (hlo : a ^ k < n) (hhi : n < (a + 1) ^ k) :
    ¬ ∃ z : ℕ, z ^ k = n := by
  rintro ⟨z, rfl⟩
  by_cases hz : z ≤ a
  · exact (not_lt_of_ge (Nat.pow_le_pow_left hz k)) hlo
  · have ha : a + 1 ≤ z := by omega
    exact (not_lt_of_ge (Nat.pow_le_pow_left ha k)) hhi

/-- [DkMath.Lib] x>1、k≥2ならx^k−1は隣接k乗の間にある。
下側の厳密性は二項尾項の正性から得る。これはy=1の特殊構成であり、
x^k−y^kへ無条件に拡張する不等式ではない。 -/
theorem pow_sub_one_between {x k : ℕ} (hx : 1 < x) (hk : 2 ≤ k) :
    (x - 1) ^ k < x ^ k - 1 ∧ x ^ k - 1 < x ^ k := by
  have h := DkMath.Algebra.BinomTail.add_pow_gt_sum_pows_nat_of_two_le
    (x - 1) 1 hk (by omega) (by decide)
  have hsum : x - 1 + 1 = x := by omega
  rw [hsum, one_pow] at h
  omega

/-- [DkMath.Lib] 連続k乗の間隔による非完全冪性。任意の余因子R_nの非完全冪性ではない。 -/
theorem not_pow_pow_sub_one {x k : ℕ} (hx : 1 < x) (hk : 2 ≤ k) :
    ¬ ∃ a : ℕ, a ^ k = x ^ k - 1 := by
  obtain ⟨hl, hh⟩ := pow_sub_one_between hx hk
  apply not_pow_of_between_consecutive_powers hl
  simpa only [Nat.sub_add_cancel hx.le] using hh

/-! ## 次数0と非零条件の境界 -/
example : ∃ a : ℕ, a ^ 0 = 1 := ⟨1, by decide⟩
example : (∀ q : ℕ, 0 ∣ padicValNat q 0) ∧ ¬ ∃ a : ℕ, a ^ 0 = 0 := by simp
example : ¬ ∃ a : ℕ, a ^ 3 = 7 :=
  not_pow_of_between_consecutive_powers (a := 1) (by decide) (by decide)

end DkMath.Lib.NumberTheory
