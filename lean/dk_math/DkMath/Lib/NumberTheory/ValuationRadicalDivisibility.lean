/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Adapted from P2M/Sol/S_ValuationSubring_exists_pow_eq_of_kummer_descent.lean,
commit 115356cbc627159d0d16add0da6e9a2bb3655ed8.
Modified: valuation stability and exact radical descent in the reusable DkMath library.
-/

import DkMath.Lib.NumberTheory.InertiaUnitExactRoots

#print "file: DkMath.Lib.NumberTheory.ValuationRadicalDivisibility"

/-! # 代数的付値の有理関係と根の塔による値群 p 可除性
消去多項式の最大項を比較し、Bezout 係数で値を正規化する。 -/
namespace DkMath.Lib.NumberTheory
noncomputable section
open Polynomial
namespace RationalValue

variable {L : Type*} [Field L]

theorem valuation_natCast_eq_one (P : ValuationSubring L) (q : ℕ)
    (hq : ((q : ℕ) : P) ∈ IsLocalRing.maximalIdeal P) (n : ℕ) (hn : Nat.Coprime n q) :
    P.valuation (n : L) = 1 := by
  have hunit : IsUnit ((n : ℕ) : P) := by
    rw [← IsLocalRing.notMem_maximalIdeal]
    intro hm
    obtain ⟨a, b, hab⟩ := Nat.Coprime.cast (R := P) hn
    apply (IsLocalRing.maximalIdeal.isMaximal P).ne_top
    rw [Ideal.eq_top_iff_one, ← hab]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hm) (Ideal.mul_mem_left _ _ hq)
  have := (P.valuation_eq_one_iff _).mp hunit
  simpa using this

theorem valuation_intCast (P : ValuationSubring L) (q : ℕ) (hqp : q.Prime)
    (hq : ((q : ℕ) : P) ∈ IsLocalRing.maximalIdeal P) (z : ℤ) (hz : z ≠ 0) :
    ∃ e : ℕ, P.valuation (z : L) = P.valuation (q : L) ^ e := by
  obtain ⟨e, n', hnd, habs⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (Int.natAbs_ne_zero.mpr hz) q hqp.one_lt.ne'
  have hn' : Nat.Coprime n' q := ((Nat.Prime.coprime_iff_not_dvd hqp).mpr hnd).symm
  refine ⟨e, ?_⟩
  have habs' : ((z.natAbs : ℕ) : L) = (q : L) ^ e * (n' : L) := by rw [habs]; push_cast; ring
  have hzabs : P.valuation (z : L) = P.valuation ((z.natAbs : ℕ) : L) := by
    rcases Int.natAbs_eq z with h | h
    · conv_lhs => rw [h]
      rw [Int.cast_natCast]
    · conv_lhs => rw [h]
      rw [Int.cast_neg, Valuation.map_neg, Int.cast_natCast]
  rw [hzabs, habs', map_mul, map_pow, valuation_natCast_eq_one P q hq n' hn', mul_one]

theorem valuation_ratCast [CharZero L] (P : ValuationSubring L) (q : ℕ) (hqp : q.Prime)
    (hq : ((q : ℕ) : P) ∈ IsLocalRing.maximalIdeal P) (c : ℚ) (hc : c ≠ 0) :
    ∃ m : ℤ, P.valuation (c : L) = P.valuation (q : L) ^ m := by
  have hq0 : P.valuation (q : L) ≠ 0 := by
    rw [Valuation.ne_zero_iff]; exact_mod_cast hqp.ne_zero
  obtain ⟨e₁, h₁⟩ := valuation_intCast P q hqp hq c.num (Rat.num_ne_zero.mpr hc)
  obtain ⟨e₂, h₂⟩ := valuation_intCast P q hqp hq c.den (by exact_mod_cast c.den_ne_zero)
  refine ⟨e₁ - e₂, ?_⟩
  rw [Rat.cast_def, map_div₀, h₁]
  have : P.valuation ((c.den : ℕ) : L) = P.valuation (q : L) ^ e₂ := by simpa using h₂
  rw [this, zpow_sub₀ hq0, zpow_natCast, zpow_natCast]

theorem exists_valuation_pow_eq [CharZero L] (P : ValuationSubring L) (q : ℕ) (hqp : q.Prime)
    (hq : ((q : ℕ) : P) ∈ IsLocalRing.maximalIdeal P) (x : L) (hx : x ≠ 0) (halg : IsAlgebraic ℚ x) :
    ∃ n : ℕ, 0 < n ∧ ∃ m : ℤ, P.valuation x ^ n = P.valuation (q : L) ^ m := by
  classical
  set v := P.valuation with hv
  have hq0 : v (q : L) ≠ 0 := by
    rw [Valuation.ne_zero_iff]; exact_mod_cast hqp.ne_zero
  have hx0 : v x ≠ 0 := (Valuation.ne_zero_iff v).mpr hx
  have key : ∀ (i j : ℕ) (mi mj : ℤ), i < j →
      v (q : L) ^ mi * v x ^ i = v (q : L) ^ mj * v x ^ j →
      ∃ n : ℕ, 0 < n ∧ ∃ m : ℤ, v x ^ n = v (q : L) ^ m := by
    intro i j mi mj hij h
    refine ⟨j - i, Nat.sub_pos_of_lt hij, mi - mj, ?_⟩
    have hsplit : v x ^ j = v x ^ (j - i) * v x ^ i := by
      rw [← pow_add, Nat.sub_add_cancel hij.le]
    rw [hsplit, ← mul_assoc] at h
    have h' : v (q : L) ^ mi = v (q : L) ^ mj * v x ^ (j - i) := mul_right_cancel₀ (pow_ne_zero _ hx0) h
    rw [zpow_sub₀ hq0, eq_div_iff (zpow_ne_zero _ hq0), mul_comm]
    exact h'.symm
  obtain ⟨p, hp0, hpx⟩ := halg
  let f : ℕ → L := fun i => (p.coeff i : L) * x ^ i
  have hsum : ∑ i ∈ p.support, f i = 0 := by
    rw [aeval_def, eval₂_eq_sum, Polynomial.sum_def] at hpx
    simpa [f] using hpx
  have hs : p.support.Nonempty :=
    Finset.nonempty_of_ne_empty (by rwa [Ne, Polynomial.support_eq_empty])
  obtain ⟨j, hj, hjmax⟩ := Finset.exists_max_image p.support (fun i => v (f i)) hs
  have hcj : p.coeff j ≠ 0 := Polynomial.mem_support_iff.mp hj
  have hfj0 : v (f j) ≠ 0 := by
    rw [Valuation.ne_zero_iff]
    exact mul_ne_zero (by exact_mod_cast hcj) (pow_ne_zero _ hx)
  have hex : ∃ i ∈ p.support, i ≠ j ∧ v (f i) = v (f j) := by
    by_contra hne
    simp only [not_exists, not_and] at hne
    have hlt : ∀ i ∈ p.support \ {j}, v (f i) < v (f j) := by
      intro i hi
      rw [Finset.mem_sdiff, Finset.mem_singleton] at hi
      exact lt_of_le_of_ne (hjmax i hi.1) (hne i hi.1 hi.2)
    have heq := Valuation.map_sum_eq_of_lt v hj hlt
    rw [hsum, map_zero] at heq
    exact hfj0 heq.symm
  obtain ⟨i, hi, hij, hvij⟩ := hex
  have hci : p.coeff i ≠ 0 := Polynomial.mem_support_iff.mp hi
  obtain ⟨mi, hmi⟩ := valuation_ratCast P q hqp hq _ hci
  obtain ⟨mj, hmj⟩ := valuation_ratCast P q hqp hq _ hcj
  rw [← hv] at hmi hmj
  have hvij' : v (q : L) ^ mi * v x ^ i = v (q : L) ^ mj * v x ^ j := by
    simpa [f, map_mul, map_pow, hmi, hmj] using hvij
  rcases lt_or_gt_of_ne hij with h | h
  · exact key i j mi mj h hvij'
  · exact key j i mj mi h hvij'.symm

end RationalValue

namespace RadicalValue

variable {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

theorem eq_one_of_pow_eq_one (u : Γ₀) {k : ℕ} (hk : k ≠ 0) (h : u ^ k = 1) : u = 1 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  rcases lt_trichotomy u 1 with hlt | heq | hgt
  · exfalso
    have h1 : u ^ k ≤ 1 := pow_le_one' hlt.le k
    have h2 : u ^ (k + 1) ≤ u := by
      rw [pow_succ]
      calc u ^ k * u ≤ 1 * u := mul_le_mul' h1 le_rfl
        _ = u := one_mul u
    rw [h] at h2
    exact absurd (lt_of_le_of_lt h2 hlt) (lt_irrefl 1)
  · exact heq
  · exfalso
    have h1 : 1 ≤ u ^ k := one_le_pow_of_one_le' hgt.le k
    have h2 : u ≤ u ^ (k + 1) := by
      rw [pow_succ]
      calc u = 1 * u := (one_mul u).symm
        _ ≤ u ^ k * u := mul_le_mul' h1 le_rfl
    rw [h] at h2
    exact absurd (lt_of_lt_of_le hgt h2) (lt_irrefl 1)

variable {K : Type*} [Field K]

theorem exists_valuation_eq_pow (v : Valuation K Γ₀) (p : ℕ) (hp : p.Prime) (q : K) (hq : q ≠ 0)
    (hroot : ∀ k : ℕ, ∃ r : K, r ^ (p ^ k) = q) (a : K) (ha : a ≠ 0)
    (hrat : ∃ n : ℕ, 0 < n ∧ ∃ m : ℤ, v a ^ n = v q ^ m) :
    ∃ b : K, b ≠ 0 ∧ v a = v b ^ p := by
  obtain ⟨n, hn, m, hnm⟩ := hrat
  obtain ⟨j, n', hnd, hnj⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn.ne' p hp.one_lt.ne'
  obtain ⟨r, hr⟩ := hroot (j + 1)
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [zero_pow (pow_ne_zero _ hp.ne_zero)] at hr
    exact hq hr.symm
  set α := v a with hα
  set ρ := v r with hρ
  have hα0 : α ≠ 0 := (Valuation.ne_zero_iff v).mpr ha
  have hρ0 : ρ ≠ 0 := (Valuation.ne_zero_iff v).mpr hr0
  have hγ : v q = ρ ^ (p ^ (j + 1)) := by rw [← hr, map_pow]
  have h1 : α ^ n' = ρ ^ ((p : ℤ) * m) := by
    have hx : (α ^ n' / ρ ^ ((p : ℤ) * m)) ^ (p ^ j) = 1 := by
      rw [div_pow, ← pow_mul, mul_comm n' (p ^ j), ← hnj, hnm, hγ, ← zpow_natCast, ← zpow_natCast,
        ← zpow_mul, ← zpow_mul]
      rw [show (p : ℤ) * m * ((p ^ j : ℕ) : ℤ) = ((p ^ (j + 1) : ℕ) : ℤ) * m by push_cast; ring,
        div_self (zpow_ne_zero _ hρ0)]
    have := eq_one_of_pow_eq_one _ (pow_ne_zero _ hp.ne_zero) hx
    rwa [div_eq_one_iff_eq (zpow_ne_zero _ hρ0)] at this
  have hcop : IsCoprime (n' : ℤ) (p : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr ((Nat.Prime.coprime_iff_not_dvd hp).mpr hnd).symm
  obtain ⟨s, t, hst⟩ := hcop
  refine ⟨r ^ (m * s) * a ^ t, mul_ne_zero (zpow_ne_zero _ hr0) (zpow_ne_zero _ ha), ?_⟩
  rw [map_mul, map_zpow₀, map_zpow₀, ← hρ, ← hα]
  calc α = α ^ ((1 : ℤ)) := (zpow_one α).symm
    _ = α ^ (s * n' + t * p) := by rw [hst]
    _ = (α ^ n') ^ s * (α ^ t) ^ (p : ℤ) := by
        rw [zpow_add₀ hα0, mul_comm s, zpow_mul, zpow_mul, zpow_natCast]
    _ = (ρ ^ ((p : ℤ) * m)) ^ s * (α ^ t) ^ (p : ℤ) := by rw [h1]
    _ = (ρ ^ (m * s) * α ^ t) ^ p := by
        rw [← zpow_natCast, mul_zpow, ← zpow_mul, ← zpow_mul, ← zpow_mul,
          show (p : ℤ) * m * s = m * s * (p : ℤ) by ring]

end RadicalValue

end
end DkMath.Lib.NumberTheory

