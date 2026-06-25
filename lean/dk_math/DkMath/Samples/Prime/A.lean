/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib

-- cid: 6a3bcb39-f6e4-83e8-a7a9-9ed99b987282

set_option linter.style.whitespace false
set_option linter.style.emptyLine false

/-!
宇宙式の基本型からの素数無限性定理を導く
$N+1 = (P+1)²$
-/

namespace DkMath.CosmicFormula

/-- 宇宙境界関数：n² - 1 = (n-1)(n+1) -/
def cosmicN (P : ℕ) : ℕ := (P + 1)^2 - 1

/-- 基本等式：cosmicN P + 1 = (P + 1)² -/
theorem cosmicN_boundary' (P : ℕ) :
    cosmicN P + 1 = (P + 1)^2 := by
  unfold cosmicN
  exact Nat.add_succ ((P + 1) ^ 2 - 1) 0

/-- 基本等式：cosmicN P + 1 = (P + 1)² : (hpos) -/
theorem cosmicN_boundary (P : ℕ) :
    cosmicN P + 1 = (P + 1)^2 := by
  unfold cosmicN
  have hpos : 0 < (P + 1)^2 := by
    positivity
  omega

/-- 積の等式：cosmicN P = P * (P + 2) -/
theorem cosmicN_eq_mul (P : ℕ) :
    cosmicN P = P * (P + 2) := by
  unfold cosmicN
  refine Nat.sub_eq_of_eq_add ?_
  ring_nf

/-- 素数が宇宙境界と境界平方の両方を割り切ることは不可能 -/
theorem no_prime_divides_cosmicN_and_boundary_square
    (P q : ℕ)
    (hq_prime : Nat.Prime q)
    (hq_cosmic : q ∣ cosmicN P)
    (hq_square : q ∣ (P + 1)^2) :
    False := by
  have hq_succ : q ∣ cosmicN P + 1 := by
    rw [cosmicN_boundary P]
    exact hq_square
  have hq_one : q ∣ 1 := by
    have h : q ∣ cosmicN P + 1 - cosmicN P :=
      Nat.dvd_sub hq_succ hq_cosmic
    exact (Nat.dvd_add_iff_right hq_cosmic).mpr hq_square
  exact hq_prime.not_dvd_one hq_one

/-- 素数集合 s の外側に新しい素数が存在する（gcd スタイル） -/
theorem cosmic_boundary_demands_new_prime_gcd_style
    (s : Finset ℕ)
    (hs : ∀ p ∈ s, Nat.Prime p) :
    ∃ q : ℕ,
      Nat.Prime q ∧
      q ∣ ((∏ p ∈ s, p) + 1)^2 ∧
      q ∉ s := by
  classical
  let P : ℕ := ∏ p ∈ s, p
  have hP_ne_zero : P ≠ 0 := by
    dsimp [P]
    exact Finset.prod_ne_zero_iff.mpr (by
      intro p hp
      exact (hs p hp).ne_zero)
  have hP1_ne_one : P + 1 ≠ 1 := by
    intro h
    apply hP_ne_zero
    exact Nat.succ.inj h
  obtain ⟨q, hq_prime, hq_dvd_P1⟩ :=
    (Nat.ne_one_iff_exists_prime_dvd).mp hP1_ne_one
  have hq_dvd_square : q ∣ (P + 1)^2 :=
    dvd_pow hq_dvd_P1 (by decide : 2 ≠ 0)
  refine ⟨q, hq_prime, ?_, ?_⟩
  · simpa [P] using hq_dvd_square
  · intro hq_mem
    have hq_dvd_P : q ∣ P := by
      dsimp [P]
      exact Finset.dvd_prod_of_mem (fun p => p) hq_mem
    have hP_dvd_cosmic : P ∣ cosmicN P := by
      rw [cosmicN_eq_mul P]
      exact Nat.dvd_mul_right P (P + 2)
    have hq_dvd_cosmic : q ∣ cosmicN P :=
      dvd_trans hq_dvd_P hP_dvd_cosmic
    exact no_prime_divides_cosmicN_and_boundary_square
      P q hq_prime hq_dvd_cosmic hq_dvd_square

/-- 素数集合 s の外側に新しい素数が存在する（標準形） -/
theorem exists_prime_not_mem_dvd_prod_succ
    (s : Finset ℕ)
    (hs : ∀ p ∈ s, Nat.Prime p) :
    ∃ q : ℕ, Nat.Prime q ∧ q ∣ (∏ p ∈ s, p) + 1 ∧ q ∉ s := by
  classical
  let P : ℕ := ∏ p ∈ s, p
  have hP_ne_zero : P ≠ 0 := by
    dsimp [P]
    exact Finset.prod_ne_zero_iff.mpr (by
      intro p hp
      exact (hs p hp).ne_zero)
  have hP1_ne_one : P + 1 ≠ 1 := by
    intro h
    apply hP_ne_zero
    exact Nat.succ.inj h
  obtain ⟨q, hq_prime, hq_dvd⟩ :=
    (Nat.ne_one_iff_exists_prime_dvd).mp hP1_ne_one
  refine ⟨q, hq_prime, ?_, ?_⟩
  · simpa [P] using hq_dvd
  · intro hq_mem
    have hq_dvd_P : q ∣ P := by
      dsimp [P]
      exact Finset.dvd_prod_of_mem (fun p => p) hq_mem
    have hq_dvd_one : q ∣ 1 := by
      have h : q ∣ P + 1 - P := Nat.dvd_sub hq_dvd hq_dvd_P
      exact (Nat.dvd_add_iff_right hq_dvd_P).mpr hq_dvd
    exact hq_prime.not_dvd_one hq_dvd_one

/-- 宇宙境界定理（標準形から派生） -/
theorem cosmic_boundary_demands_new_prime
    (s : Finset ℕ)
    (hs : ∀ p ∈ s, Nat.Prime p) :
    ∃ q : ℕ,
      Nat.Prime q ∧
      q ∣ ((∏ p ∈ s, p) + 1)^2 ∧
      q ∉ s := by
  obtain ⟨q, hq_prime, hq_dvd, hq_not_mem⟩ :=
    exists_prime_not_mem_dvd_prod_succ s hs
  refine ⟨q, hq_prime, ?_, hq_not_mem⟩
  exact dvd_pow hq_dvd (by decide : 2 ≠ 0)

/-- n ≤ q の素数存在（ユークリッドの定理） -/
theorem exists_prime_ge_from_cosmic (n : ℕ) :
    ∃ q : ℕ, n ≤ q ∧ Nat.Prime q := by
  classical
  let s : Finset ℕ := (Finset.range n).filter Nat.Prime
  have hs : ∀ p ∈ s, Nat.Prime p := by
    intro p hp
    exact (Finset.mem_filter.mp hp).2
  obtain ⟨q, hq_prime, hq_dvd, hq_not_mem⟩ :=
    exists_prime_not_mem_dvd_prod_succ s hs
  refine ⟨q, ?_, hq_prime⟩
  by_contra hq_lt_not
  have hq_lt : q < n := by omega
  have hq_mem_s : q ∈ s := by
    dsimp [s]
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr hq_lt, hq_prime⟩
  exact hq_not_mem hq_mem_s

/-- ユークリッドの定理の標準形 -/
def EuclidPrimesInfinite : Prop :=
  ∀ n : ℕ, ∃ p : ℕ, n ≤ p ∧ Nat.Prime p

/-- 宇宙境界ルートからユークリッドの定理を導く -/
theorem euclid_from_cosmic_boundary :
    EuclidPrimesInfinite := by
  intro n
  classical
  -- n 未満の素数を全部集めた有限集合
  let s : Finset ℕ := (Finset.range n).filter Nat.Prime
  have hs : ∀ p ∈ s, Nat.Prime p := by
    intro p hp
    exact (Finset.mem_filter.mp hp).2
  -- 宇宙境界定理から、s の外側の新しい素数 q を得る
  obtain ⟨q, hq_prime, _hq_dvd_boundary, hq_not_mem⟩ :=
    cosmic_boundary_demands_new_prime s hs
  refine ⟨q, ?_, hq_prime⟩
  -- q < n だと、q は s に入ってしまい矛盾
  by_contra hq_not_ge
  have hq_lt : q < n := by omega
  have hq_mem_s : q ∈ s := by
    dsimp [s]
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr hq_lt, hq_prime⟩
  exact hq_not_mem hq_mem_s

/-- mathlib 既存定理 -/
theorem euclid_from_mathlib :
    EuclidPrimesInfinite := by
  exact Nat.exists_infinite_primes

/-- 宇宙式ルートと mathlib の突合 -/
theorem euclid_cosmic_matches_mathlib :
    euclid_from_cosmic_boundary = euclid_from_mathlib := by
  exact Subsingleton.elim _ _
-- `Prop` の証明同士なので、Lean では proof irrelevance により等しい。

example :
    EuclidPrimesInfinite =
      (∀ n : ℕ, ∃ p : ℕ, n ≤ p ∧ Nat.Prime p) := by
  rfl

end DkMath.CosmicFormula

-- ========================================================

def IsPrime (n : Nat) := 1 < n ∧ ∀ k, 1 < k → k < n → ¬ k ∣ n

theorem InfinitudeOfPrimes : ∀ n, ∃ p > n, IsPrime p := by
  intro n
  rcases DkMath.CosmicFormula.euclid_from_cosmic_boundary (n + 1) with
    ⟨p, hp_ge, hp_prime⟩
  refine ⟨p, ?_, ?_⟩
  · omega
  · constructor
    · exact hp_prime.one_lt
    · intro k hk_one hk_lt hk_dvd
      rcases hp_prime.eq_one_or_self_of_dvd k hk_dvd with hk_eq_one | hk_eq_p
      · rw [hk_eq_one] at hk_one
        omega
      · rw [hk_eq_p] at hk_lt
        omega
