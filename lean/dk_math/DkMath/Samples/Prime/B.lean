/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib

-- cid: 6a3bcb39-f6e4-83e8-a7a9-9ed99b987282

set_option linter.style.whitespace false
set_option linter.style.emptyLine false

-- --------------------------------------------------------

theorem cosmic_identity_ring {R : Type*} [CommRing R] (x u : R) :
    (x + u)^2 - x * (x + 2 * u) - u^2 = 0 := by
  ring

-- --------------------------------------------------------

-- 1. finite prime product と unit u の coprime 化
theorem coprime_prod_primes_of_forall_not_dvd
    (s : Finset ℕ)
    (u : ℕ)
    (hs : ∀ p ∈ s, Nat.Prime p)
    (hu : ∀ p ∈ s, ¬ p ∣ u) :
    Nat.Coprime (s.prod fun p => p) u := by
  classical

  have hcop_u_prod : Nat.Coprime u (s.prod fun p => p) := by
    exact Nat.Coprime.prod_right (by
      intro p hp
      have hpu : Nat.Coprime p u :=
        (Nat.Prime.coprime_iff_not_dvd (hs p hp)).mpr (hu p hp)
      exact hpu.symm)

  exact hcop_u_prod.symm

-- --------------------------------------------------------

-- 2. not-dvd 仮定による直接版
theorem exists_prime_not_mem_dvd_prod_add_unit
    (s : Finset ℕ)
    (u : ℕ)
    (hu_pos : 0 < u)
    (hs : ∀ p ∈ s, Nat.Prime p)
    (hu_not_dvd : ∀ p ∈ s, ¬ p ∣ u) :
    ∃ q : ℕ,
      Nat.Prime q ∧
      q ∣ (s.prod fun p => p) + u ∧
      q ∉ s := by
  classical

  let P : ℕ := s.prod fun p => p

  have hP_ne_zero : P ≠ 0 := by
    dsimp [P]
    exact Finset.prod_ne_zero_iff.mpr (by
      intro p hp
      exact (hs p hp).ne_zero)

  have hP_pos : 0 < P := Nat.pos_of_ne_zero hP_ne_zero

  have hP_ge_one : 1 ≤ P := Nat.succ_le_of_lt hP_pos
  have hu_ge_one : 1 ≤ u := Nat.succ_le_of_lt hu_pos

  have hPu_ne_one : P + u ≠ 1 := by
    intro h
    have htwo : 2 ≤ P + u := by
      calc
        2 = 1 + 1 := rfl
        _ ≤ P + u := Nat.add_le_add hP_ge_one hu_ge_one
    have hbad : 2 ≤ 1 := by
      simp [h] at htwo
    exact (by decide : ¬ 2 ≤ 1) hbad

  obtain ⟨q, hq_prime, hq_dvd⟩ :=
    (Nat.ne_one_iff_exists_prime_dvd).mp hPu_ne_one

  refine ⟨q, hq_prime, ?_, ?_⟩

  · simpa [P] using hq_dvd

  · intro hq_mem

    have hq_dvd_P : q ∣ P := by
      dsimp [P]
      exact Finset.dvd_prod_of_mem (fun p => p) hq_mem

    have hq_dvd_u : q ∣ u := by
      have h : q ∣ P + u - P := Nat.dvd_sub hq_dvd hq_dvd_P
      have hsub : P + u - P = u := by
        exact Nat.add_sub_cancel_left P u
      simpa [hsub] using h

    exact hu_not_dvd q hq_mem hq_dvd_u

-- 3. 平方境界版
theorem cosmic_unit_boundary_demands_new_prime
    (s : Finset ℕ)
    (u : ℕ)
    (hu_pos : 0 < u)
    (hs : ∀ p ∈ s, Nat.Prime p)
    (hu_not_dvd : ∀ p ∈ s, ¬ p ∣ u) :
    ∃ q : ℕ,
      Nat.Prime q ∧
      q ∣ ((s.prod fun p => p) + u)^2 ∧
      q ∉ s := by
  obtain ⟨q, hq_prime, hq_dvd, hq_not_mem⟩ :=
    exists_prime_not_mem_dvd_prod_add_unit s u hu_pos hs hu_not_dvd

  refine ⟨q, hq_prime, ?_, hq_not_mem⟩

  exact dvd_pow hq_dvd (by decide : 2 ≠ 0)

-- --------------------------------------------------------

def cosmicNReal (P u : ℝ) : ℝ :=
  (P + u)^2 - u^2

theorem cosmicNReal_boundary (P u : ℝ) :
    cosmicNReal P u + u^2 = (P + u)^2 := by
  unfold cosmicNReal
  ring

theorem cosmicNReal_eq_mul (P u : ℝ) :
    cosmicNReal P u = P * (P + 2 * u) := by
  unfold cosmicNReal
  ring

theorem cosmicNReal_nat_cast_boundary (P u : ℕ) :
    cosmicNReal (P : ℝ) (u : ℝ) + (u : ℝ)^2 =
      ((P : ℝ) + (u : ℝ))^2 := by
  simpa using cosmicNReal_boundary (P : ℝ) (u : ℝ)

theorem cosmicNReal_nat_cast_eq_mul (P u : ℕ) :
    cosmicNReal (P : ℝ) (u : ℝ) =
      (P : ℝ) * ((P : ℝ) + 2 * (u : ℝ)) := by
  simpa using cosmicNReal_eq_mul (P : ℝ) (u : ℝ)

-- --------------------------------------------------------

theorem exists_prime_not_mem_dvd_nat_add_unit_of_forall_dvd
    (s : Finset ℕ)
    (P u : ℕ)
    (hP_pos : 0 < P)
    (hu_pos : 0 < u)
    (_hs : ∀ p ∈ s, Nat.Prime p)
    (hP_dvd : ∀ p ∈ s, p ∣ P)
    (hu_not_dvd : ∀ p ∈ s, ¬ p ∣ u) :
    ∃ q : ℕ,
      Nat.Prime q ∧
      q ∣ P + u ∧
      q ∉ s := by
  classical

  have hP_ge_one : 1 ≤ P := Nat.succ_le_of_lt hP_pos
  have hu_ge_one : 1 ≤ u := Nat.succ_le_of_lt hu_pos

  have hPu_ne_one : P + u ≠ 1 := by
    intro h
    have htwo : 2 ≤ P + u := by
      calc
        2 = 1 + 1 := rfl
        _ ≤ P + u := Nat.add_le_add hP_ge_one hu_ge_one
    have hbad : 2 ≤ 1 := by
      simp [h] at htwo
    exact (by decide : ¬ 2 ≤ 1) hbad

  obtain ⟨q, hq_prime, hq_dvd⟩ :=
    (Nat.ne_one_iff_exists_prime_dvd).mp hPu_ne_one

  refine ⟨q, hq_prime, hq_dvd, ?_⟩

  intro hq_mem

  have hq_dvd_P : q ∣ P := hP_dvd q hq_mem

  have hq_dvd_u : q ∣ u := by
    have h : q ∣ P + u - P := Nat.dvd_sub hq_dvd hq_dvd_P
    have hsub : P + u - P = u := by
      exact Nat.add_sub_cancel_left P u
    simpa [hsub] using h

  exact hu_not_dvd q hq_mem hq_dvd_u

-- ========================================================

/- ### research theorems (pending) -/

-- P は素数積でなくてよい。
-- s の各素数が P を割り、u はそれらを避ければよい。
theorem exists_prime_not_mem_dvd_add_of_forall_dvd_forall_not_dvd
    (s : Finset ℕ)
    (P u : ℕ)
    (hP_pos : 0 < P)
    (hu_pos : 0 < u)
    (hs : ∀ p ∈ s, Nat.Prime p)
    (hP_dvd : ∀ p ∈ s, p ∣ P)
    (hu_not_dvd : ∀ p ∈ s, ¬ p ∣ u) :
    ∃ q : ℕ,
      Nat.Prime q ∧
      q ∣ P + u ∧
      q ∉ s := by
  -- ここは既存の +u 論法を P 一般化したもの
  sorry

-- --------------------------------------------------------

example {P u}
  (s : Finset ℕ)
  (hs : ∀ p ∈ s, Nat.Prime p)
  (hu : ∀ p ∈ s, ¬ p ∣ u) : Nat.gcd P u = 1 := by
  have hgcd : Nat.gcd (s.prod fun p => p) u = 1 :=
    (Nat.coprime_iff_gcd_eq_one).mp
      (coprime_prod_primes_of_forall_not_dvd s u hs hu)
  refine Nat.coprime_iff_gcd_eq_one.mpr ?_
  sorry


theorem exists_prime_not_mem_dvd_prod_add_unit_of_coprime'
    (s : Finset ℕ)
    (u : ℕ)
    (hu : 0 < u)
    (hs : ∀ p ∈ s, Nat.Prime p)
    (hcop : Nat.Coprime (∏ p ∈ s, p) u) :
    ∃ q : ℕ,
      Nat.Prime q ∧
      q ∣ (∏ p ∈ s, p) + u ∧
      q ∉ s := by
  sorry

theorem cosmic_unit_boundary_demands_new_prime'
    (s : Finset ℕ)
    (u : ℕ)
    (hu : 0 < u)
    (hs : ∀ p ∈ s, Nat.Prime p)
    (hcop : Nat.Coprime (∏ p ∈ s, p) u) :
    ∃ q : ℕ,
      Nat.Prime q ∧
      q ∣ ((∏ p ∈ s, p) + u)^2 ∧
      q ∉ s := by
  sorry
