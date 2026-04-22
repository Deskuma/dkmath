/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/


import DkMath.ABC.Core

#print "file: DkMath.ABC.ChernoffBasic"

set_option linter.style.longLine false
set_option linter.style.emptyLine false

namespace DkMath.ABC

open scoped BigOperators

open Nat Real Rat Filter Finset
open MeasureTheory ProbabilityTheory

namespace Chernoff

def Nmul (n : ℕ) : ℕ := Nat.mul n n
def n2a0 (n : ℕ) : ℕ := Nmul n
def n2mul (n : ℕ) : ℕ := 2 * n

example : n2a0 3 = 9 := by rw [n2a0, Nmul, Nat.mul_eq]
example : n2a0 7 = 49 := by rfl
example : n2a0 11 = 121 := by simp [n2a0, Nmul]

def n2a1 (n : ℕ) : ℕ := 2 * n + 1
def n2a2 (n : ℕ) : ℕ := 2 * n + 2
def n2a3' (n : ℕ) : ℕ := 2 * (n + 1) + 1
def n2a3 (n : ℕ) : ℕ := 2 * n + 3

lemma n2a3_to_1 (n : ℕ) : n2a3' n = n2a1 (n + 1) := by rw [n2a3', n2a1]
lemma n2a3_to_2 (n : ℕ) : n2a3' n = n2a2 n + 1 := by rw [n2a3', n2a2]; ring_nf
lemma n2a3_eq (n : ℕ) : n2a3 n = n2a3' n := rfl

lemma n2a1_eq_2 (n : ℕ) : n2a1 n + 1 = n2a2 n := by
  rw [n2a2, n2a1]

example : ∀ n : ℕ, n2a3' n = n2a1 (n + 1) := fun n => n2a3_eq n
example (n : ℕ) : n2a3' n = n2a1 (n + 1) := n2a3_eq n
example (n : ℕ) : n2a3 n = n2a3' n := rfl
example (n : ℕ) : n2a3 n = n2a2 n + 1 := rfl

@[simp] abbrev Vp (p n : ℕ) : ℕ := padicValNat p (2 * n + 1)
@[simp] abbrev Vp' (p n : ℕ) : ℕ := padicValNat p (n2a1 n)

lemma Vp_nonneg (p n : ℕ) : 0 ≤ Vp p n := by
  exact Nat.zero_le _

def Vp1 (p n : ℕ) : ℕ := Vp p n

lemma Vp_eq_Vp1 (p n : ℕ) : Vp p n = Vp1 p n := by rfl

def Excess (p : ℕ) (γ : ℝ) (n : ℕ) : Prop :=
  ((Vp p n : ℤ) : ℝ) - 2 > γ

def Excess' (p : ℕ) (γ : ℝ) (n : ℕ) : Prop :=
  ↑(Int.subNatNat (Vp p n) 2) > γ

example (p : ℕ) (γ : ℝ) (n : ℕ) : Excess p γ n ↔ ((Vp p n : ℤ) : ℝ) - 2 > γ :=
  Iff.rfl

example (p : ℕ) (γ : ℝ) (n : ℕ) : Excess' p γ n ↔ ↑(Int.subNatNat (Vp p n) 2) > γ :=
  Iff.rfl

lemma subNatNat_lt_two_cases (k : ℕ) (hk : ¬k.succ ≥ 2) :
  Int.subNatNat k.succ 2 = ↑k + 1 - 2 := by
  cases k
  case zero =>
    rw [Int.subNatNat]
    simp
  case succ k' =>
    have hk' : k' = 0 := by linarith
    rw [hk']
    simp

lemma subNatNat_lt_two {k : ℕ} (hk : k.succ < 2) : Int.subNatNat k.succ 2 = -(2 - k.succ : ℤ) := by
  have hk0 : k = 0 := by linarith
  rw [hk0]
  rfl

lemma subNatNat_lt_two' {k : ℕ} (hk : ¬k.succ ≥ 2) : Int.subNatNat k.succ 2 = -(2 - k.succ : ℤ) := by
  have hk0 : k = 0 := by linarith
  rw [hk0]
  rfl

lemma subNatNat_ge_two {k : ℕ} : Int.subNatNat k.succ 2 = (k.succ - 2 : ℤ) := by
  rw [Int.subNatNat]
  rfl

lemma Excess_iff (p : ℕ) (γ : ℝ) (n : ℕ) :
  Excess p γ n ↔ Excess' p γ n := by
  simp only [Excess, Excess']
  cases h : Vp p n
  case zero =>
    simp [Int.subNatNat]
  case succ k =>
    if hge : k.succ ≥ 2 then
      rw [subNatNat_ge_two]
      simp
    else
      have : Int.subNatNat k.succ 2 = -(2 - k.succ : ℤ) := subNatNat_lt_two' hge
      rw [this]
      simp only [Nat.cast_add, Nat.cast_one, Int.cast_add, Int.cast_natCast, Int.cast_one,
        gt_iff_lt, Nat.succ_eq_add_one, neg_sub, Int.cast_sub, Int.cast_ofNat]

def pge3 (p : ℕ) : Prop := p ≥ 3
def ple3 (p : ℕ) : Prop := p ≤ 3
def xge3 (X : ℕ) : Prop := X ≥ 3

def const_C : ℕ := 5
def const_K : ℕ := 4
def const_X : ℕ := 100

def C_sub : ℝ := const_C - 1

def primesUpTo (n : ℕ) : Finset ℕ :=
  Finset.filter (fun (p : ℕ) => p.Prime ∧ p ≥ 3) (Finset.range (2 * n + 2))

lemma prime_mem_primesUpTo_of_dvd_odd {p n X : ℕ} (hnX : n ≤ X) (hp : p.Prime) (hp3 : 3 ≤ p) (hp_dvd : p ∣ (2 * n + 1)) :
  p ∈ primesUpTo X := by
  have h1 : p ≤ 2 * n + 1 := Nat.le_of_dvd (Nat.succ_pos (2 * n)) hp_dvd
  have h2 : 2 * n + 1 ≤ 2 * X + 1 := by nlinarith [hnX]
  have hp_le : p ≤ 2 * X + 1 := le_trans h1 h2
  have hlt : p < 2 * X + 2 := Nat.lt_succ_of_le hp_le
  have hmem : p ∈ Finset.range (2 * X + 2) := Finset.mem_range.mpr hlt
  let H : p ∈ Finset.range (2 * X + 2) ∧ (p.Prime ∧ p ≥ 3) := And.intro hmem (And.intro hp hp3)
  exact Finset.mem_filter.mpr H

lemma prime_mem_primesUpTo_of_dvd_odd' {p n X : ℕ} (hnX : n ≤ X) (hp : p.Prime) (hp3 : 3 ≤ p) (hp_dvd : p ∣ n2a1 n) :
  p ∈ primesUpTo X := by
  have h1 : p ≤ n2a1 n := Nat.le_of_dvd (Nat.succ_pos (2 * n)) hp_dvd
  have h2 : n2a1 n ≤ n2a1 X := by rw [n2a1, n2a1]; nlinarith [hnX]
  have hp_le : p ≤ n2a1 X := le_trans h1 h2
  have hlt : p < n2a2 X := Nat.lt_succ_of_le hp_le
  have hmem : p ∈ Finset.range (n2a2 X) := Finset.mem_range.mpr hlt
  let H : p ∈ Finset.range (n2a2 X) ∧ (p.Prime ∧ p ≥ 3) := And.intro hmem (And.intro hp hp3)
  exact Finset.mem_filter.mpr H

def Vp_sub (p n : ℕ) : ℕ := Vp p (n - 1)
def Vp_add (p n : ℕ) : ℕ := Vp p (n + 1)

example (p n : ℕ) : Vp_sub p n = Vp p (n - 1) := by rw [Vp_sub, Vp]
example (p n : ℕ) : Vp_add p n = Vp p (n + 1) := rfl
example (p n : ℕ) (hn : n > 0) : Vp_sub p n = padicValNat p (2 * n - 1) := by
  rw [Vp_sub, Vp]
  rw [two_mul, two_mul]
  have h1 : 1 ≤ n := Nat.succ_le_of_lt hn
  have : (n - 1) + (n - 1) + 1 = (n + n) - 1 := by
    calc (n - 1) + (n - 1) + 1 = (n - 1) + ((n - 1) + 1) := by rw [add_assoc]
      _ = (n - 1) + n := by rw [Nat.sub_add_cancel h1]
      _ = n + (n - 1) := by rw [add_comm]
      _ = (n + n) - 1 := by rw [← Nat.add_sub_assoc h1]
  rw [this]
example (p n : ℕ) (hn : n > 0) : Vp_sub p n = padicValNat p (2 * n - 1) := by
  rw [Vp_sub, Vp]
  rw [two_mul, two_mul]
  have h : (n - 1 + (n - 1) + 1) = (n + n - 1) := by
    omega
  rw [h]
example (p n : ℕ) : Vp_sub p n = padicValNat p (2 * (n - 1) + 1) := by rw [Vp_sub, Vp]
example (p n : ℕ) : Vp_add p n = padicValNat p (2 * n + 3) := rfl
example (p n : ℕ) : Vp_add p n = padicValNat p (n2a3 n) := rfl

lemma card_filter_le_exp_markov {α}
    (s : Finset α) (Z : α → ℝ) (γ t : ℝ) (ht : 0 ≤ t) :
    (s.filter (fun a => Z a ≥ γ)).card
      ≤ Real.exp (-t*γ) * ∑ a ∈ s, Real.exp (t * Z a) := by
  classical
  have h1 :
      (s.filter (fun a => Z a ≥ γ)).card
        ≤ ∑ a ∈ s, (if Z a ≥ γ then (1 : ℝ) else 0) := by
    trans (∑ a ∈ s.filter (fun a => Z a ≥ γ), (1 : ℝ))
    · norm_cast
      simp [Finset.sum_const]
    · have : ∑ a ∈ s.filter (fun a => Z a ≥ γ), (1 : ℝ) = ∑ a ∈ s, (if Z a ≥ γ then 1 else 0) := by
        apply Finset.sum_filter
      exact le_of_eq this
  have h2 :
      ∀ a, (if Z a ≥ γ then (1 : ℝ) else 0)
          ≤ Real.exp (-t*γ) * Real.exp (t * Z a) := by
    intro a; by_cases h : Z a ≥ γ
    · simp only [h, ite_true]
      have : (1 : ℝ) ≤ Real.exp (t * (Z a - γ)) := by
        rw [Real.one_le_exp_iff]
        apply mul_nonneg ht
        linarith
      calc (1 : ℝ)
          ≤ Real.exp (t * (Z a - γ)) := this
        _ = Real.exp (t * Z a + (-t * γ)) := by ring_nf
        _ = Real.exp (t * Z a) * Real.exp (-t * γ) := by rw [Real.exp_add]
        _ = Real.exp (-t * γ) * Real.exp (t * Z a) := by ring
    · simp only [ge_iff_le, h, ↓reduceIte, neg_mul]
      positivity
  have := Finset.sum_le_sum (s := s) (by intro a ha; exact h2 a)
  have : ∑ a ∈ s, (if Z a ≥ γ then (1 : ℝ) else 0)
           ≤ Real.exp (-t*γ) * ∑ a ∈ s, Real.exp (t * Z a) := by
    calc ∑ a ∈ s, (if Z a ≥ γ then (1 : ℝ) else 0)
        ≤ ∑ a ∈ s, Real.exp (-t*γ) * Real.exp (t * Z a) := this
      _ = Real.exp (-t*γ) * ∑ a ∈ s, Real.exp (t * Z a) := by rw [← Finset.mul_sum]
  exact le_trans h1 this

lemma t_bound_log2_div_log3 :
    Real.log 2 / (2 * Real.log 3) ≤ Real.log 2 / Real.log 3 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num : (1:ℝ) < 2)
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num : (1:ℝ) < 3)
  have : Real.log 3 ≤ 2 * Real.log 3 := by linarith
  exact div_le_div_of_nonneg_left (le_of_lt hlog2) hlog3 this

lemma absorb_constant_4_to_5 (X : ℕ) (hX : const_X ≤ X) :
    (4 : ℝ) * (X + 1) ≤ const_C * X := by
  have : (4:ℝ) * (↑X + 1) = 4 * ↑X + 4 := by ring
  have h4_le_constX : 4 ≤ const_X := by norm_num [const_X]
  have h4_le_X : 4 ≤ X := by linarith [hX, h4_le_constX]
  have h_nat : 4 * X + 4 ≤ const_C * X := by
    rw [const_C]
    linarith
  have h_real : (4 : ℝ) * ↑X + 4 ≤ 5 * ↑X := by exact_mod_cast h_nat
  rw [this]
  exact h_real

end Chernoff

end DkMath.ABC
