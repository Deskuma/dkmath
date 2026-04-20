/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.ABC.Basic
import DkMath.ABC.Rad

#print "file: DkMath.ABC.Core"

set_option linter.style.longLine false
set_option linter.style.emptyLine false
set_option linter.style.whitespace false

/-
  RpowExtras.lean
  小さな補題群：Real.rpow に関する nat 乗換えと分母正性補題
  目的：ABCMiddle の幾何和変形を安定化する
-/

namespace RpowExtras

open Real

/-- x > 0 かつ任意の k : ℕ に対して x^{a * k} = (x^a)^k となる補題。 -/
lemma rpow_mul_nat {x a : ℝ} (hx : 0 < x) :
  ∀ k : ℕ, Real.rpow x (a * (k : ℝ)) = (Real.rpow x a) ^ k := by
  intro k; induction k with
  | zero => simp only [CharP.cast_eq_zero, mul_zero, rpow_eq_pow, rpow_zero, pow_zero]
  | succ k ih =>
      have : a * ((k + 1 : ℕ) : ℝ) = a * (k : ℝ) + a := by
        simp [mul_add, Nat.cast_add, Nat.cast_one]
      calc
        Real.rpow x (a * ((k + 1 : ℕ) : ℝ)) = Real.rpow x (a * (k : ℝ) + a) := by rw [this]
        _ = Real.rpow x (a * (k : ℝ)) * Real.rpow x a := by simp [Real.rpow_add hx]
        _ = (Real.rpow x a) ^ (k + 1) := by
          rw [ih]
          rw [pow_succ]

/-- 2^(α+ε) > 1 when α+ε > 0 (helper) -/
lemma one_lt_rpow_two {a : ℝ} (h : 0 < a) : 1 < (2 : ℝ) ^ a := by
  have : (1 : ℝ) < 2 := by norm_num
  exact Real.one_lt_rpow this (by exact_mod_cast h)

/-- (2^a - 1) > 0 when a > 0 -/
lemma denom_pos {a : ℝ} (h : 0 < a) : 0 < (2 : ℝ) ^ a - 1 := by
  have h1 := one_lt_rpow_two (a:=a) h
  linarith

end RpowExtras

-- ------------------------------------------------------------------------------------------------------------------------------------

namespace DkMath.ABC

open scoped BigOperators

open Nat Real Rat Filter Finset
open MeasureTheory ProbabilityTheory

-- Auxiliary lemma: 3^(X+1) ≥ 2X+1 for all X (帰納法で証明)
lemma three_pow_ge_linear (X : ℕ) : 3 ^ (X + 1) ≥ 2 * X + 1 := by
  induction X with
  | zero =>
      norm_num
  | succ n ih =>
      -- 3^(n+2) = 3 * 3^(n+1) ≥ 3 * (2n+1) = 6n+3 ≥ 2(n+1)+1
      have : (3 : ℕ) ^ (n + 2) = 3 * 3 ^ (n + 1) := by
        rw [Nat.pow_succ]; ring
      calc
        3 ^ (n + 2)
            = 3 * 3 ^ (n + 1) := this
        _ ≥ 3 * (2 * n + 1) := Nat.mul_le_mul_left _ ih
        _ = 6 * n + 3 := by ring
        _ ≥ 2 * (n + 1) + 1 := by omega

-- 補助補題：v_p(n) の分解
lemma padicValNat_split (p n : ℕ) :
    padicValNat p n = min (padicValNat p n) 1 + max (padicValNat p n - 1) 0 := by
  by_cases h : padicValNat p n = 0
  · simp [h]
  · by_cases h1 : padicValNat p n = 1
    · simp [h1]
    · have : padicValNat p n ≥ 2 := by omega
      have : min (padicValNat p n) 1 = 1 := by omega
      have : max (padicValNat p n - 1) 0 = padicValNat p n - 1 := by omega
      omega

/- ============================================================================
     0. Basic helpers & notations
   ============================================================================ -/

-- NOTE: the two definitions below currently have no references (2025/09/07)

/-- squarefull: 任意の素因子 p に対して p^2 ∣ n が成り立つこと -/
def squarefull' (n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ n → p^2 ∣ n

/-- squarefree（mathlib の標準定義を本ファイルに鏡像として置く） -/
-- alias to Mathlib's predicate
def squarefree_prop (n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ n → ¬ (p^2 ∣ n)

/- ============================================================================
     1. gcd / coprimality lemmas
   ============================================================================ -/

-- ※以下４つはここだけ 2025/09/07  3:37
/-- (n + 1) - n = 1 であること -/
def succ_sub_self (n : ℕ) : (n + 1) - n = 1 := by
  rw [Nat.add_comm, Nat.add_sub_cancel]

/-- n ∣ 1 ↔ n = 1 であること -/
def dvd_one_iff (n : ℕ) : n ∣ 1 ↔ n = 1 := by
  constructor
  · rintro h
    exact Nat.eq_one_of_dvd_one h
  · rintro rfl
    exact ⟨1, rfl⟩

/-- (n, n + 1) が互いに素であること -/
lemma gcd_succ (n : ℕ) : Nat.gcd n (n+1) = 1 := by
  -- standard: gcd n (n+1) = 1
  have h := Nat.dvd_sub (Nat.gcd_dvd_right n (n+1)) (Nat.gcd_dvd_left n (n+1))
  have : Nat.gcd n (n+1) ∣ 1 := by
    rw [succ_sub_self] at h
    exact h
  exact (dvd_one_iff (Nat.gcd n (n+1))).1 this

/-- (n, n + 1) が互いに素であること -/
lemma coprime_succ (n : ℕ) : Nat.Coprime n (n+1) := by
  -- follows from gcd_succ
  rw [Nat.coprime_iff_gcd_eq_one]
  exact gcd_succ n

/- ============================================================================
     2. rad: definition + basic facts
   ============================================================================ -/

-- `DkMath.ABC.Rad` に `rad` 定義補題を移動した (2026/04/20 17:35)

#check rad

-- radical kernel の補題群は `DkMath.ABC.Rad` に集約した (2026/04/20)。

/- ============================================================================
     3. squarefree / squarefull controls
   ============================================================================ -/


/-- mathlib 標準を ℕ にエイリアス（再利用を最大化） -/
/-
An element of a monoid is squarefree if the only squares that
divide it are the squares of units.

def Squarefree [Monoid R] (r : R) : Prop :=
  ∀ x : R, x * x ∣ r → IsUnit x
-/
-- #check Squarefree -- mathlib の定義を確認
-- Squarefree.{u_1} {R : Type u_1} [Monoid R] (r : R) : Prop
abbrev squarefree (n : ℕ) : Prop := Squarefree n

/-- squarefull: すべての素因子が指数 ≥ 2 -/
def squarefull (n : ℕ) : Prop :=
  ∀ p, p.Prime → p ∣ n → p^2 ∣ n

-- #eval squarefree 6  -- true
-- #eval squarefree 9  -- false
-- #eval squarefree 12 -- false
-- #eval squarefree 30 -- true

end DkMath.ABC

-- ------------------------------------------------------------------------------------------------------------------------------------
