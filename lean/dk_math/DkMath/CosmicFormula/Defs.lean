/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib
import DkMath.CellDim  -- Cell Dimensionality

#print "file: DkMath.CosmicFormula.Defs"

namespace DkMath.CosmicFormula

-- ----------------------------------------------------------------------------
-- Note: This file contains the basic definitions related to the Cosmic Formula.
-- ----------------------------------------------------------------------------

-- #Big, #Body, #Gap の定義

-- 二項定理公式の指数部

/-- d-n-k -/
def d_sub_n_k (d n k : ℕ) : ℕ :=
  d - n - k

/-- d-1-k -/
def d_sub_one_k (d k : ℕ) : ℕ :=
  d_sub_n_k d 1 k

/-- d_sub_one_k = d - 1 - k -/
lemma d_sub_one_k_eq (d k : ℕ) :
    d_sub_one_k d k = d - 1 - k := by
  simp [d_sub_one_k, d_sub_n_k]

/-- d - (k + 1) = d_sub_one_k d k -/
lemma d_sub_one_k_eq' (d k : ℕ) :
    d - (k + 1) = d_sub_one_k d k := by
  rw [d_sub_one_k_eq, add_comm, Nat.sub_sub]

/-- d-k = d-0-k -/
lemma d_sub_k_eq_d_sub_zero_k (d k : ℕ) :
    d_sub_n_k d 0 k = d - k := by
  simp [d_sub_n_k]

abbrev d1k := d_sub_one_k  -- d-1-k の略称
abbrev dk := d_sub_n_k  -- d-k の略称

-- 二項定理公式の項 G の定義

/-- Cosmic Formula の項 G の定義 -/
def G (R : Type*) [CommSemiring R] (x u : R) (d : ℕ) : R :=
  ∑ k ∈ Finset.range d, (Nat.choose d (k + 1) : R) * x ^ (k + 1) * u ^ (d1k d k)

/-- Cosmic Formula の一般項 Gn の定義 -/
def Gn (R : Type*) [CommSemiring R] (x u : R) (d n : ℕ) : R :=
  ∑ k ∈ Finset.range d, (Nat.choose d (k + n) : R) * x ^ k * u ^ (d_sub_n_k d n k)

#eval G ℝ 2 1 1  -- テスト評価

/-- 大宇宙式 Big Cosmic Formula -/
def Big (x u : ℝ) (d : ℕ) : ℝ := (x + u)^d

/-- 宇宙式の本体 Body of Cosmic Formula -/
def Body (x u : ℝ) (d : ℕ) : ℝ := G ℝ x u d

/-- 宇宙式の隙間 Gap of Cosmic Formula -/
def Gap (_x u : ℝ) (d : ℕ) : ℝ := (u : ℝ)^d

/-- Cosmic Formula の恒等式 -/
example (x u : ℝ) (d : ℕ) :
    Big x u d = Body x u d + Gap x u d := by
  simp only [Big, Body, G, Gap]
  rw [add_pow]
  -- split the sum over range (d + 1) into the sum over range d (shifted) and the k = 0 term
  rw [Finset.sum_range_succ']
  -- simplify the k = 0 term (choose d 0 = 1, x^0 = 1) and normalize exponents
  simp only [d_sub_one_k_eq', pow_zero, tsub_zero, one_mul, Nat.choose_zero_right, Nat.cast_one,
    mul_one, add_left_inj]
  -- reorder multiplication in each summand using commutativity/associativity
  apply Finset.sum_congr rfl
  intro _ _
  ring

end DkMath.CosmicFormula
