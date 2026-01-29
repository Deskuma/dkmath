/-
Unique Representation in ℚ(√2) using Irrational and Linear Independence

This file demonstrates how to use Mathlib's `Irrational` type to prove
uniqueness of representations a + b·√2 where a, b ∈ ℚ.

Author: D. and Wise Wolf
Date: 2026-01-28
-/

import Mathlib
import DkMath.SilverRatio.Sqrt2Lemmas

namespace DkMath.UniqueRepresentation

open Real
open DkMath.SilverRatio.Sqrt2

noncomputable section

/-
Key Principle:
When √2 is irrational, we can use it to establish linear independence of {1, √2} over ℚ.
-/

/-- Linear independence of {1, √2} over ℚ -/
theorem sqrt2_lin_indep_over_rat (a b c d : ℚ) :
    (a : ℝ) + (b : ℝ) * sqrt2 = (c : ℝ) + (d : ℝ) * sqrt2 →
    a = c ∧ b = d := by
  intro h
  -- Rearrange to get (a - c) + (b - d)·√2 = 0
  have key : ((a - c : ℚ) : ℝ) + ((b - d : ℚ) : ℝ) * sqrt2 = 0 := by
    push_cast
    linarith [h]
  by_cases hbd : b = d
  · -- Case: b = d, so a = c
    have h' : (↑a - ↑c : ℝ) = (0 : ℝ) := by
      rw [hbd] at key
      push_cast at key
      simp only [sub_self, zero_mul] at key
      linarith [key]
    have : (a - c : ℚ) = 0 := by
      have : (↑(a - c) : ℝ) = ↑(0 : ℚ) := by simp [h']
      exact Rat.cast_injective this
    exact ⟨by linarith [this], hbd⟩
  · -- Case: b ≠ d, derive contradiction
    have h_irrat : Irrational sqrt2 := sqrt2_irrational
    -- From the key equation, if b ≠ d, then √2 = -(a-c)/(b-d)
    have hbd_ne : ↑(b - d) ≠ 0 := by
      intro h_eq
      have : (↑(b - d) : ℝ) = ↑(0 : ℚ) := by simp [h_eq]
      have : b - d = 0 := Rat.cast_injective this
      exact hbd (by linarith [this])
    have sqrt2_iso : ((b - d : ℚ) : ℝ) * sqrt2 = -((a - c : ℚ) : ℝ) := by linarith [key]
    -- From √2 = -(a-c)/(b-d), we derive a contradiction with irrationality
    exfalso
    have sqrt2_eq : sqrt2 = -(↑(a - c) / ↑(b - d)) := by
      have h1 : (↑(b - d) : ℝ) * sqrt2 = -(↑(a - c) : ℝ) := sqrt2_iso
      have : sqrt2 = (-(↑(a - c) : ℝ)) / (↑(b - d) : ℝ) := by
        field_simp [hbd_ne] at h1 ⊢
        exact h1
      simp only [neg_div] at this
      exact this
    -- The RHS is a rational number
    have hq : sqrt2 ∈ Set.range ((↑) : ℚ → ℝ) := by
      use -((a - c) / (b - d))
      simp only [Rat.cast_div, Rat.cast_neg]
      exact sqrt2_eq.symm
    -- But √2 is irrational, contradiction
    exact h_irrat hq

#print axioms sqrt2_lin_indep_over_rat

/-- Unique representation in ℚ(√2) -/
def InQAdjSqrt2 (x : ℝ) : Prop :=
  ∃ a b : ℚ, (a : ℝ) + (b : ℝ) * sqrt2 = x

theorem unique_rep_in_Q_sqrt2 (x : ℝ) (hx : InQAdjSqrt2 x) :
    ∃! (ab : ℚ × ℚ), (↑ab.1 : ℝ) + ↑ab.2 * sqrt2 = x := by
  obtain ⟨a, b, hab⟩ := hx
  use ⟨a, b⟩
  simp only [Prod.forall, Prod.mk.injEq]
  constructor
  · exact hab
  · intros a' b' hab'
    have : (a' : ℝ) + (b' : ℝ) * sqrt2 = (a : ℝ) + (b : ℝ) * sqrt2 :=
      hab' ▸ hab.symm
    have ⟨ha, hb⟩ := sqrt2_lin_indep_over_rat a' b' a b this
    exact ⟨ha, hb⟩

#print axioms unique_rep_in_Q_sqrt2

end -- noncomputable section

end DkMath.UniqueRepresentation
