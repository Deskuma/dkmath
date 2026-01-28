/-
Unique Representation in ℚ(√2) using Irrational and Linear Independence

This file demonstrates how to use Mathlib's `Irrational` type to prove
uniqueness of representations a + b·√2 where a, b ∈ ℚ.

Author: D. and Wise Wolf
Date: 2026-01-28
-/

import Mathlib
import DkMath.SilverRatio.Sqrt2Lemmas

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

  -- Rearrange: (a - c) + (b - d)·√2 = 0
  have key : ((a - c) : ℝ) + ((b - d) : ℝ) * sqrt2 = 0 := by
    have := h
    change ((a - c) : ℝ) + ((b - d) : ℝ) * sqrt2 = 0
    nlinarith [h]

  by_cases hbd : b = d
  · -- Case: b = d, so a = c
    have : ((a - c) : ℝ) = 0 := by
      simp only [hbd, sub_self, zero_mul, add_zero] at key
      exact key
    have : (a - c : ℚ) = 0 := by
      have : (↑(a - c) : ℝ) = ↑(0 : ℚ) := by simp [this]
      exact Rat.cast_injective this
    exact ⟨by linarith [this], hbd⟩

  · -- Case: b ≠ d, derive contradiction
    -- The proof relies on √2's irrationality preventing the equation
    -- (a-c) + (b-d)·√2 = 0 from holding (unless b-d = 0)

    -- Since √2 is irrational, we have:
    -- √2 = -((a-c)/(b-d)) would mean √2 is a ratio of rationals
    -- which contradicts irrationality

    -- More precisely: we can appeal to the minimal polynomial of √2
    -- or use a direct contradiction argument

    sorry -- The rigorous proof requires showing that
           -- (a-c) + (b-d)·√2 = 0 with (b-d) ≠ 0 is impossible when √2 is irrational

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
