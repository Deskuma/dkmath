/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib

#print "file: DkMath.Lib.NumberTheory.SquarefreePowerFactor"

/-!
# Squarefree residual extraction

This is the neutral UFD-side part of the ABC Eisenstein provider.  A
well-founded divisibility monoid admits a terminating extraction of square
factors, leaving a squarefree residual.  No choice of prime orientation or
number-theoretic counting statement is involved.
-/

namespace DkMath.Lib.NumberTheory

noncomputable section

theorem exists_squarefree_mul_sq
    {R : Type*} [CommMonoidWithZero R] [WfDvdMonoid R]
    (a : R) (ha : a ≠ 0) :
    ∃ b c : R, Squarefree b ∧ a = b * c ^ 2 := by
  classical
  revert ha
  refine (wellFounded_dvdNotUnit (α := R)).induction
    (C := fun a : R => a ≠ 0 → ∃ b c : R, Squarefree b ∧ a = b * c ^ 2) a ?_
  intro a ih ha
  by_cases hs : Squarefree a
  · exact ⟨a, 1, hs, by simp⟩
  · obtain ⟨d, hd, hdu⟩ : ∃ d : R, ∃ _ : d * d ∣ a, ¬IsUnit d := by
      simpa only [Squarefree, not_forall] using hs
    obtain ⟨q, hq⟩ := hd
    have hq0 : q ≠ 0 := by
      intro h
      simp only [h, mul_zero] at hq
      exact ha hq
    have hqa : DvdNotUnit q a := by
      refine ⟨hq0, d * d, ?_, ?_⟩
      · exact fun hu => hdu (isUnit_of_mul_isUnit_left hu)
      · rw [hq]
        ac_rfl
    obtain ⟨b, c, hb, hbc⟩ := ih q hqa hq0
    refine ⟨b, d * c, hb, ?_⟩
    simp only [hq, hbc, pow_two]
    ac_rfl

end

end DkMath.Lib.NumberTheory

#print axioms DkMath.Lib.NumberTheory.exists_squarefree_mul_sq
