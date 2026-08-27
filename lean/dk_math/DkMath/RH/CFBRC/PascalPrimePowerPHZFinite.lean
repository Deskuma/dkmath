/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.PascalPrimePowerModeBridge
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.PascalPrimePowerPHZFinite"

/-!
# Finite prime-power PHZ with a natural-number cutoff

This module turns the rectangular PPW-008 ladder into the finite, natural
cutoff suggested by the prime-power condition `p ^ (k + 1) ≤ X`.  The outer
prime support and the exponent search are both finite, so every identity here
is an exact finite identity.  The module deliberately makes no analytic claim
about the von Mangoldt function, `-ζ'/ζ`, zeros, or RH.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open DkMath.NumberTheory
open DkMath.NumberTheory.PrimitiveSet

/-- Natural cutoff for the finite prime-power shadow wave.

The range on `k` is only a finite search envelope; the actual mathematical
cutoff is the displayed prime-power test `p ^ (k + 1) ≤ X`.
-/
noncomputable def pascalPrimePowerPHZFiniteUpTo
    (X : ℕ) (s : ℂ) : ℂ :=
  ∑ p ∈ pascalPrimeCoordinateSupportUpTo X,
    ∑ k ∈ Finset.range X,
      if p ^ (k + 1) ≤ X then
        (Real.log (p : ℝ) : ℂ) * eulerPrimePowerMode p (k + 1) s
      else 0

/-- The zero cutoff contains no prime-power terms. -/
@[simp] theorem pascalPrimePowerPHZFiniteUpTo_zero (s : ℂ) :
    pascalPrimePowerPHZFiniteUpTo 0 s = 0 := by
  simp [pascalPrimePowerPHZFiniteUpTo, pascalPrimeCoordinateSupportUpTo]

/-- The unit cutoff contains no positive prime power. -/
@[simp] theorem pascalPrimePowerPHZFiniteUpTo_one (s : ℂ) :
    pascalPrimePowerPHZFiniteUpTo 1 s = 0 := by
  unfold pascalPrimePowerPHZFiniteUpTo
  apply Finset.sum_eq_zero
  intro p hp
  have hprime : Nat.Prime p :=
    (mem_pascalPrimeCoordinateSupportUpTo_iff.mp hp).1
  have hp_le : p ≤ 1 := (mem_pascalPrimeCoordinateSupportUpTo_iff.mp hp).2
  exfalso
  exact (Nat.not_le_of_lt hprime.one_lt) hp_le

/-- The finite PHZ is exactly its natural-cutoff `(p,k)` pair sum. -/
theorem pascalPrimePowerPHZFiniteUpTo_eq_pair_sum (X : ℕ) (s : ℂ) :
    pascalPrimePowerPHZFiniteUpTo X s =
      ∑ p ∈ pascalPrimeCoordinateSupportUpTo X,
        ∑ k ∈ Finset.range X,
          if p ^ (k + 1) ≤ X then
            (Real.log (p : ℝ) : ℂ) * eulerPrimePowerMode p (k + 1) s
          else 0 := by
  rfl

/-- Exponent-normalized form of the natural-cutoff pair sum.

For a prime `p`, the mode is the `(k+1)`st power of the primitive Euler mode;
the theorem exposes that exact finite normal form without introducing a
choice of a prime-power representation.
-/
theorem pascalPrimePowerPHZFiniteUpTo_eq_primitive_pair_sum (X : ℕ) (s : ℂ) :
    pascalPrimePowerPHZFiniteUpTo X s =
      ∑ p ∈ pascalPrimeCoordinateSupportUpTo X,
        ∑ k ∈ Finset.range X,
          if p ^ (k + 1) ≤ X then
            (Real.log (p : ℝ) : ℂ) *
              (eulerPrimePrimitiveMode p s) ^ (k + 1)
          else 0 := by
  unfold pascalPrimePowerPHZFiniteUpTo
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro k hk
  simp only [eulerPrimePowerMode]

/-- Label-cost presentation of the same finite shadow.

The prime proof is recovered from support membership and is used only to form
the dependent `PrimePowerLabel`; the cutoff and summation remain unchanged.
-/
theorem pascalPrimePowerPHZFiniteUpTo_eq_label_cost_pair_sum (X : ℕ) (s : ℂ) :
    pascalPrimePowerPHZFiniteUpTo X s =
      ∑ p ∈ pascalPrimeCoordinateSupportUpTo X,
        ∑ k ∈ Finset.range X,
          if p ^ (k + 1) ≤ X then
            if hprime : Nat.Prime p then
              eulerPrimePowerShadowMode p hprime k s
            else 0
          else 0 := by
  unfold pascalPrimePowerPHZFiniteUpTo
  apply Finset.sum_congr rfl
  intro p hp
  have hprime : Nat.Prime p :=
    (mem_pascalPrimeCoordinateSupportUpTo_iff.mp hp).1
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hcut : p ^ (k + 1) ≤ X
  · simp [hcut, hprime, eulerPrimePowerShadowMode]
  · simp [hcut]

end DkMath.RH.CFBRCProjection
