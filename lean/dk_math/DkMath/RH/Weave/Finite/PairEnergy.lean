/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic

#print "file: DkMath.RH.Weave.Finite.PairEnergy"

namespace DkMath.RH.Weave.Finite

/-- Symmetric center of two complex arms. -/
noncomputable def pairCenter (a b : ℂ) : ℂ :=
  (a + b) / 2

/-- Antisymmetric offset of two complex arms. -/
noncomputable def pairOffset (a b : ℂ) : ℂ :=
  (a - b) / 2

/-- The left arm is reconstructed from center plus offset. -/
theorem pairCenter_add_pairOffset (a b : ℂ) :
    pairCenter a b + pairOffset a b = a := by
  unfold pairCenter pairOffset
  ring

/-- The right arm is reconstructed from center minus offset. -/
theorem pairCenter_sub_pairOffset (a b : ℂ) :
    pairCenter a b - pairOffset a b = b := by
  unfold pairCenter pairOffset
  ring

/-- Twice the center is the sum of the two arms. -/
theorem two_mul_pairCenter (a b : ℂ) :
    2 * pairCenter a b = a + b := by
  unfold pairCenter
  ring

/-- Twice the antisymmetric offset is the difference of the two arms. -/
theorem two_mul_pairOffset (a b : ℂ) :
    2 * pairOffset a b = a - b := by
  unfold pairOffset
  ring

/-- Exchanging the two arms preserves their center. -/
theorem pairCenter_comm (a b : ℂ) :
    pairCenter a b = pairCenter b a := by
  unfold pairCenter
  rw [add_comm]

/-- Exchanging the two arms negates their antisymmetric offset. -/
theorem pairOffset_swap (a b : ℂ) :
    pairOffset b a = -pairOffset a b := by
  unfold pairOffset
  ring

/-- Equal arms are exactly the zero-offset state. -/
theorem pairOffset_eq_zero_iff (a b : ℂ) :
    pairOffset a b = 0 ↔ a = b := by
  constructor
  · intro h
    apply sub_eq_zero.mp
    calc
      a - b = 2 * pairOffset a b := by
        rw [two_mul_pairOffset]
      _ = 0 := by simp [h]
  · intro h
    subst b
    simp [pairOffset]

/--
Pair-energy decomposition for two complex arms.

The total squared norm splits into symmetric-center energy and antisymmetric
-offset energy.  This is the finite algebraic conservation law behind the
warp/weft decomposition; no zeta or critical-line premise occurs here.
-/
theorem normSq_pair_decomposition (a b : ℂ) :
    Complex.normSq a + Complex.normSq b =
      2 * Complex.normSq (pairCenter a b) +
        2 * Complex.normSq (pairOffset a b) := by
  simp [pairCenter, pairOffset, Complex.normSq_apply]
  ring

/-- Finite sums of the two arms reconstruct twice the summed center. -/
theorem sum_pair_eq_two_mul_sum_center
    {ι : Type*} (S : Finset ι) (a b : ι → ℂ) :
    (∑ i ∈ S, a i) + (∑ i ∈ S, b i) =
      2 * ∑ i ∈ S, pairCenter (a i) (b i) := by
  calc
    (∑ i ∈ S, a i) + (∑ i ∈ S, b i) =
        ∑ i ∈ S, (a i + b i) := by
      rw [Finset.sum_add_distrib]
    _ = ∑ i ∈ S, 2 * pairCenter (a i) (b i) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [two_mul_pairCenter]
    _ = 2 * ∑ i ∈ S, pairCenter (a i) (b i) := by
      rw [Finset.mul_sum]

end DkMath.RH.Weave.Finite
