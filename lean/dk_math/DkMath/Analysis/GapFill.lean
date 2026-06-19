/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Analysis.GapGN

#print "file: DkMath.Analysis.GapFill"

/-!
# Filling the gap between two observations

`gapLine` scans the affine segment from `u₁` to `u₂`. `gapFill` observes that
segment through the power map. Algebraic endpoint formulas are separated from
the ordered real bridge.
-/

namespace DkMath.Analysis

/-- Affine scan from `u₁` to `u₂` with parameter `t`. -/
def gapLine {R : Type*} [Ring R] (u₁ u₂ t : R) : R :=
  u₁ + t * (u₂ - u₁)

/-- Power observation along the affine gap line. -/
def gapFill {R : Type*} [Ring R] (d : ℕ) (u₁ u₂ t : R) : R :=
  gapLine u₁ u₂ t ^ d

/-- The gap line starts at `u₁`. -/
@[simp]
theorem gapLine_zero {R : Type*} [Ring R] (u₁ u₂ : R) :
    gapLine u₁ u₂ 0 = u₁ := by
  simp [gapLine]

/-- The gap line ends at `u₂`. -/
@[simp]
theorem gapLine_one {R : Type*} [Ring R] (u₁ u₂ : R) :
    gapLine u₁ u₂ 1 = u₂ := by
  simp [gapLine]

/-- The powered gap fill starts at `u₁^d`. -/
@[simp]
theorem gapFill_zero {R : Type*} [Ring R] (d : ℕ) (u₁ u₂ : R) :
    gapFill d u₁ u₂ 0 = u₁ ^ d := by
  simp [gapFill]

/-- The powered gap fill ends at `u₂^d`. -/
@[simp]
theorem gapFill_one {R : Type*} [Ring R] (d : ℕ) (u₁ u₂ : R) :
    gapFill d u₁ u₂ 1 = u₂ ^ d := by
  simp [gapFill]

/--
The endpoint change of a powered gap fill is exactly its width times `gapGN`.
-/
theorem gapFill_endpoint_sub_eq
    {R : Type*} [CommRing R] (d : ℕ) (u₁ u₂ : R) :
    gapFill d u₁ u₂ 1 - gapFill d u₁ u₂ 0
      = (u₂ - u₁) * gapGN d u₁ (u₂ - u₁) := by
  rw [gapFill_one, gapFill_zero]
  have hbase : u₁ + (u₂ - u₁) = u₂ := by ring
  simpa only [hbase] using
    (pow_add_sub_pow_eq_delta_mul_gapGN d u₁ (u₂ - u₁))

/-- For `t` in `[0,1]`, the real gap line stays between ordered endpoints. -/
theorem gapLine_mem_Icc
    {u₁ u₂ t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (hle : u₁ ≤ u₂) :
    gapLine u₁ u₂ t ∈ Set.Icc u₁ u₂ := by
  have hdelta : 0 ≤ u₂ - u₁ := sub_nonneg.mpr hle
  have hmul_nonneg : 0 ≤ t * (u₂ - u₁) := mul_nonneg ht.1 hdelta
  have hmul_le : t * (u₂ - u₁) ≤ u₂ - u₁ := by
    exact mul_le_of_le_one_left hdelta ht.2
  constructor <;> simp only [gapLine, Set.mem_Icc] at *
  · linarith
  · linarith

/--
On a nonnegative ordered real interval, the powered gap fill stays between the
powered endpoint values.
-/
theorem gapFill_mem_Icc_of_nonneg
    {d : ℕ} {u₁ u₂ t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (hu₁ : 0 ≤ u₁) (hle : u₁ ≤ u₂) :
    gapFill d u₁ u₂ t ∈ Set.Icc (u₁ ^ d) (u₂ ^ d) := by
  have hline := gapLine_mem_Icc ht hle
  have hline_nonneg : 0 ≤ gapLine u₁ u₂ t := hu₁.trans hline.1
  constructor
  · exact pow_le_pow_left₀ hu₁ hline.1 d
  · exact pow_le_pow_left₀ hline_nonneg hline.2 d

end DkMath.Analysis
