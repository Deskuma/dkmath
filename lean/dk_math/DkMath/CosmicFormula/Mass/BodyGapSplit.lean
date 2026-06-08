/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib

#print "file: DkMath.CosmicFormula.Mass.BodyGapSplit"

namespace DkMath.CosmicFormula.Mass

/-!
## Body/Gap split records

These records package already-proved decomposition identities so later bridge
layers can transport the same structure across binomial, mass, probability, and
descent contexts without re-expanding the underlying formula.
-/

/-- A named additive split `big = body + gap`. -/
structure BodyGapSplit (R : Type _) [Add R] where
  big : R
  body : R
  gap : R
  split : big = body + gap

/--
A named kernel split `big = boundary + gapAxis * kernel`.

The intended reading is that removing the boundary leaves a tail carried by
the gap axis.
-/
structure BodyGapKernelSplit (R : Type _) [Add R] [Mul R] where
  big : R
  boundary : R
  gapAxis : R
  kernel : R
  split : big = boundary + gapAxis * kernel

namespace BodyGapSplit

variable {R : Type _} [Add R]

/-- Rewrite the big mass through its stored split. -/
theorem rewrite_big (S : BodyGapSplit R) :
    S.big = S.body + S.gap :=
  S.split

/-- In `ℕ`, the body part is bounded by the big part. -/
theorem body_le_big_nat (S : BodyGapSplit ℕ) :
    S.body ≤ S.big := by
  rw [S.split]
  exact Nat.le_add_right S.body S.gap

/-- In `ℕ`, the gap part is bounded by the big part. -/
theorem gap_le_big_nat (S : BodyGapSplit ℕ) :
    S.gap ≤ S.big := by
  rw [S.split]
  exact Nat.le_add_left S.gap S.body

end BodyGapSplit

namespace BodyGapKernelSplit

variable {R : Type _} [Add R] [Mul R]

/-- The tail determined by a kernel split. -/
def tail (S : BodyGapKernelSplit R) : R :=
  S.gapAxis * S.kernel

/-- Rewrite the big mass through its stored kernel split. -/
theorem rewrite_big (S : BodyGapKernelSplit R) :
    S.big = S.boundary + S.gapAxis * S.kernel :=
  S.split

/-- The stored tail is definitionally the gap axis times the kernel. -/
theorem tail_eq_gapAxis_mul_kernel (S : BodyGapKernelSplit R) :
    S.tail = S.gapAxis * S.kernel :=
  rfl

/-- Forget a kernel split down to the additive boundary/tail split. -/
def toBodyGapSplit (S : BodyGapKernelSplit R) : BodyGapSplit R where
  big := S.big
  body := S.boundary
  gap := S.tail
  split := by
    simpa [tail] using S.split

/-- In `ℕ`, subtracting the boundary leaves the stored tail. -/
theorem big_sub_boundary_eq_tail_nat (S : BodyGapKernelSplit ℕ) :
    S.big - S.boundary = S.tail := by
  unfold tail
  exact Nat.sub_eq_of_eq_add (by simpa [add_comm] using S.split)

/-- In `ℕ`, subtracting the boundary leaves `gapAxis * kernel`. -/
theorem big_sub_boundary_eq_gapAxis_mul_kernel_nat
    (S : BodyGapKernelSplit ℕ) :
    S.big - S.boundary = S.gapAxis * S.kernel := by
  rw [big_sub_boundary_eq_tail_nat]
  rfl

/-- In `ℕ`, the stored tail is divisible by the gap axis. -/
theorem gapAxis_dvd_tail_nat (S : BodyGapKernelSplit ℕ) :
    S.gapAxis ∣ S.tail := by
  unfold tail
  exact dvd_mul_right S.gapAxis S.kernel

/-- In `ℕ`, the boundary is bounded by the big part. -/
theorem boundary_le_big_nat (S : BodyGapKernelSplit ℕ) :
    S.boundary ≤ S.big :=
  BodyGapSplit.body_le_big_nat S.toBodyGapSplit

/-- In `ℕ`, the tail is bounded by the big part. -/
theorem tail_le_big_nat (S : BodyGapKernelSplit ℕ) :
    S.tail ≤ S.big :=
  BodyGapSplit.gap_le_big_nat S.toBodyGapSplit

end BodyGapKernelSplit

end DkMath.CosmicFormula.Mass
