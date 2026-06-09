/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Petal.Basic

#print "file: DkMath.Petal.Forms"

/-!
# Petal Forms

This file exposes the existing `S0` / `S1` Petal detector lemmas through the
new `DkMath.Petal.*` package.

The original proofs currently live in `DkMath.FLT.PetalDetect`.  This file
intentionally gives only Petal-facing names and keeps proof ownership unchanged.
-/

namespace DkMath
namespace Petal

open DkMath.FLT.PetalDetect

/-- Petal-facing name for the `S0` difference-kernel identity. -/
theorem petal_diff_kernel (a b : ℤ) :
    S1 ℤ a b = S0 ℤ a b + a * b := by
  exact diff_kernel ℤ a b

/-- Petal-facing name for the natural-number `S0` difference-kernel identity. -/
theorem petal_diff_kernel_nat (a b : ℕ) :
    S1_nat a b = S0_nat a b + a * b := by
  exact diff_kernel_nat a b

/-- Petal-facing name for commutativity of the `S0` detector. -/
theorem petal_S0_comm (a b : ℤ) :
    S0 ℤ a b = S0 ℤ b a := by
  exact S0_comm ℤ a b

/-- Petal-facing name for commutativity of the `S1` detector. -/
theorem petal_S1_comm (a b : ℤ) :
    S1 ℤ a b = S1 ℤ b a := by
  exact S1_comm ℤ a b

/-- Petal-facing name for the natural-number inequality `S0 <= S1`. -/
theorem petal_S0_le_S1_nat (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    S0_nat a b ≤ S1_nat a b := by
  exact S0_le_S1_nat a b ha hb

end Petal
end DkMath
