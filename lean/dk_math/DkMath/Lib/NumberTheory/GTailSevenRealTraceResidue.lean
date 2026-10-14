/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.GTailSevenPairedResidue

#print "file: DkMath.Lib.NumberTheory.GTailSevenRealTraceResidue"

namespace DkMath.Lib.NumberTheory

/-- The inversion-invariant real trace of a scalar seventh root. -/
def seventhRootBeta {q : ℕ} [Fact (Nat.Prime q)] (r : ZMod q) : ZMod q :=
  1 + r + r⁻¹

/-- A nontrivial seventh root supplies the real-cubic defining relation. -/
theorem seventhRootBeta_cubic {q : ℕ} [Fact (Nat.Prime q)] (r : ZMod q)
    (hr0 : r ≠ 0) (hr7 : r ^ 7 = 1) (hr1 : r ≠ 1) :
    seventhRootBeta r ^ 3 - 2 * seventhRootBeta r ^ 2 - seventhRootBeta r + 1 = 0 := by
  have hsum := seven_geom_sum_eq_zero_of_pow_eq_one r hr7 hr1
  dsimp only [seventhRootBeta]
  field_simp [hr0]
  linear_combination hsum

/-- The trace and root satisfy the quadratic relation of the degree-six carrier. -/
theorem seventhRootBeta_quadratic {q : ℕ} [Fact (Nat.Prime q)] (r : ZMod q)
    (hr0 : r ≠ 0) : r ^ 2 = -1 + (seventhRootBeta r - 1) * r := by
  have hinv : r * r⁻¹ = 1 := mul_inv_cancel₀ hr0
  dsimp only [seventhRootBeta]
  linear_combination -hinv

end DkMath.Lib.NumberTheory
