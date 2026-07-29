/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.QuadraticEuclidean

#print "file: DkMath.FLT.Seven.QuadraticUnits"

namespace DkMath.FLT.Seven

open DkMath.NumberTheory.TraceOneQuadratic

local notation "tqNorm" => DkMath.NumberTheory.TraceOneQuadratic.norm

theorem isUnit_iff_norm_eq_one {x : TraceOneInt (-2)} :
    IsUnit x ↔ tqNorm x = 1 := by
  constructor
  · intro hx
    rcases isUnit_iff_exists_inv.mp hx with ⟨y, hxy⟩
    have hy : IsUnit y := by
      apply isUnit_iff_exists_inv.mpr
      exact ⟨x, by simpa [mul_comm] using hxy⟩
    have hxNorm := one_le_traceOneNorm_negTwo_of_ne_zero x hx.ne_zero
    have hyNorm := one_le_traceOneNorm_negTwo_of_ne_zero y hy.ne_zero
    have hprod : tqNorm x * tqNorm y = 1 := by
      rw [← traceOne_norm_mul, hxy]
      rfl
    nlinarith
  · intro hx
    rcases (norm_eq_one_iff_of_negTwo x).mp hx with rfl | rfl <;> simp

theorem isUnit_iff_eq_one_or_neg_one {x : TraceOneInt (-2)} :
    IsUnit x ↔ x = 1 ∨ x = -1 := by
  rw [isUnit_iff_norm_eq_one, norm_eq_one_iff_of_negTwo]

theorem exists_seventh_power_eq_of_isUnit
    {u : TraceOneInt (-2)} (hu : IsUnit u) :
    ∃ e : TraceOneInt (-2), u = e ^ 7 := by
  rcases (isUnit_iff_eq_one_or_neg_one.mp hu) with rfl | rfl
  · exact ⟨1, by norm_num⟩
  · exact ⟨-1, by norm_num⟩

end DkMath.FLT.Seven
