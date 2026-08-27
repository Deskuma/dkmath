/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenRealCubicNormFirstVariation

#print "file: DkMath.FLT.Seven.SevenRealCubicSourcePlane"

namespace DkMath.FLT.Seven

namespace SevenRealCubicInt

/-- The two-coordinate plane used by the original ramified source chart. -/
def IsSourcePlane (x : SevenRealCubicInt) : Prop :=
  x.thd = 0

/-- The primitive degree-seven equation controlling whether a seventh power
returns to the source plane. -/
def seventhSourcePlaneEquation (a b c : ℤ) : ℤ :=
  a ^ 6 * c + 3 * a ^ 5 * b ^ 2 + 12 * a ^ 5 * b * c +
  15 * a ^ 5 * c ^ 2 + 10 * a ^ 4 * b ^ 3 +
  75 * a ^ 4 * b ^ 2 * c + 165 * a ^ 4 * b * c ^ 2 +
  125 * a ^ 4 * c ^ 3 + 25 * a ^ 3 * b ^ 4 +
  220 * a ^ 3 * b ^ 3 * c + 750 * a ^ 3 * b ^ 2 * c ^ 2 +
  1120 * a ^ 3 * b * c ^ 3 + 630 * a ^ 3 * c ^ 4 +
  33 * a ^ 2 * b ^ 5 + 375 * a ^ 2 * b ^ 4 * c +
  1680 * a ^ 2 * b ^ 3 * c ^ 2 + 3780 * a ^ 2 * b ^ 2 * c ^ 3 +
  4245 * a ^ 2 * b * c ^ 4 + 1908 * a ^ 2 * c ^ 5 +
  25 * a * b ^ 6 + 336 * a * b ^ 5 * c +
  1890 * a * b ^ 4 * c ^ 2 + 5660 * a * b ^ 3 * c ^ 3 +
  9540 * a * b ^ 2 * c ^ 4 + 8574 * a * b * c ^ 5 +
  3211 * a * c ^ 6 + 8 * b ^ 7 + 126 * b ^ 6 * c +
  849 * b ^ 5 * c ^ 2 + 3180 * b ^ 4 * c ^ 3 +
  7145 * b ^ 3 * c ^ 4 + 9633 * b ^ 2 * c ^ 5 +
  7215 * b * c ^ 6 + 2316 * c ^ 7

set_option maxHeartbeats 1000000 in
-- Expanding the seventh power in the cubic multiplication table is large.
set_option maxRecDepth 100000 in
theorem thd_pow_seven (x : SevenRealCubicInt) :
    (x ^ 7).thd =
      7 * seventhSourcePlaneEquation x.fst x.snd x.thd := by
  rcases x with ⟨a, b, c⟩
  norm_num [seventhSourcePlaneEquation, pow_succ]
  ring

/-- FUSION-002 reconnaissance: source-plane return is exactly one explicit
homogeneous degree-seven Diophantine equation. -/
theorem pow_seven_isSourcePlane_iff (x : SevenRealCubicInt) :
    IsSourcePlane (x ^ 7) ↔
      seventhSourcePlaneEquation x.fst x.snd x.thd = 0 := by
  rw [IsSourcePlane, thd_pow_seven]
  constructor
  · intro h
    exact mul_left_cancel₀ (by norm_num : (7 : ℤ) ≠ 0) h
  · intro h
    rw [h, mul_zero]


end SevenRealCubicInt

end DkMath.FLT.Seven
