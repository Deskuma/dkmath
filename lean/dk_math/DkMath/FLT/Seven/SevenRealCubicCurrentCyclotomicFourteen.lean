import DkMath.FLT.Seven.SevenRealCubicCurrentCommonPrimePacket

namespace DkMath.FLT.Seven

noncomputable section

namespace SevenRealCubic

set_option linter.style.longLine false

/-! Neutral three-zero-index extraction for the fourteen-power equation. -/

theorem three_zero_index_fourteen_zero
    {K : Type*} [_root_.Field K]
    {c0 c1 c2 r0 r1 r2 : K}
    (hc1 : c1 ≠ 0) (hr2 : r2 ≠ 0)
    (hEq : c0 * r0 ^ 14 + c1 * r1 ^ 14 + c2 * r2 ^ 14 = 0)
    (hr0 : r0 = 0) :
    (r1 / r2) ^ 14 = -c2 / c1 := by
  simp only [hr0, zero_pow (by norm_num : (14 : ℕ) ≠ 0),
    mul_zero, zero_add] at hEq
  rw [div_pow]
  field_simp [hc1, hr2]
  linear_combination hEq

theorem three_zero_index_fourteen_one
    {K : Type*} [_root_.Field K]
    {c0 c1 c2 r0 r1 r2 : K}
    (hc2 : c2 ≠ 0) (hr0 : r0 ≠ 0)
    (hEq : c0 * r0 ^ 14 + c1 * r1 ^ 14 + c2 * r2 ^ 14 = 0)
    (hr1 : r1 = 0) :
    (r2 / r0) ^ 14 = -c0 / c2 := by
  simp only [hr1, zero_pow (by norm_num : (14 : ℕ) ≠ 0),
    mul_zero, add_zero] at hEq
  rw [div_pow]
  field_simp [hc2, hr0]
  linear_combination hEq

theorem three_zero_index_fourteen_two
    {K : Type*} [_root_.Field K]
    {c0 c1 c2 r0 r1 r2 : K}
    (hc0 : c0 ≠ 0) (hr1 : r1 ≠ 0)
    (hEq : c0 * r0 ^ 14 + c1 * r1 ^ 14 + c2 * r2 ^ 14 = 0)
    (hr2 : r2 = 0) :
    (r0 / r1) ^ 14 = -c1 / c0 := by
  simp only [hr2, zero_pow (by norm_num : (14 : ℕ) ≠ 0),
    mul_zero, add_zero] at hEq
  rw [div_pow]
  field_simp [hc0, hr1]
  linear_combination hEq

end SevenRealCubic
end
end DkMath.FLT.Seven
