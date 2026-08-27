/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.AxisPowerRoll

#print "file: DkMath.FLT.Seven.AxisDepth"

namespace DkMath.FLT.Seven

open DkMath.NumberTheory.TraceOneQuadratic

local notation "tqNorm" => DkMath.NumberTheory.TraceOneQuadratic.norm

/-- Maximal finite seven-axis depth of a nonzero core, measured by the natural
`7`-adic valuation of its positive integral norm.  At zero the inherited
`padicValNat` convention gives depth zero. -/
def sevenAxisDepth (x : TraceOneInt (-2)) : ℕ :=
  padicValNat 7 (Int.natAbs (tqNorm x))

/-- Zero is absence of a core and is assigned depth zero. -/
@[simp] theorem sevenAxisDepth_zero : sevenAxisDepth 0 = 0 := by
  simp [sevenAxisDepth, DkMath.NumberTheory.TraceOneQuadratic.norm,
    padicValNat_zero_right]

/-- A nonzero discriminant `-7` core has strictly positive norm. -/
theorem norm_pos_of_ne_zero {x : TraceOneInt (-2)} (hx : x ≠ 0) :
    0 < tqNorm x := by
  have h := one_le_traceOneNorm_negTwo_of_ne_zero x hx
  omega

/-- The natural absolute value of a nonzero core norm is nonzero. -/
theorem natAbs_norm_ne_zero_of_ne_zero {x : TraceOneInt (-2)} (hx : x ≠ 0) :
    Int.natAbs (tqNorm x) ≠ 0 := by
  rw [Int.natAbs_ne_zero]
  exact ne_of_gt (norm_pos_of_ne_zero hx)

/-- Integer norm-power divisibility is exactly natural divisibility after
taking `natAbs`. -/
theorem pow_seven_dvd_norm_iff_pow_seven_dvd_natAbs_norm
    (n : ℕ) (x : TraceOneInt (-2)) :
    (7 : ℤ) ^ n ∣ tqNorm x ↔ 7 ^ n ∣ Int.natAbs (tqNorm x) := by
  have h := @Int.natAbs_dvd_natAbs ((7 : ℤ) ^ n) (tqNorm x)
  simpa [Int.natAbs_pow] using h.symm

/-- For a nonzero core, the valuation-defined depth characterizes exactly all
attained finite powers of the seven axis. -/
theorem sevenAxis_pow_dvd_iff_le_sevenAxisDepth
    {x : TraceOneInt (-2)} (hx : x ≠ 0) (n : ℕ) :
    sevenAxis ^ n ∣ x ↔ n ≤ sevenAxisDepth x := by
  rw [sevenAxis_pow_dvd_iff_pow_seven_dvd_norm,
    pow_seven_dvd_norm_iff_pow_seven_dvd_natAbs_norm]
  exact @padicValNat_dvd_iff_le 7 (Fact.mk (by norm_num))
    (Int.natAbs (tqNorm x)) n (natAbs_norm_ne_zero_of_ne_zero hx)

/-- The maximal depth is attained. -/
theorem sevenAxis_pow_depth_dvd {x : TraceOneInt (-2)} (hx : x ≠ 0) :
    sevenAxis ^ sevenAxisDepth x ∣ x :=
  (sevenAxis_pow_dvd_iff_le_sevenAxisDepth hx _).mpr le_rfl

/-- The successor of the maximal depth is not attained. -/
theorem not_sevenAxis_pow_succ_depth_dvd
    {x : TraceOneInt (-2)} (hx : x ≠ 0) :
    ¬ sevenAxis ^ (sevenAxisDepth x + 1) ∣ x := by
  rw [sevenAxis_pow_dvd_iff_le_sevenAxisDepth hx]
  omega

/-- Every attained power exponent is bounded by the maximal depth. -/
theorem le_sevenAxisDepth_of_pow_dvd
    {x : TraceOneInt (-2)} (hx : x ≠ 0) {n : ℕ}
    (hdiv : sevenAxis ^ n ∣ x) :
    n ≤ sevenAxisDepth x :=
  (sevenAxis_pow_dvd_iff_le_sevenAxisDepth hx n).mp hdiv

/-- Every exponent below the maximal depth is attained. -/
theorem sevenAxis_pow_dvd_of_le_depth
    {x : TraceOneInt (-2)} (hx : x ≠ 0) {n : ℕ}
    (hn : n ≤ sevenAxisDepth x) :
    sevenAxis ^ n ∣ x :=
  (sevenAxis_pow_dvd_iff_le_sevenAxisDepth hx n).mpr hn

/-- The attained depth cannot exceed the norm thickness available to a
nonzero core. -/
theorem pow_seven_depth_le_norm {x : TraceOneInt (-2)} (hx : x ≠ 0) :
    (7 : ℤ) ^ sevenAxisDepth x ≤ tqNorm x :=
  pow_seven_le_norm_of_sevenAxis_pow_dvd hx (sevenAxis_pow_depth_dvd hx)

/-- Peeling the attained maximal power leaves a nonzero terminal core with no
remaining seven-axis (equivalently norm-seven) factor. -/
theorem exists_terminal_sevenAxis_core
    {x : TraceOneInt (-2)} (hx : x ≠ 0) :
    ∃ y : TraceOneInt (-2),
      x = sevenAxis ^ sevenAxisDepth x * y ∧
      y ≠ 0 ∧
      ¬ sevenAxis ∣ y ∧
      ¬ (7 : ℤ) ∣ tqNorm y ∧
      tqNorm x = (7 : ℤ) ^ sevenAxisDepth x * tqNorm y ∧
      1 ≤ tqNorm y := by
  rcases sevenAxis_pow_depth_dvd hx with ⟨y, hxy⟩
  have hy0 : y ≠ 0 := ne_zero_of_eq_sevenAxis_pow_mul_of_ne_zero hxy hx
  have hyAxis : ¬ sevenAxis ∣ y := by
    rintro ⟨z, hyz⟩
    apply not_sevenAxis_pow_succ_depth_dvd hx
    refine ⟨z, ?_⟩
    calc
      x = sevenAxis ^ sevenAxisDepth x * y := hxy
      _ = sevenAxis ^ sevenAxisDepth x * (sevenAxis * z) := by rw [hyz]
      _ = sevenAxis ^ (sevenAxisDepth x + 1) * z := by
        rw [pow_succ]
        ring
  have hyNorm : ¬ (7 : ℤ) ∣ tqNorm y := by
    simpa [sevenAxis_dvd_iff_seven_dvd_norm] using hyAxis
  exact ⟨y, hxy, hy0, hyAxis, hyNorm,
    norm_eq_pow_seven_mul_norm_of_eq_sevenAxis_pow_mul hxy,
    one_le_norm_of_eq_sevenAxis_pow_mul_of_ne_zero hxy hx⟩

/-- Exact depth of a pure seven-axis power. -/
theorem sevenAxisDepth_sevenAxis_pow (n : ℕ) :
    sevenAxisDepth (sevenAxis ^ n) = n := by
  rw [sevenAxisDepth, norm_sevenAxis_pow]
  norm_num [Int.natAbs_pow]

/-- The cyclotomic coordinate depth is transparently the valuation of its
homogeneous seventh cyclotomic norm. -/
theorem sevenAxisDepth_cyclotomicSevenToTraceOne (z y : ℤ) :
    sevenAxisDepth (cyclotomicSevenToTraceOne z y) =
      padicValNat 7 (Int.natAbs (cyclotomicSeven z y)) := by
  rw [sevenAxisDepth, ← cyclotomicSeven_eq_traceOneNorm_negTwo]

end DkMath.FLT.Seven
