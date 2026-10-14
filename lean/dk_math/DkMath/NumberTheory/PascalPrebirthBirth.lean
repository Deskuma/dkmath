/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.PascalPrebirthBoundary
import DkMath.NumberTheory.PascalPrimeCoordinateDecoder

#print "file: DkMath.NumberTheory.PascalPrebirthBirth"

/-! Prime-coordinate birth is distinct from positive prime-power synchronization.
Real logarithms stay local to this decoder bridge. -/

namespace DkMath.NumberTheory

/-- In-range zero cancellation defect is positive prime-dial height. -/
theorem pascalCancellationDefect_zero_iff_dial_pos {d p k : ℕ}
    (hp : p.Prime) (hk : k < d) :
    pascalCancellationDefect d p k = 0 ↔ 0 < pascalPrimeDialHeight p (d + 1) (k + 1) := by
  rw [pascalCancellationDefect_eq_zero_iff]
  exact (DkMath.ABC.Vp_ge_one_iff hp (Nat.choose_ne_zero (by omega))).symm

/-- Before the first prime boundary every in-range adjacent defect is nonzero. -/
theorem pascalCancellationDefect_ne_zero_of_next_row_lt {d p k : ℕ}
    (hp : p.Prime) (hd : d + 1 < p) (hk : k < d) :
    pascalCancellationDefect d p k ≠ 0 := by
  intro hz
  exact prime_not_dvd_pascalCoeffMass_of_row_lt hp hd (by omega)
    ((pascalCancellationDefect_eq_zero_iff d p k).mp hz)

/-- A prime is absent earlier, born at its own row, with its prime-only log mass. -/
theorem prime_prebirth_birth_packet {p : ℕ} (hp : p.Prime) :
    (∀ d, d < p → p ∉ pascalRowPrimeCoordinateSupport d) ∧
    PascalPrebirthAlternationMod (p - 1) p ∧
    p ∈ pascalPrimeCoordinateBirthSupport p ∧
    pascalPrimeBirthLogMass p = Real.log (p : ℝ) := by
  refine ⟨fun d hd => prime_not_mem_pascalRowPrimeCoordinateSupport_of_row_lt hp hd,
    prime_prebirthAlternation hp, ?_, ?_⟩
  · exact mem_pascalPrimeCoordinateBirthSupport_iff.mpr ⟨hp, rfl⟩
  · simp [pascalPrimeBirthLogMass_eq, hp]

/-- Within positive prime powers, genuine base-coordinate birth is exponent one. -/
theorem prime_power_coordinate_birth_iff {p a : ℕ} (hp : p.Prime) (ha : 0 < a) :
    p ∈ pascalPrimeCoordinateBirthSupport (p ^ a) ↔ a = 1 := by
  rw [mem_pascalPrimeCoordinateBirthSupport_iff]
  constructor
  · rintro ⟨_, h⟩
    have heq : p ^ a = p ^ 1 := by simpa using h.symm
    exact (Nat.pow_right_injective hp.one_lt) heq
  · rintro rfl
    simp [hp]

/-- Higher powers synchronize a base direction already present in cumulative support. -/
theorem prime_power_resynchronization_packet {p a : ℕ} (hp : p.Prime) (ha : 1 < a) :
    PascalPrebirthAlternationMod (p ^ a - 1) p ∧
    AllInnerChooseDivisible (p ^ a) p ∧
    p ∈ pascalPrimeCoordinateSupportUpTo (p ^ a - 1) ∧
    p ∉ pascalPrimeCoordinateBirthSupport (p ^ a) := by
  have hlt : p < p ^ a := by
    have := Nat.pow_lt_pow_right hp.one_lt ha
    simpa using this
  refine ⟨prime_power_prebirthAlternation hp (by omega), prime_power_allInnerChooseDivisible hp,
    mem_pascalPrimeCoordinateSupportUpTo_iff.mpr ⟨hp, by omega⟩, ?_⟩
  rw [prime_power_coordinate_birth_iff hp (by omega)]
  omega

/-- Prime-only row birth mass is nonnegative. -/
theorem pascalPrimeBirthLogMass_nonneg (N : ℕ) : 0 ≤ pascalPrimeBirthLogMass N := by
  rw [pascalPrimeBirthLogMass_eq]
  split_ifs with h
  · exact Real.log_nonneg (by exact_mod_cast h.one_le)
  · rfl

/-- Positive row birth mass occurs exactly at prime rows. -/
theorem pascalPrimeBirthLogMass_pos_iff (N : ℕ) :
    0 < pascalPrimeBirthLogMass N ↔ N.Prime := by
  rw [pascalPrimeBirthLogMass_eq]
  by_cases h : N.Prime
  · simp only [h, ite_true, iff_true]
    exact Real.log_pos (by exact_mod_cast h.one_lt)
  · simp [h]

/-- A logarithmic relative modulus gauge, separate from exponent-period PowerGauge. -/
noncomputable def pascalPrimePowerLogGauge (p a : ℕ) : ℝ :=
  Real.log (p : ℝ) / Real.log ((p ^ a : ℕ) : ℝ)

/-- Positive prime powers have relative log modulus exactly inverse exponent. -/
theorem pascalPrimePowerLogGauge_eq {p a : ℕ} (hp : p.Prime) (ha : 0 < a) :
    pascalPrimePowerLogGauge p a = 1 / (a : ℝ) := by
  have hl : Real.log (p : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by exact_mod_cast hp.one_lt))
  have haR : (a : ℝ) ≠ 0 := by exact_mod_cast ha.ne'
  simp only [pascalPrimePowerLogGauge, Nat.cast_pow, Real.log_pow]
  field_simp

end DkMath.NumberTheory
