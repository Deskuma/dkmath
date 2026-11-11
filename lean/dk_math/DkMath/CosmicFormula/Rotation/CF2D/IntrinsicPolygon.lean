import DkMath.CosmicFormula.Rotation.CF2D.HalfKernel

/-! Algebraic candidates for polygon area and half-perimeter; no geometric identification is assumed. -/
namespace DkMath.CosmicFormula.Rotation.CF2D
open QuadrantUnitKernel

noncomputable def areaApprox (n : ℕ) : ℝ := (2 : ℝ) ^ (n + 1) * (sequence n).beam
noncomputable def halfPerimeterApprox (n : ℕ) : ℝ :=
  (2 : ℝ) ^ (n + 1) * Real.sqrt (2 - 2 * (sequence n).core)

theorem halfPerimeterApprox_eq_areaApprox_succ (n : ℕ) :
    halfPerimeterApprox n = areaApprox (n + 1) := by
  have h : 0 ≤ (1 - (sequence n).core) / 2 := by
    have := (sequence n).core_le_one
    linarith
  have hs := Real.sq_sqrt h
  have hr : 0 ≤ 2 - 2 * (sequence n).core := by linarith
  have ht := Real.sq_sqrt hr
  have ha := Real.sqrt_nonneg ((1 - (sequence n).core) / 2)
  have hb := Real.sqrt_nonneg (2 - 2 * (sequence n).core)
  have he : Real.sqrt (2 - 2 * (sequence n).core) =
      2 * Real.sqrt ((1 - (sequence n).core) / 2) := by nlinarith
  simp only [halfPerimeterApprox, areaApprox, QuadrantUnitKernel.sequence, half, beam, pow_succ]
  rw [he]
  ring

theorem areaApprox_zero : areaApprox 0 = 2 := by norm_num [areaApprox, QuadrantUnitKernel.sequence, initial, beam]

theorem areaApprox_one : areaApprox 1 = 2 * Real.sqrt 2 := by
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have h' := Real.sq_sqrt (show (0 : ℝ) ≤ 1 / 2 by norm_num)
  have hpos := Real.sqrt_nonneg 2
  have hpos' := Real.sqrt_nonneg (1 / 2)
  have he : 2 * Real.sqrt (1 / 2) = Real.sqrt 2 := by nlinarith
  change (2 : ℝ) ^ 2 * Real.sqrt ((1 - 0) / 2) = 2 * Real.sqrt 2
  norm_num only [sub_zero, pow_two]
  linarith

theorem halfPerimeterApprox_zero : halfPerimeterApprox 0 = 2 * Real.sqrt 2 := by
  rw [halfPerimeterApprox_eq_areaApprox_succ, areaApprox_one]

theorem areaApprox_eq_core_mul_succ (n : ℕ) :
    areaApprox n = (sequence (n + 1)).core * areaApprox (n + 1) := by
  have h := congrArg Vec.beam (sequence_star n)
  simp only [Vec.star_beam] at h
  change (sequence (n + 1)).core * (sequence (n + 1)).beam +
    (sequence (n + 1)).beam * (sequence (n + 1)).core = (sequence n).beam at h
  simp only [areaApprox, pow_succ]
  rw [← h]
  ring

theorem areaApprox_nonneg (n : ℕ) : 0 ≤ areaApprox n := by
  exact mul_nonneg (pow_nonneg (by norm_num) _) (sequence n).beam_nonneg

theorem areaApprox_monotone : Monotone areaApprox := by
  apply monotone_nat_of_le_succ
  intro n
  rw [areaApprox_eq_core_mul_succ]
  have hc := (sequence (n + 1)).core_le_one
  have ha := areaApprox_nonneg (n + 1)
  nlinarith


theorem core_succ_sq (n : ℕ) :
    (sequence (n + 1)).core ^ 2 = (1 + (sequence n).core) / 2 := by
  change Real.sqrt ((1 + (sequence n).core) / 2) ^ 2 = _
  rw [Real.sq_sqrt (by have := (sequence n).core_nonneg; change 0 ≤ (sequence n).core at this; linarith)]

theorem core_succ_pos (n : ℕ) : 0 < (sequence (n + 1)).core := by
  have h := core_succ_sq n
  have hc := (sequence n).core_nonneg
  have hn := (sequence (n + 1)).core_nonneg
  change 0 ≤ (sequence n).core at hc
  change 0 ≤ (sequence (n + 1)).core at hn
  nlinarith

noncomputable def outerApprox (n : ℕ) : ℝ := areaApprox (n + 1) / (sequence (n + 1)).core

theorem outerApprox_antitone : Antitone outerApprox := by
  apply antitone_nat_of_succ_le
  intro n
  unfold outerApprox
  apply (div_le_div_iff₀ (core_succ_pos (n+1)) (core_succ_pos n)).2
  have hrec := areaApprox_eq_core_mul_succ (n+1)
  have hsq := core_succ_sq (n+1)
  have hc := (sequence (n+1)).core_le_one
  have ha := areaApprox_nonneg (n+2)
  have hle : (sequence (n+1)).core ≤ (sequence (n+2)).core ^ 2 := by
    convert (show (sequence (n+1)).core ≤ (1 + (sequence (n+1)).core) / 2 by linarith) using 1
  have hm := mul_le_mul_of_nonneg_left hle ha
  rw [hrec]
  nlinarith [hm]

theorem outerApprox_zero : outerApprox 0 = 4 := by
  have hp := core_succ_pos 0
  have he : (QuadrantUnitKernel.sequence 1).beam = (QuadrantUnitKernel.sequence 1).core := by
    simp [QuadrantUnitKernel.sequence, half, core, beam, initial]
  unfold outerApprox areaApprox
  rw [he]
  have hn : (QuadrantUnitKernel.sequence 1).core ≠ 0 := ne_of_gt hp
  norm_num
  field_simp

theorem areaApprox_le_four (n : ℕ) : areaApprox n ≤ 4 := by
  have ho := outerApprox_antitone (Nat.zero_le n)
  rw [outerApprox_zero] at ho
  have hp := core_succ_pos n
  have hc := (sequence (n+1)).core_le_one
  have ha := areaApprox_nonneg (n+1)
  have hrec := areaApprox_eq_core_mul_succ n
  have hdiv : areaApprox (n+1) ≤ outerApprox n := by
    unfold outerApprox
    apply (le_div_iff₀ hp).2
    nlinarith
  nlinarith

end DkMath.CosmicFormula.Rotation.CF2D
