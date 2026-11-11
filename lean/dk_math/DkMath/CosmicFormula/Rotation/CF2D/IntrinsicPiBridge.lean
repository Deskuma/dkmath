import DkMath.CosmicFormula.Rotation.CF2D.IntrinsicPi

/-! Comparison with the standard trigonometric constant. -/
namespace DkMath.CosmicFormula.Rotation.CF2D
open QuadrantUnitKernel Filter
open scoped Topology

noncomputable def dyadicAngle (n : ℕ) : ℝ := Real.pi / (2 : ℝ) ^ (n + 1)

private theorem dyadicAngle_pos (n : ℕ) : 0 < dyadicAngle n := by
  exact div_pos Real.pi_pos (pow_pos (by norm_num) _)

private theorem dyadicAngle_le (n : ℕ) : dyadicAngle n ≤ Real.pi := by
  unfold dyadicAngle
  apply div_le_self Real.pi_pos.le
  exact one_le_pow₀ (by norm_num)

private theorem dyadicAngle_succ (n : ℕ) : dyadicAngle (n+1) = dyadicAngle n / 2 := by
  simp only [dyadicAngle, pow_succ, Nat.add_assoc]
  ring

theorem sequence_trig (n : ℕ) :
    (sequence n).core = Real.cos (dyadicAngle n) ∧ (sequence n).beam = Real.sin (dyadicAngle n) := by
  induction n with
  | zero => simp [QuadrantUnitKernel.sequence, initial, core, beam, dyadicAngle]
  | succ n ih =>
    have hp := dyadicAngle_pos n
    have hl := dyadicAngle_le n
    rw [dyadicAngle_succ]
    constructor
    · change Real.sqrt ((1 + (sequence n).core) / 2) = _
      rw [ih.1, Real.cos_half (by linarith) hl]
    · change Real.sqrt ((1 - (sequence n).core) / 2) = _
      rw [ih.1, Real.sin_half_eq_sqrt hp.le (by nlinarith [Real.pi_pos])]

theorem areaApprox_eq_trig (n : ℕ) :
    areaApprox n = (2 : ℝ) ^ (n+1) * Real.sin (Real.pi / (2 : ℝ) ^ (n+1)) := by
  rw [areaApprox, (sequence_trig n).2]
  rfl


private theorem tendsto_dyadicAngle : Tendsto dyadicAngle atTop (𝓝 0) := by
  have hp : Tendsto (fun n : ℕ => ((2 : ℝ)⁻¹ ^ n)) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have h := hp.const_mul (Real.pi / 2)
  convert h using 1
  · funext n
    simp only [dyadicAngle, pow_succ, div_eq_mul_inv, mul_inv_rev, inv_pow]
    ac_rfl
  · simp

theorem tendsto_areaApprox_real_pi : Tendsto areaApprox atTop (𝓝 Real.pi) := by
  have hs : Tendsto (fun n => Real.sinc (dyadicAngle n)) atTop (𝓝 1) := by
    simpa only [Real.sinc_zero, Function.comp_def] using Real.continuous_sinc.continuousAt.tendsto.comp tendsto_dyadicAngle
  have hm := hs.const_mul Real.pi
  have he : areaApprox = fun n => Real.pi * Real.sinc (dyadicAngle n) := by
    funext n
    rw [areaApprox_eq_trig, Real.sinc_of_ne_zero (ne_of_gt (dyadicAngle_pos n))]
    unfold dyadicAngle
    have hp : (2 : ℝ) ^ (n+1) ≠ 0 := pow_ne_zero _ (by norm_num)
    have hp' : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
    field_simp
  rw [he]
  simpa using hm

theorem intrinsicPi_eq_real_pi : intrinsicPi = Real.pi :=
  tendsto_nhds_unique tendsto_areaApprox_intrinsicPi tendsto_areaApprox_real_pi

end DkMath.CosmicFormula.Rotation.CF2D
