/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.Weave.Analytic.EtaPairIntegral
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

#print "file: DkMath.RH.Weave.Analytic.EtaPairPhaseSpan"

noncomputable section

namespace DkMath.RH.Weave.Analytic

open Filter
open scoped Topology

/--
Maximum phase rotation of the eta-pair derivative kernel over the natural
interval `[2k+1, 2k+2]`.

For `s = σ + it`, the positive-real factor `x⁻ˢ⁻¹` rotates by
`-t * log x`; hence its phase width across the interval is
`|t| * log ((2k+2)/(2k+1))`.
-/
noncomputable def etaPairDerivativePhaseSpan
    (s : ℂ) (k : ℕ) : ℝ :=
  |s.im| *
    Real.log
      ((((2 * k + 2 : ℕ) : ℝ)) /
        (((2 * k + 1 : ℕ) : ℝ)))

/-- The phase-span quantity is always nonnegative. -/
theorem etaPairDerivativePhaseSpan_nonneg
    (s : ℂ) (k : ℕ) :
    0 ≤ etaPairDerivativePhaseSpan s k := by
  have ha : 0 < (((2 * k + 1 : ℕ) : ℝ)) := by positivity
  have hab :
      (((2 * k + 1 : ℕ) : ℝ)) ≤
        (((2 * k + 2 : ℕ) : ℝ)) := by
    exact_mod_cast (by omega : 2 * k + 1 ≤ 2 * k + 2)
  have hratio :
      1 ≤
        (((2 * k + 2 : ℕ) : ℝ)) /
          (((2 * k + 1 : ℕ) : ℝ)) :=
    (le_div_iff₀ ha).2 (by simpa using hab)
  exact mul_nonneg (abs_nonneg s.im) (Real.log_nonneg hratio)

/--
The phase span is bounded by the reciprocal left endpoint.  This is the exact
place where the logarithmic pair width is converted into a simple tail bound.
-/
theorem etaPairDerivativePhaseSpan_le_inv
    (s : ℂ) (k : ℕ) :
    etaPairDerivativePhaseSpan s k ≤
      |s.im| / (((2 * k + 1 : ℕ) : ℝ)) := by
  let a : ℝ := ((2 * k + 1 : ℕ) : ℝ)
  let b : ℝ := ((2 * k + 2 : ℕ) : ℝ)
  have ha : 0 < a := by
    dsimp [a]
    positivity
  have hb : 0 < b := by
    dsimp [b]
    positivity
  have hstep : b = a + 1 := by
    dsimp [a, b]
    norm_num
    ring
  have hlog : Real.log (b / a) ≤ b / a - 1 :=
    Real.log_le_sub_one_of_pos (div_pos hb ha)
  have hratio : b / a - 1 = 1 / a := by
    rw [hstep]
    field_simp [ha.ne']
    ring
  rw [hratio] at hlog
  have hlog' : Real.log (b / a) ≤ a⁻¹ := by
    simpa [one_div] using hlog
  unfold etaPairDerivativePhaseSpan
  change
    |s.im| * Real.log (b / a) ≤ |s.im| / a
  rw [div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_left hlog' (abs_nonneg s.im)

/-- The affine odd-index subsequence `k ↦ 2k+1` is cofinal. -/
theorem tendsto_two_mul_add_one_atTop :
    Tendsto (fun k : ℕ => 2 * k + 1) atTop atTop := by
  refine tendsto_atTop.2 ?_
  intro n
  exact eventually_atTop.2 ⟨n, by
    intro k hk
    omega⟩

/-- The eta-pair derivative phase width shrinks to zero. -/
theorem etaPairDerivativePhaseSpan_tendsto_zero
    (s : ℂ) :
    Tendsto (fun k : ℕ => etaPairDerivativePhaseSpan s k)
      atTop (nhds 0) := by
  have hupper :
      Tendsto
        (fun k : ℕ =>
          |s.im| / (((2 * k + 1 : ℕ) : ℝ)))
        atTop (nhds 0) := by
    have hcomp :=
      (tendsto_const_div_atTop_nhds_zero_nat (|s.im| : ℝ)).comp
        tendsto_two_mul_add_one_atTop
    have hfun :
        (fun k : ℕ =>
          |s.im| / (((2 * k + 1 : ℕ) : ℝ))) =
          ((fun n : ℕ => |s.im| / (n : ℝ)) ∘
            fun k : ℕ => 2 * k + 1) := by
      funext k
      simp [Function.comp_apply, Nat.cast_add, Nat.cast_mul]
    rw [hfun]
    exact hcomp
  exact
    tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hupper
      (Eventually.of_forall fun k =>
        etaPairDerivativePhaseSpan_nonneg s k)
      (Eventually.of_forall fun k =>
        etaPairDerivativePhaseSpan_le_inv s k)

/-- Eventually each natural eta-pair derivative arc has width below a half-plane. -/
theorem eventually_etaPairDerivativePhaseSpan_lt_pi_div_two
    (s : ℂ) :
    ∀ᶠ k : ℕ in atTop,
      etaPairDerivativePhaseSpan s k < Real.pi / 2 :=
  (etaPairDerivativePhaseSpan_tendsto_zero s).eventually_lt_const
    (by positivity)

end DkMath.RH.Weave.Analytic
