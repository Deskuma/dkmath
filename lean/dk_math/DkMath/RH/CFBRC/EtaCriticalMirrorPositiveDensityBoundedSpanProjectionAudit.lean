/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPositiveDensityScheduleCompatibilityAudit
import Mathlib.Tactic

/-!
# ZDI-008: positive-density bounded-span projection audit

The elementary angle condition is feasible for a fixed nonreal point and a
fixed positive safe angle: a sufficiently small positive density makes the
limiting phase span small.  This module records only that local feasibility.
It does not construct a schedule, prove residual domination, or provide a
global no-cancellation theorem.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

/-
The namespace is kept at the projection layer because the lemma is intended
to be combined with the existing positive-density phase-limit API, while its
proof itself is independent of Eta or zeta hypotheses.
-/

/--
For every fixed nonzero imaginary height and every positive safe angle, some
strictly positive density has limiting phase span below that angle.  This is
an angle-only feasibility statement; it contains no margin comparison.
-/
theorem exists_positive_density_with_bounded_phase_span
    {t δ : ℝ} (ht : t ≠ 0) (hδ : 0 < δ) :
    ∃ ρ : ℝ, 0 < ρ ∧ |t| * Real.log (1 + 2 * ρ) < δ := by
  let a : ℝ := δ / (2 * |t|)
  let ρ : ℝ := (Real.exp a - 1) / 2
  have ht_abs : 0 < |t| := abs_pos.mpr ht
  have ha : 0 < a := by
    dsimp [a]
    positivity
  have hexp : 1 < Real.exp a := Real.one_lt_exp_iff.mpr ha
  refine ⟨ρ, ?_, ?_⟩
  · dsimp [ρ]
    linarith
  · have harg : 1 + 2 * ρ = Real.exp a := by
      dsimp [ρ]
      ring
    rw [harg, Real.log_exp]
    have hhalf : |t| * a = δ / 2 := by
      dsimp [a]
      field_simp
    rw [hhalf]
    linarith

end DkMath.RH.CFBRCProjection
