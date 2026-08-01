/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.CFBRC.TrigBridge.Complex
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.OffCriticalExclusion"

namespace DkMath.RH.CFBRCProjection

open DkMath.CFBRC.TrigBridge

/--
The real coordinate centered at the critical line.

`centeredSigma σ = 0` is exactly `σ = 1 / 2`.
-/
noncomputable def centeredSigma (σ : ℝ) : ℝ :=
  σ - (1 : ℝ) / 2

/--
Evaluate the standard real-input CFBRC polynomial at the coordinate centered on
`σ = 1 / 2`.

This definition contains no zeta-zero predicate; it is an ordinary CFBRC
evaluation prepared for a later zero-preserving bridge.
-/
noncomputable def offCriticalCFBRC (d : ℕ) (σ Θ : ℝ) : ℂ :=
  cfbrcR d (centeredSigma σ) Θ

@[simp] theorem centeredSigma_eq_zero_iff (σ : ℝ) :
    centeredSigma σ = 0 ↔ σ = (1 : ℝ) / 2 := by
  unfold centeredSigma
  constructor <;> intro h <;> linarith

/--
The first completed off-critical exclusion kernel.

For degree two,

`cfbrcR 2 X Θ = X^2 + 2 i X Θ`.

Hence the complex value can vanish only when the centered real coordinate `X`
vanishes.  The proof uses the already formalized real-component theorem and is
independent of every zeta-zero statement.
-/
theorem cfbrcR_two_eq_zero_iff_x_eq_zero (X Θ : ℝ) :
    cfbrcR 2 X Θ = 0 ↔ X = 0 := by
  constructor
  · intro h
    have hre : Complex.re (cfbrcR 2 X Θ) = 0 := by
      rw [h]
      simp
    rw [cfbrc_two_re] at hre
    nlinarith
  · intro h
    subst X
    simp [cfbrcR, cfbrc]

/--
Degree-two standard CFBRC closure occurs exactly on the critical line.
-/
theorem offCriticalCFBRC_two_eq_zero_iff_re_eq_half (σ Θ : ℝ) :
    offCriticalCFBRC 2 σ Θ = 0 ↔ σ = (1 : ℝ) / 2 := by
  rw [offCriticalCFBRC, cfbrcR_two_eq_zero_iff_x_eq_zero,
    centeredSigma_eq_zero_iff]

/--
Abstract interface for the final analytic step.

A realization supplies a phase coordinate and proves only that every selected
complex zero maps to a degree-two standard CFBRC zero.  The interface does not
assume that the zero lies on the critical line and does not prescribe what the
predicate `Zero` means.
-/
structure ZeroToCFBRCTwoBridge (Zero : ℂ → Prop) where
  phase : ℂ → ℝ
  map_zero : ∀ {s : ℂ}, Zero s → offCriticalCFBRC 2 s.re (phase s) = 0

/--
Any zero predicate admitting a zero-preserving degree-two CFBRC bridge is
confined to real part `1 / 2`.

All analytic difficulty is intentionally isolated in `bridge.map_zero`.
-/
theorem re_eq_half_of_zeroToCFBRCTwoBridge
    {Zero : ℂ → Prop}
    (bridge : ZeroToCFBRCTwoBridge Zero)
    {s : ℂ}
    (hs : Zero s) :
    s.re = (1 : ℝ) / 2 := by
  exact
    (offCriticalCFBRC_two_eq_zero_iff_re_eq_half s.re (bridge.phase s)).mp
      (bridge.map_zero hs)

end DkMath.RH.CFBRCProjection
