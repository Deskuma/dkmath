/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.PrimeMirrorOffsetCore
import DkMath.RH.CFBRC.PascalPrimePowerModeBridge
import DkMath.RH.CFBRC.CriticalMirrorGeometry
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.CosmicFormulaZetaPrimePowerModeProjection"

/-!
# CFZP-001: prime-power mode projection

This module starts the Cosmic Formula -> Zeta Projection route at one finite
positive natural mode.  It factors the exact complex power into

* a common critical-line radial carrier,
* the already existing prime-mirror real amplitude, and
* a unit cycle state carrying the imaginary coordinate.

No argument function, infinite Euler product, zero set, limit, or RH statement
is used here.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

/-- Common radial carrier of a positive natural mode at the critical center. -/
noncomputable def cfzpPrimePowerCommonRadialCarrier (q : ℕ) : ℂ :=
  (q : ℂ) ^ (-(1 / 2 : ℂ))

/-- Branch-free cycle state of a positive natural mode at height `t`. -/
noncomputable def cfzpPrimePowerCycleState (q : ℕ) (t : ℝ) : ℂ :=
  Complex.exp
    (-Complex.I * (((t * Real.log (q : ℝ) : ℝ) : ℂ)))

/-- The cycle state has unit norm. -/
theorem norm_cfzpPrimePowerCycleState (q : ℕ) (t : ℝ) :
    ‖cfzpPrimePowerCycleState q t‖ = 1 := by
  rw [cfzpPrimePowerCycleState, Complex.norm_exp]
  simp

/--
The centered part of one positive natural mode is exactly the existing left
prime-mirror amplitude times its vertical cycle state.
-/
theorem natCpowNegCentered_eq_leftAmplitude_mul_cycle
    {q : ℕ} (hq : 0 < q) (s : ℂ) :
    (q : ℂ) ^ (-(s - (1 / 2 : ℂ))) =
      (primeMirrorLeftAmplitude q (centeredSigma s.re) : ℂ) *
        cfzpPrimePowerCycleState q s.im := by
  have hq0 : (q : ℂ) ≠ 0 := by
    exact_mod_cast hq.ne'
  rw [Complex.cpow_def_of_ne_zero hq0]
  rw [← Complex.natCast_log]
  unfold primeMirrorLeftAmplitude cfzpPrimePowerCycleState centeredSigma
  rw [Complex.ofReal_exp]
  rw [← Complex.exp_add]
  congr 1
  rw [← Complex.re_add_im s]
  rw [Complex.I]
  simp
  ring

/--
Exact factorization of `q^(-s)` into common radial carrier, horizontal mirror
amplitude, and vertical cycle state.
-/
theorem natCpowNeg_eq_commonRadial_mul_leftAmplitude_mul_cycle
    {q : ℕ} (hq : 0 < q) (s : ℂ) :
    (q : ℂ) ^ (-s) =
      cfzpPrimePowerCommonRadialCarrier q *
        (primeMirrorLeftAmplitude q (centeredSigma s.re) : ℂ) *
          cfzpPrimePowerCycleState q s.im := by
  have hq0 : (q : ℂ) ≠ 0 := by
    exact_mod_cast hq.ne'
  calc
    (q : ℂ) ^ (-s) =
        (q : ℂ) ^
          ((-(1 / 2 : ℂ)) + (-(s - (1 / 2 : ℂ)))) := by
      congr 1
      ring
    _ = cfzpPrimePowerCommonRadialCarrier q *
          ((q : ℂ) ^ (-(s - (1 / 2 : ℂ)))) := by
      rw [Complex.cpow_add _ _ hq0]
      rfl
    _ = cfzpPrimePowerCommonRadialCarrier q *
          (primeMirrorLeftAmplitude q (centeredSigma s.re) : ℂ) *
            cfzpPrimePowerCycleState q s.im := by
      rw [natCpowNegCentered_eq_leftAmplitude_mul_cycle hq s]
      ring

/-- Critical reflection changes only the horizontal mirror amplitude. -/
theorem primeMirrorLeftAmplitude_criticalMirror_eq_right
    (q : ℕ) (s : ℂ) :
    primeMirrorLeftAmplitude q (centeredSigma (criticalMirror s).re) =
      primeMirrorRightAmplitude q (centeredSigma s.re) := by
  unfold primeMirrorLeftAmplitude primeMirrorRightAmplitude centeredSigma
  rw [criticalMirror_re]
  congr 1
  ring

/--
The same-height critical mirror has the right mirror amplitude and the same
cycle state.
-/
theorem natCpowNeg_criticalMirror_eq_commonRadial_mul_rightAmplitude_mul_cycle
    {q : ℕ} (hq : 0 < q) (s : ℂ) :
    (q : ℂ) ^ (-(criticalMirror s)) =
      cfzpPrimePowerCommonRadialCarrier q *
        (primeMirrorRightAmplitude q (centeredSigma s.re) : ℂ) *
          cfzpPrimePowerCycleState q s.im := by
  rw [natCpowNeg_eq_commonRadial_mul_leftAmplitude_mul_cycle hq (criticalMirror s)]
  rw [primeMirrorLeftAmplitude_criticalMirror_eq_right]
  simp

/-- Functional-equation reflection also flips the cycle-height sign. -/
theorem primeMirrorLeftAmplitude_one_sub_eq_right
    (q : ℕ) (s : ℂ) :
    primeMirrorLeftAmplitude q (centeredSigma (1 - s).re) =
      primeMirrorRightAmplitude q (centeredSigma s.re) := by
  unfold primeMirrorLeftAmplitude primeMirrorRightAmplitude centeredSigma
  simp
  congr 1
  ring

/--
At `1 - s`, the radial carrier is unchanged, the horizontal amplitude is the
right mirror amplitude, and the cycle state runs at height `-s.im`.
-/
theorem natCpowNeg_one_sub_eq_commonRadial_mul_rightAmplitude_mul_cycle
    {q : ℕ} (hq : 0 < q) (s : ℂ) :
    (q : ℂ) ^ (-(1 - s)) =
      cfzpPrimePowerCommonRadialCarrier q *
        (primeMirrorRightAmplitude q (centeredSigma s.re) : ℂ) *
          cfzpPrimePowerCycleState q (-s.im) := by
  rw [natCpowNeg_eq_commonRadial_mul_leftAmplitude_mul_cycle hq (1 - s)]
  rw [primeMirrorLeftAmplitude_one_sub_eq_right]
  simp

/--
The existing Euler prime-power mode is exactly the natural-label mode at
`q = p^k`.
-/
theorem eulerPrimePowerMode_eq_naturalLabelCpowNeg
    {p : ℕ} (hp : Nat.Prime p) (k : ℕ) (s : ℂ) :
    eulerPrimePowerMode p k s =
      (((p ^ k : ℕ) : ℂ) ^ (-s)) := by
  rw [eulerPrimePowerMode, eulerPrimePrimitiveMode_eq_cpow_neg hp]
  calc
    ((p : ℂ) ^ (-s)) ^ k =
        (p : ℂ) ^ ((k : ℂ) * (-s)) := by
      symm
      simpa using (Complex.cpow_nat_mul (p : ℂ) k (-s))
    _ = (((p ^ k : ℕ) : ℂ) ^ (-s)) := by
      simpa using (Complex.natCast_cpow_natCast_mul p k (-s))

/-- Actual Euler prime-power mode factorization on the original side. -/
theorem eulerPrimePowerMode_eq_commonRadial_mul_leftAmplitude_mul_cycle
    {p : ℕ} (hp : Nat.Prime p) (k : ℕ) (s : ℂ) :
    eulerPrimePowerMode p k s =
      cfzpPrimePowerCommonRadialCarrier (p ^ k) *
        (primeMirrorLeftAmplitude (p ^ k) (centeredSigma s.re) : ℂ) *
          cfzpPrimePowerCycleState (p ^ k) s.im := by
  rw [eulerPrimePowerMode_eq_naturalLabelCpowNeg hp]
  exact natCpowNeg_eq_commonRadial_mul_leftAmplitude_mul_cycle
    (pow_pos hp.pos k) s

/-- Actual Euler prime-power mode factorization on the same-height mirror. -/
theorem eulerPrimePowerMode_criticalMirror_eq_commonRadial_mul_rightAmplitude_mul_cycle
    {p : ℕ} (hp : Nat.Prime p) (k : ℕ) (s : ℂ) :
    eulerPrimePowerMode p k (criticalMirror s) =
      cfzpPrimePowerCommonRadialCarrier (p ^ k) *
        (primeMirrorRightAmplitude (p ^ k) (centeredSigma s.re) : ℂ) *
          cfzpPrimePowerCycleState (p ^ k) s.im := by
  rw [eulerPrimePowerMode_eq_naturalLabelCpowNeg hp]
  exact natCpowNeg_criticalMirror_eq_commonRadial_mul_rightAmplitude_mul_cycle
    (pow_pos hp.pos k) s

/-- Actual Euler prime-power mode factorization at the functional reflection. -/
theorem eulerPrimePowerMode_one_sub_eq_commonRadial_mul_rightAmplitude_mul_cycle
    {p : ℕ} (hp : Nat.Prime p) (k : ℕ) (s : ℂ) :
    eulerPrimePowerMode p k (1 - s) =
      cfzpPrimePowerCommonRadialCarrier (p ^ k) *
        (primeMirrorRightAmplitude (p ^ k) (centeredSigma s.re) : ℂ) *
          cfzpPrimePowerCycleState (p ^ k) (-s.im) := by
  rw [eulerPrimePowerMode_eq_naturalLabelCpowNeg hp]
  exact natCpowNeg_one_sub_eq_commonRadial_mul_rightAmplitude_mul_cycle
    (pow_pos hp.pos k) s

/-- Original and functional-reflection factorizations packaged on one mode. -/
theorem eulerPrimePowerMode_cfzp_pair_factorization
    {p : ℕ} (hp : Nat.Prime p) (k : ℕ) (s : ℂ) :
    (eulerPrimePowerMode p k s =
        cfzpPrimePowerCommonRadialCarrier (p ^ k) *
          (primeMirrorLeftAmplitude (p ^ k) (centeredSigma s.re) : ℂ) *
            cfzpPrimePowerCycleState (p ^ k) s.im) ∧
      (eulerPrimePowerMode p k (1 - s) =
        cfzpPrimePowerCommonRadialCarrier (p ^ k) *
          (primeMirrorRightAmplitude (p ^ k) (centeredSigma s.re) : ℂ) *
            cfzpPrimePowerCycleState (p ^ k) (-s.im)) := by
  exact ⟨
    eulerPrimePowerMode_eq_commonRadial_mul_leftAmplitude_mul_cycle hp k s,
    eulerPrimePowerMode_one_sub_eq_commonRadial_mul_rightAmplitude_mul_cycle hp k s⟩

end DkMath.RH.CFBRCProjection
