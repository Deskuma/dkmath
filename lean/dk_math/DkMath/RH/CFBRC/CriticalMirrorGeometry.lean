/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.CompletedZetaBridge
import DkMath.RH.CFBRC.MirrorThreatModel
import DkMath.RH.CFBRC.MirrorRootOfUnity
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.CriticalMirrorGeometry"

namespace DkMath.RH.CFBRCProjection

/-- Reflection across the critical line while preserving the imaginary coordinate. -/
noncomputable def criticalMirror (s : ℂ) : ℂ :=
  ⟨1 - s.re, s.im⟩

@[simp] theorem criticalMirror_re (s : ℂ) :
    (criticalMirror s).re = 1 - s.re := by
  rfl

@[simp] theorem criticalMirror_im (s : ℂ) :
    (criticalMirror s).im = s.im := by
  rfl

/-- Critical reflection is an involution. -/
theorem criticalMirror_involutive (s : ℂ) :
    criticalMirror (criticalMirror s) = s := by
  apply Complex.ext
  · simp [criticalMirror]
  · simp [criticalMirror]

/-- The fixed locus of critical reflection is exactly `re s = 1/2`. -/
theorem criticalMirror_eq_self_iff_re_eq_half (s : ℂ) :
    criticalMirror s = s ↔ s.re = (1 : ℝ) / 2 := by
  constructor
  · intro h
    have hre := congrArg Complex.re h
    simp [criticalMirror] at hre
    linarith
  · intro hre
    apply Complex.ext
    · simp [criticalMirror]
      linarith
    · simp [criticalMirror]

/-- Complex coordinate centered at the critical line. -/
noncomputable def centeredComplex (s : ℂ) : ℂ :=
  ⟨s.re - (1 : ℝ) / 2, s.im⟩

@[simp] theorem centeredComplex_re (s : ℂ) :
    (centeredComplex s).re = s.re - (1 : ℝ) / 2 := by
  rfl

@[simp] theorem centeredComplex_im (s : ℂ) :
    (centeredComplex s).im = s.im := by
  rfl

/-- The centered original point is exactly the mirror model's left state. -/
theorem centeredComplex_eq_mirrorLeft (s : ℂ) :
    centeredComplex s = mirrorLeft (centeredSigma s.re) s.im := by
  apply Complex.ext <;> simp [centeredSigma, mirrorLeft]

end DkMath.RH.CFBRCProjection
