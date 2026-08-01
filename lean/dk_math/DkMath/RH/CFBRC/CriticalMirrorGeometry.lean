/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.CompletedZetaBridge
import DkMath.RH.CFBRC.MirrorThreatModel
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.CriticalMirrorGeometry"

namespace DkMath.RH.CFBRCProjection

/-- Reflection across the critical line while preserving the imaginary coordinate. -/
noncomputable def criticalMirror (s : ℂ) : ℂ :=
  1 - Complex.conj s

@[simp] theorem criticalMirror_re (s : ℂ) :
    (criticalMirror s).re = 1 - s.re := by
  simp [criticalMirror]

@[simp] theorem criticalMirror_im (s : ℂ) :
    (criticalMirror s).im = s.im := by
  simp [criticalMirror]

/-- Critical reflection is an involution. -/
theorem criticalMirror_involutive (s : ℂ) :
    criticalMirror (criticalMirror s) = s := by
  apply Complex.ext <;> simp [criticalMirror]

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
  s - (1 : ℂ) / 2

/-- The centered original point is the mirror model's left state. -/
theorem centeredComplex_eq_mirrorLeft (s : ℂ) :
    centeredComplex s = mirrorLeft (centeredSigma s.re) s.im := by
  apply Complex.ext <;>
    simp [centeredComplex, mirrorLeft, centeredSigma] <;> ring

/-- The centered reflected point is the mirror model's right state. -/
theorem centeredCriticalMirror_eq_mirrorRight (s : ℂ) :
    centeredComplex (criticalMirror s) =
      mirrorRight (centeredSigma s.re) s.im := by
  apply Complex.ext <;>
    simp [centeredComplex, criticalMirror, mirrorRight, centeredSigma] <;> ring

/--
The mirror CFBRC polynomial is exactly the difference of powers of the centered
point and its critical reflection.
-/
theorem mirrorCFBRC_eq_centered_criticalMirror_diff_pow
    (d : ℕ) (s : ℂ) :
    mirrorCFBRC d (centeredSigma s.re) s.im =
      centeredComplex s ^ d - centeredComplex (criticalMirror s) ^ d := by
  rw [mirrorCFBRC, ← centeredComplex_eq_mirrorLeft,
    ← centeredCriticalMirror_eq_mirrorRight]

/-- On the critical line, the centered point is fixed by critical reflection. -/
theorem centeredCriticalMirror_eq_self_of_re_eq_half
    {s : ℂ} (hs : s.re = (1 : ℝ) / 2) :
    centeredComplex (criticalMirror s) = centeredComplex s := by
  rw [(criticalMirror_eq_self_iff_re_eq_half s).2 hs]

/-- Consequently every mirror CFBRC degree closes on the critical line. -/
theorem mirrorCFBRC_centeredSigma_eq_zero_of_re_eq_half
    (d : ℕ) {s : ℂ} (hs : s.re = (1 : ℝ) / 2) :
    mirrorCFBRC d (centeredSigma s.re) s.im = 0 := by
  rw [mirrorCFBRC_eq_centered_criticalMirror_diff_pow,
    centeredCriticalMirror_eq_self_of_re_eq_half hs, sub_self]

end DkMath.RH.CFBRCProjection
