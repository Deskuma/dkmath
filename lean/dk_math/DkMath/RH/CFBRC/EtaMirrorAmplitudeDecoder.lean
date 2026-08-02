/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.CriticalMirrorGeometry
import DkMath.RH.Weave.Analytic.EtaTermDecay
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.EtaMirrorAmplitudeDecoder"

noncomputable section

namespace DkMath.RH.CFBRCProjection

open DkMath.RH.Weave.Analytic

/--
Ratio between the magnitude of one eta term at the critical mirror point and
its magnitude at the original point.
-/
noncomputable def etaMirrorAmplitudeRatio (s : ℂ) (m : ℕ) : ℝ :=
  ‖etaSignedVector (criticalMirror s) m‖ / ‖etaSignedVector s m‖

/--
The mirror/original eta-amplitude ratio records exactly twice the centered
real coordinate in the positive base `m + 1`.
-/
theorem etaMirrorAmplitudeRatio_eq_rpow
    (s : ℂ) (m : ℕ) :
    etaMirrorAmplitudeRatio s m =
      (((m + 1 : ℕ) : ℝ) ^ (2 * centeredSigma s.re)) := by
  rw [etaMirrorAmplitudeRatio,
    norm_etaSignedVector_eq_rpow,
    norm_etaSignedVector_eq_rpow,
    criticalMirror_re]
  have hbase : 0 < (((m + 1 : ℕ) : ℝ)) := by positivity
  rw [← Real.rpow_sub hbase]
  congr 1
  unfold centeredSigma
  ring

/-- The first nonconstant eta term uses base two. -/
@[simp] theorem etaMirrorAmplitudeRatio_one_eq_two_rpow
    (s : ℂ) :
    etaMirrorAmplitudeRatio s 1 =
      (2 : ℝ) ^ (2 * centeredSigma s.re) := by
  simpa using etaMirrorAmplitudeRatio_eq_rpow s 1

/--
Decode the centered real coordinate from the base-two mirror-amplitude ratio.
This expression depends only on genuine eta magnitudes at `s` and its critical
mirror; it does not read any stored centered-coordinate field.
-/
noncomputable def etaMirrorAmplitudeDecoder (s : ℂ) : ℝ :=
  Real.log (etaMirrorAmplitudeRatio s 1) / (2 * Real.log 2)

/-- The base-two mirror-amplitude decoder recovers the centered coordinate exactly. -/
theorem etaMirrorAmplitudeDecoder_eq_centeredSigma
    (s : ℂ) :
    etaMirrorAmplitudeDecoder s = centeredSigma s.re := by
  rw [etaMirrorAmplitudeDecoder,
    etaMirrorAmplitudeRatio_one_eq_two_rpow]
  have h2pos : 0 < (2 : ℝ) := by norm_num
  have hlog2pos : 0 < Real.log (2 : ℝ) :=
    Real.log_pos (by norm_num)
  have hlog2_ne : Real.log (2 : ℝ) ≠ 0 := ne_of_gt hlog2pos
  rw [Real.log_rpow h2pos]
  field_simp [hlog2_ne]
  ring

end DkMath.RH.CFBRCProjection
