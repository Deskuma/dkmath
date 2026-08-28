/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaEndpointIncrementDecoder
import DkMath.RH.CFBRC.PrimeMirrorEnergy
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.PrimeMirrorEtaBridge"

noncomputable section

namespace DkMath.RH.CFBRCProjection

open DkMath.RH.Weave.Analytic

/-!
# Prime-mirror / eta endpoint bridge

The prime-mirror amplitudes use the same positive base as the eta term at
index `m`: namely `m + 1`.  This module records that the two descriptions read
the same centered coordinate, without introducing a second amplitude or
decoder definition.
-/

/-- The ratio of the prime-mirror amplitudes is the expected exponential. -/
theorem primeMirrorAmplitudeRatio_eq_rpow
    (m : ℕ) (δ : ℝ) :
    primeMirrorRightAmplitude (m + 1) δ /
        primeMirrorLeftAmplitude (m + 1) δ =
      (((m + 1 : ℕ) : ℝ) ^ (2 * δ)) := by
  have hbase : 0 < (((m + 1 : ℕ) : ℝ)) := by positivity
  rw [primeMirrorRightAmplitude, primeMirrorLeftAmplitude]
  rw [div_eq_mul_inv, ← Real.exp_neg]
  rw [← Real.exp_add]
  rw [Real.rpow_def_of_pos hbase]
  congr 1
  ring

/-- At the eta centered coordinate, the prime-mirror ratio is the eta ratio. -/
theorem primeMirrorAmplitudeRatio_eq_etaMirrorAmplitudeRatio
    (s : ℂ) (m : ℕ) :
    primeMirrorRightAmplitude (m + 1) (centeredSigma s.re) /
        primeMirrorLeftAmplitude (m + 1) (centeredSigma s.re) =
      etaMirrorAmplitudeRatio s m := by
  rw [primeMirrorAmplitudeRatio_eq_rpow,
    etaMirrorAmplitudeRatio_eq_rpow]

/-- The exact `(N, N + 1)` eta increment reads the prime-mirror ratio. -/
theorem etaEndpointIncrementMirrorRatio_eq_primeMirrorAmplitudeRatio
    (s : ℂ) (N : ℕ) :
    etaEndpointIncrementMirrorRatio s N =
      primeMirrorRightAmplitude (N + 1) (centeredSigma s.re) /
        primeMirrorLeftAmplitude (N + 1) (centeredSigma s.re) := by
  rw [etaEndpointIncrementMirrorRatio_eq_etaMirrorAmplitudeRatio,
    primeMirrorAmplitudeRatio_eq_etaMirrorAmplitudeRatio]

/-- The endpoint decoder and the prime-mirror offset use the same coordinate. -/
theorem etaEndpointIncrementDecoder_eq_primeMirrorCenteredOffset
    (s : ℂ) :
    etaEndpointIncrementDecoder s = centeredSigma s.re := by
  exact etaEndpointIncrementDecoder_eq_centeredSigma s

end DkMath.RH.CFBRCProjection
