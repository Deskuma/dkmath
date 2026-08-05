/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameTwoScaleNonresonanceAudit

#print "file: DkMathTest.RH.CFBRCEtaCriticalMirrorPairedFrameTwoScaleNonresonanceAudit"

noncomputable section

namespace DkMathTest.RH.CFBRCEtaCriticalMirrorPairedFrameTwoScaleNonresonanceAudit

open Filter
open scoped Topology
open DkMath.RH.CFBRCProjection
open DkMath.RH.CFBRCProjection.EtaPairPositiveDensityBlockSchedule

example (s : ℂ) :
    Tendsto
      (etaPairFullDensityBlockSchedule.scheduledBlockPhase s)
      atTop
      (nhds (s.im * Real.log 3)) :=
  etaPairFullDensityBlockSchedule_scheduledBlockPhase_tendsto s

example (s : ℂ) :
    Tendsto
      (etaPairFullDensityBlockSchedule.scheduledBlockRotation s)
      atTop
      (nhds
        (Complex.exp
          (Complex.I * (((s.im * Real.log 3 : ℝ) : ℂ))))) :=
  etaPairFullDensityBlockSchedule_scheduledBlockRotation_tendsto s

example {s : ℂ} (him : s.im ≠ 0) :
    Complex.exp
          (Complex.I * (((s.im * Real.log 2 : ℝ) : ℂ))) ≠ 1 ∨
      Complex.exp
          (Complex.I * (((s.im * Real.log 3 : ℝ) : ℂ))) ≠ 1 :=
  etaPairTwoScaleRotation_nonresonant him

example {s : ℂ} (him : s.im ≠ 0) :
    etaPairHalfDensityBlockSchedule.scheduledBlockRotationLimit s ≠ 1 ∨
      etaPairFullDensityBlockSchedule.scheduledBlockRotationLimit s ≠ 1 :=
  etaPairHalf_or_fullDensityBlockSchedule_rotationLimit_ne_one him

example {s : ℂ} (him : s.im ≠ 0) :
    EtaPairTwoScaleNonresonanceCertificate s :=
  etaPairTwoScaleNonresonanceCertificate_of_im_ne_zero him

end DkMathTest.RH.CFBRCEtaCriticalMirrorPairedFrameTwoScaleNonresonanceAudit
