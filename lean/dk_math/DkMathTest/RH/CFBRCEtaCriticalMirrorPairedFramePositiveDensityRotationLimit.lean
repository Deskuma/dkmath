import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFramePositiveDensityRotationLimit

#print "file: DkMathTest.RH.CFBRCEtaCriticalMirrorPairedFramePositiveDensityRotationLimit"

noncomputable section
namespace DkMath.RH.CFBRCProjection

open Filter
open scoped BigOperators Topology

example
    (S : EtaPairPositiveDensityBlockSchedule)
    (s : ℂ) :
    Tendsto
      (S.scheduledBlockPhase s)
      atTop
      (nhds
        (s.im * Real.log (1 + 2 * S.density))) :=
  S.scheduledBlockPhase_tendsto s

example
    (S : EtaPairPositiveDensityBlockSchedule)
    (s : ℂ) :
    Tendsto
      (S.scheduledBlockRotation s)
      atTop
      (nhds (S.scheduledBlockRotationLimit s)) :=
  S.scheduledBlockRotation_tendsto s

example (s : ℂ) :
    Tendsto
      (etaPairHalfDensityBlockSchedule.scheduledBlockPhase s)
      atTop
      (nhds (s.im * Real.log 2)) :=
  etaPairHalfDensityBlockSchedule_scheduledBlockPhase_tendsto s

example (s : ℂ) :
    Tendsto
      (etaPairHalfDensityBlockSchedule.scheduledBlockRotation s)
      atTop
      (nhds
        (Complex.exp
          (Complex.I * (((s.im * Real.log 2 : ℝ) : ℂ))))) :=
  etaPairHalfDensityBlockSchedule_scheduledBlockRotation_tendsto s

end DkMath.RH.CFBRCProjection
