import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameExactGaugeObstruction

#print "file: DkMathTest.RH.CFBRCEtaCriticalMirrorPairedFrameExactGaugeObstruction"

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open scoped BigOperators Topology

example {s ω : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) :
    EtaCriticalMirrorPairedFrameExactGaugeObstructionCertificate s ω :=
  etaCriticalMirrorPairedFrameExactGaugeClosureDecision hs him

example {s ω : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) :
    ¬ Summable (etaPairFrameStepSpan s) := by
  exact
    (etaCriticalMirrorPairedFrameExactGaugeClosureDecision
      (ω := ω) hs him).step_span_not_summable

example {s ω : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) :
    Tendsto
      (fun K : ℕ =>
        etaCriticalMirrorGaugeRenormalizedProjectedPartial K ω s)
      atTop (nhds 0) := by
  exact
    (etaCriticalMirrorPairedFrameExactGaugeClosureDecision
      hs him).fixed_projection_tendsto_zero

end DkMath.RH.CFBRCProjection
