/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameGaugeAudit

#print "file: DkMathTest.RH.CFBRCEtaCriticalMirrorPairedFrameGaugeAudit"

noncomputable section

namespace DkMathTest.RH.CFBRCEtaCriticalMirrorPairedFrameGaugeAudit

open Filter
open scoped Topology
open DkMath.RH.CFBRCProjection

example (s : ℂ) (k : ℕ) :
    etaPairBaseCounterRotation s k * etaPairBaseRotation s k = 1 :=
  etaPairBaseCounterRotation_mul_baseRotation s k

example (s : ℂ) (k : ℕ) :
    etaCriticalMirrorGaugeRenormalizedDefectPairTerm s k =
      etaCriticalMirrorDefectPairTerm s k :=
  etaCriticalMirrorGaugeRenormalizedDefectPairTerm_eq s k

example (K : ℕ) (s : ℂ) :
    etaCriticalMirrorGaugeRenormalizedDefectPairedPartial K s =
      etaCriticalMirrorDefectPairedPartial K s :=
  etaCriticalMirrorGaugeRenormalizedDefectPairedPartial_eq K s

example (K : ℕ) (ω s : ℂ) :
    etaCriticalMirrorGaugeRenormalizedProjectedPartial K ω s =
      etaCriticalMirrorProjectedDefectPairedPartial K ω s :=
  etaCriticalMirrorGaugeRenormalizedProjectedPartial_eq K ω s

example
    {s ω : ℂ} (hs : NontrivialRiemannZetaZero s) (him : s.im ≠ 0) :
    Tendsto
      (fun K : ℕ =>
        etaCriticalMirrorGaugeRenormalizedProjectedPartial K ω s)
      atTop (nhds 0) :=
  etaCriticalMirrorGaugeRenormalizedProjectedPartial_tendsto_zero_of_nontrivialRiemannZetaZero
    hs him

end DkMathTest.RH.CFBRCEtaCriticalMirrorPairedFrameGaugeAudit
