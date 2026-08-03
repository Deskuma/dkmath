/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedPhaseProjection
import Mathlib.Tactic

#print "file: DkMathTest.RH.CFBRCEtaCriticalMirrorPairedPhaseProjection"

noncomputable section

namespace DkMathTest.RH.CFBRCEtaCriticalMirrorPairedPhaseProjection

open Filter
open scoped Topology
open DkMath.RH.CFBRCProjection

example (K : ℕ) (s : ℂ) :
    etaCriticalMirrorTransportDefectEndpoint (2 * K) s =
      etaCriticalMirrorDefectPairedPartial K s :=
  etaCriticalMirrorTransportDefectEndpoint_two_mul_eq_pairedPartial K s

example (K : ℕ) (ω s : ℂ) :
    etaCriticalMirrorProjectedDefectPairedPartial K ω s =
      (Finset.range K).sum
        (etaCriticalMirrorProjectedDefectPairTerm ω s) :=
  etaCriticalMirrorProjectedDefectPairedPartial_eq_sum K ω s

example
    {s ω : ℂ} (hs : NontrivialRiemannZetaZero s) (him : s.im ≠ 0) :
    Tendsto
      (fun K : ℕ => etaCriticalMirrorProjectedDefectPairedPartial K ω s)
      atTop (nhds 0) :=
  etaCriticalMirrorProjectedDefectPairedPartial_tendsto_zero_of_nontrivialRiemannZetaZero
    hs him

example
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) (him : s.im ≠ 0) :
    EtaCriticalMirrorDefectPairHalfPlaneCertificate s → False :=
  not_etaCriticalMirrorDefectPairHalfPlaneCertificate_of_nontrivialRiemannZetaZero
    hs him

example
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) (him : s.im ≠ 0)
    (hsep : EtaCriticalMirrorOffCriticalPairHalfPlaneSeparation s) :
    s.re = (1 : ℝ) / 2 :=
  re_eq_half_of_nontrivialRiemannZetaZero_of_offCriticalPairHalfPlaneSeparation
    hs him hsep

example
    {d : ℕ} (hd : 0 < d) {s : ℂ} (Θ : ℝ)
    (hs : NontrivialRiemannZetaZero s) (him : s.im ≠ 0)
    (hsep : EtaCriticalMirrorOffCriticalPairHalfPlaneSeparation s) :
    offCriticalCFBRC d s.re Θ = 0 :=
  offCriticalCFBRC_eq_zero_of_nontrivialRiemannZetaZero_of_offCriticalPairHalfPlaneSeparation
    hd Θ hs him hsep

end DkMathTest.RH.CFBRCEtaCriticalMirrorPairedPhaseProjection
