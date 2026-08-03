/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPhaseProjection
import Mathlib.Tactic

#print "file: DkMathTest.RH.CFBRCEtaCriticalMirrorPhaseProjection"

noncomputable section

namespace DkMathTest.RH.CFBRCEtaCriticalMirrorPhaseProjection

open Filter
open scoped Topology
open DkMath.RH.CFBRCProjection

example (N : ℕ) (ω s : ℂ) :
    etaCriticalMirrorProjectedDefectEndpoint N ω s =
      (Finset.range N).sum
        (etaCriticalMirrorProjectedDefectTerm ω s) :=
  etaCriticalMirrorProjectedDefectEndpoint_eq_sum N ω s

example
    {s ω : ℂ} (hs : NontrivialRiemannZetaZero s) (him : s.im ≠ 0) :
    Tendsto
      (fun N : ℕ => etaCriticalMirrorProjectedDefectEndpoint N ω s)
      atTop (nhds 0) :=
  etaCriticalMirrorProjectedDefectEndpoint_tendsto_zero_of_nontrivialRiemannZetaZero
    hs him

example
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) (him : s.im ≠ 0) :
    ¬ EtaCriticalMirrorDefectHalfPlaneCertificate s :=
  not_etaCriticalMirrorDefectHalfPlaneCertificate_of_nontrivialRiemannZetaZero
    hs him

example
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) (him : s.im ≠ 0)
    (hsep : EtaCriticalMirrorOffCriticalHalfPlaneSeparation s) :
    s.re = (1 : ℝ) / 2 :=
  re_eq_half_of_nontrivialRiemannZetaZero_of_offCriticalHalfPlaneSeparation
    hs him hsep

example
    {d : ℕ} (hd : 0 < d) {s : ℂ} (Θ : ℝ)
    (hs : NontrivialRiemannZetaZero s) (him : s.im ≠ 0)
    (hsep : EtaCriticalMirrorOffCriticalHalfPlaneSeparation s) :
    offCriticalCFBRC d s.re Θ = 0 :=
  offCriticalCFBRC_eq_zero_of_nontrivialRiemannZetaZero_of_offCriticalHalfPlaneSeparation
    hd Θ hs him hsep

end DkMathTest.RH.CFBRCEtaCriticalMirrorPhaseProjection
