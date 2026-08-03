/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.CriticalMirrorZeroBridge
import DkMath.RH.Weave.Analytic.EtaPairedContinuation
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.EtaCriticalMirrorEndpointLimits"

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open scoped Topology
open DkMath.RH.Weave.Analytic

/-- A nonreal nontrivial zeta zero has a vanishing finite eta endpoint. -/
theorem etaPartialEndpoint_tendsto_zero_of_nontrivialRiemannZetaZero
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) (him : s.im ≠ 0) :
    Tendsto (fun N : ℕ => etaPartialEndpoint N s) atTop (nhds 0) := by
  exact
    etaPartialEndpoint_tendsto_zero_of_riemannZeta_eq_zero_of_pos_re_of_im_ne_zero
      (nontrivialRiemannZetaZero_re_pos hs) him hs.1

/-- The critical-mirror eta endpoint vanishes along the same truncation limit. -/
theorem etaPartialEndpoint_criticalMirror_tendsto_zero_of_nontrivialRiemannZetaZero
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) (him : s.im ≠ 0) :
    Tendsto (fun N : ℕ => etaPartialEndpoint N (criticalMirror s))
      atTop (nhds 0) := by
  have himMirror : (criticalMirror s).im ≠ 0 := by
    simpa using him
  exact
    etaPartialEndpoint_tendsto_zero_of_riemannZeta_eq_zero_of_pos_re_of_im_ne_zero
      (criticalMirror_re_pos_of_nontrivialRiemannZetaZero hs)
      himMirror
      (riemannZeta_criticalMirror_eq_zero_of_nontrivialRiemannZetaZero hs)

/-- Both original and critical-mirror endpoint limits packaged together. -/
structure EtaCriticalMirrorEndpointVanishing (s : ℂ) : Prop where
  original : Tendsto (fun N : ℕ => etaPartialEndpoint N s) atTop (nhds 0)
  mirror : Tendsto (fun N : ℕ => etaPartialEndpoint N (criticalMirror s))
    atTop (nhds 0)

/-- Build the two-sided endpoint-vanishing certificate from a nonreal zero. -/
theorem etaCriticalMirrorEndpointVanishing_of_nontrivialRiemannZetaZero
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) (him : s.im ≠ 0) :
    EtaCriticalMirrorEndpointVanishing s where
  original := etaPartialEndpoint_tendsto_zero_of_nontrivialRiemannZetaZero hs him
  mirror :=
    etaPartialEndpoint_criticalMirror_tendsto_zero_of_nontrivialRiemannZetaZero
      hs him

/-- The mirror-minus-original finite endpoint displacement tends to zero. -/
theorem etaCriticalMirrorEndpoint_sub_tendsto_zero_of_nontrivialRiemannZetaZero
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) (him : s.im ≠ 0) :
    Tendsto
      (fun N : ℕ =>
        etaPartialEndpoint N (criticalMirror s) - etaPartialEndpoint N s)
      atTop (nhds 0) := by
  have hpair :=
    etaCriticalMirrorEndpointVanishing_of_nontrivialRiemannZetaZero hs him
  simpa using hpair.mirror.sub hpair.original

/-- The mirror-plus-original finite endpoint sum also tends to zero. -/
theorem etaCriticalMirrorEndpoint_add_tendsto_zero_of_nontrivialRiemannZetaZero
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) (him : s.im ≠ 0) :
    Tendsto
      (fun N : ℕ =>
        etaPartialEndpoint N (criticalMirror s) + etaPartialEndpoint N s)
      atTop (nhds 0) := by
  have hpair :=
    etaCriticalMirrorEndpointVanishing_of_nontrivialRiemannZetaZero hs him
  simpa using hpair.mirror.add hpair.original

end DkMath.RH.CFBRCProjection
