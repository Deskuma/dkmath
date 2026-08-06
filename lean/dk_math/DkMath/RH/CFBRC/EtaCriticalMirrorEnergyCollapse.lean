/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorEndpointLimits
import DkMath.RH.CFBRC.EtaMirrorEndpointOuterNormalization
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.EtaCriticalMirrorEnergyCollapse"

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open scoped Topology

/--
At every nonreal nontrivial zeta zero, all absolute original/mirror endpoint
energy coordinates collapse to zero.
-/
structure EtaCriticalMirrorEnergyCollapse (s : ℂ) : Prop where
  totalEnergy :
    Tendsto (fun N : ℕ => etaMirrorEndpointTotalEnergy N s)
      atTop (nhds 0)
  core :
    Tendsto (fun N : ℕ => etaMirrorEndpointCore N s)
      atTop (nhds 0)
  gapCore :
    Tendsto (fun N : ℕ => etaMirrorEndpointGapCore N s)
      atTop (nhds 0)
  outerBig :
    Tendsto (fun N : ℕ => etaMirrorEndpointOuterBig N s)
      atTop (nhds 0)

/-- The paired endpoint Total/Core/Gap coordinates all vanish at a nonreal zero. -/
theorem etaCriticalMirror_pairEnergy_tendsto_zero
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) (him : s.im ≠ 0) :
    Tendsto (fun N : ℕ => etaMirrorEndpointTotalEnergy N s)
        atTop (nhds 0) ∧
      Tendsto (fun N : ℕ => etaMirrorEndpointCore N s)
        atTop (nhds 0) ∧
      Tendsto (fun N : ℕ => etaMirrorEndpointGapCore N s)
        atTop (nhds 0) := by
  have hpair :=
    etaCriticalMirrorEndpointVanishing_of_nontrivialRiemannZetaZero hs him
  exact
    ⟨etaMirrorEndpointTotalEnergy_tendsto_zero_of_endpoint_limits
        hpair.original hpair.mirror,
      by
        simpa only [etaMirrorEndpointCore_eq] using
          etaMirrorEndpointBig_tendsto_zero_of_endpoint_limits
            hpair.original hpair.mirror,
      by
        simpa only [etaMirrorEndpointGapCore_eq] using
          etaMirrorEndpointGap_tendsto_zero_of_endpoint_limits
            hpair.original hpair.mirror⟩

/-- The shared outer denominator also collapses to zero. -/
theorem etaMirrorEndpointOuterBig_tendsto_zero_of_nontrivialRiemannZetaZero
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) (him : s.im ≠ 0) :
    Tendsto (fun N : ℕ => etaMirrorEndpointOuterBig N s)
      atTop (nhds 0) := by
  have htotal :=
    (etaCriticalMirror_pairEnergy_tendsto_zero hs him).1
  have hscaled :
      Tendsto (fun N : ℕ => 2 * etaMirrorEndpointTotalEnergy N s)
        atTop (nhds (2 * 0)) :=
    tendsto_const_nhds.mul htotal
  simpa only [etaMirrorEndpointOuterBig_eq_two_mul_totalEnergy, mul_zero] using
    hscaled

/-- Build the complete absolute-energy collapse certificate. -/
theorem etaCriticalMirrorEnergyCollapse_of_nontrivialRiemannZetaZero
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) (him : s.im ≠ 0) :
    EtaCriticalMirrorEnergyCollapse s := by
  have henergy := etaCriticalMirror_pairEnergy_tendsto_zero hs him
  exact
    { totalEnergy := henergy.1
      core := henergy.2.1
      gapCore := henergy.2.2
      outerBig :=
        etaMirrorEndpointOuterBig_tendsto_zero_of_nontrivialRiemannZetaZero
          hs him }

end DkMath.RH.CFBRCProjection
