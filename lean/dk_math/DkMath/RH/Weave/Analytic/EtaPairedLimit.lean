/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.Weave.Analytic.EtaEvenPairing
import Mathlib.Tactic

#print "file: DkMath.RH.Weave.Analytic.EtaPairedLimit"

namespace DkMath.RH.Weave.Analytic

open Filter
open scoped Topology
open DkMath.RH.CFBRCProjection

/-- The even-index map `K ↦ 2K` is cofinal in the natural numbers. -/
theorem tendsto_two_mul_atTop :
    Tendsto (fun K : ℕ => 2 * K) atTop atTop := by
  refine tendsto_atTop.2 ?_
  intro b
  exact eventually_atTop.2 ⟨b, by
    intro a ha
    omega⟩

/--
Convergence of the full finite eta endpoint sequence implies convergence of
the paired-difference partial sums to the same analytic eta value.
-/
theorem etaPairedPartial_tendsto_analyticEta
    {s : ℂ} (hconv : EtaPartialConvergesAt s) :
    Tendsto (fun K : ℕ => etaPairedPartial K s)
      atTop (nhds (analyticEta s)) := by
  unfold EtaPartialConvergesAt at hconv
  have heven := hconv.comp tendsto_two_mul_atTop
  refine heven.congr' (Eventually.of_forall fun K => ?_)
  exact etaPartialEndpoint_two_mul_eq_etaPairedPartial K s

/-- An analytic eta zero gives a zero limit for the paired differences. -/
theorem etaPairedPartial_tendsto_zero_of_analyticEta_eq_zero
    {s : ℂ} (hconv : EtaPartialConvergesAt s)
    (heta : analyticEta s = 0) :
    Tendsto (fun K : ℕ => etaPairedPartial K s) atTop (nhds 0) := by
  simpa [heta] using etaPairedPartial_tendsto_analyticEta hconv

/-- A standard zeta zero gives a zero limit for the paired differences. -/
theorem etaPairedPartial_tendsto_zero_of_riemannZeta_eq_zero
    {s : ℂ} (hconv : EtaPartialConvergesAt s)
    (hz : riemannZeta s = 0) :
    Tendsto (fun K : ℕ => etaPairedPartial K s) atTop (nhds 0) := by
  exact etaPairedPartial_tendsto_zero_of_analyticEta_eq_zero hconv
    (analyticEta_eq_zero_of_riemannZeta_eq_zero hz)

/--
Right-half-plane eta convergence therefore maps every standard zeta zero in
that half-plane to a zero paired-difference limit.
-/
theorem etaPairedPartial_tendsto_zero_of_halfPlaneConvergence
    (bridge : EtaHalfPlaneConvergence) {s : ℂ}
    (hs : 0 < s.re) (hz : riemannZeta s = 0) :
    Tendsto (fun K : ℕ => etaPairedPartial K s) atTop (nhds 0) := by
  exact etaPairedPartial_tendsto_zero_of_riemannZeta_eq_zero
    (bridge.converges hs) hz

end DkMath.RH.Weave.Analytic
