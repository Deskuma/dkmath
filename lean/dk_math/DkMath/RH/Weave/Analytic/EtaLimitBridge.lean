/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.Weave.Finite.EtaPairDecomposition
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Tactic

#print "file: DkMath.RH.Weave.Analytic.EtaLimitBridge"

namespace DkMath.RH.Weave.Analytic

open Filter
open scoped Topology
open DkMath.RH.CFBRCProjection
open DkMath.RH.Weave.Finite

/--
Analytically continued Dirichlet eta value, expressed through Mathlib's
standard Riemann zeta function.

This is a value-level definition.  Identification with the limit of the
alternating finite eta endpoints is recorded separately by
`EtaPartialConvergesAt` and is not built into the definition.
-/
noncomputable def analyticEta (s : ℂ) : ℂ :=
  (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s

/--
The finite alternating eta endpoints converge to the analytically continued
eta value at `s`.

This predicate isolates the genuine infinite-series obligation.  It contains
no critical-line conclusion and no CFBRC zero statement.
-/
def EtaPartialConvergesAt (s : ℂ) : Prop :=
  Tendsto (fun N : ℕ => etaPartialEndpoint N s)
    atTop (nhds (analyticEta s))

/-- A reusable realization of eta convergence on the open right half-plane. -/
structure EtaHalfPlaneConvergence where
  converges : ∀ {s : ℂ}, 0 < s.re → EtaPartialConvergesAt s

/-- Every standard zeta zero is automatically an analytic-eta zero. -/
theorem analyticEta_eq_zero_of_riemannZeta_eq_zero
    {s : ℂ} (hz : riemannZeta s = 0) :
    analyticEta s = 0 := by
  simp [analyticEta, hz]

/--
Under the eta convergence obligation, an analytic-eta zero is exactly a zero
limit of the finite alternating endpoints.
-/
theorem etaPartialEndpoint_tendsto_zero_of_analyticEta_eq_zero
    {s : ℂ} (hconv : EtaPartialConvergesAt s)
    (heta : analyticEta s = 0) :
    Tendsto (fun N : ℕ => etaPartialEndpoint N s) atTop (nhds 0) := by
  simpa [EtaPartialConvergesAt, heta] using hconv

/-- Uniqueness of limits recovers the analytic eta zero from a zero endpoint limit. -/
theorem analyticEta_eq_zero_of_etaPartialEndpoint_tendsto_zero
    {s : ℂ} (hconv : EtaPartialConvergesAt s)
    (hzero :
      Tendsto (fun N : ℕ => etaPartialEndpoint N s) atTop (nhds 0)) :
    analyticEta s = 0 := by
  exact tendsto_nhds_unique hconv hzero

/-- Exact limit-level characterization of analytic eta zeros. -/
theorem etaPartialEndpoint_tendsto_zero_iff_analyticEta_eq_zero
    {s : ℂ} (hconv : EtaPartialConvergesAt s) :
    Tendsto (fun N : ℕ => etaPartialEndpoint N s) atTop (nhds 0) ↔
      analyticEta s = 0 := by
  constructor
  · exact analyticEta_eq_zero_of_etaPartialEndpoint_tendsto_zero hconv
  · exact etaPartialEndpoint_tendsto_zero_of_analyticEta_eq_zero hconv

/--
A standard zeta zero produces a zero limit of the genuine finite eta endpoint
sequence, once eta convergence at the same complex coordinate has been proved.
-/
theorem etaPartialEndpoint_tendsto_zero_of_riemannZeta_eq_zero
    {s : ℂ} (hconv : EtaPartialConvergesAt s)
    (hz : riemannZeta s = 0) :
    Tendsto (fun N : ℕ => etaPartialEndpoint N s) atTop (nhds 0) := by
  exact etaPartialEndpoint_tendsto_zero_of_analyticEta_eq_zero hconv
    (analyticEta_eq_zero_of_riemannZeta_eq_zero hz)

/-- Right-half-plane eta convergence specializes the previous zero-limit bridge. -/
theorem etaPartialEndpoint_tendsto_zero_of_halfPlaneConvergence
    (bridge : EtaHalfPlaneConvergence) {s : ℂ}
    (hs : 0 < s.re) (hz : riemannZeta s = 0) :
    Tendsto (fun N : ℕ => etaPartialEndpoint N s) atTop (nhds 0) := by
  exact etaPartialEndpoint_tendsto_zero_of_riemannZeta_eq_zero
    (bridge.converges hs) hz

end DkMath.RH.Weave.Analytic
