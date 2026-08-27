/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.Weave.Analytic.EtaPairedContinuation
import DkMath.RH.Weave.Finite.EtaPairDecomposition
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

#print "file: DkMath.RH.Weave.Analytic.EtaEnergyLimit"

noncomputable section

namespace DkMath.RH.Weave.Analytic

open Filter
open scoped Topology
open DkMath.RH.CFBRCProjection
open DkMath.RH.Weave.Finite

/--
The finite antisymmetric eta energy is one half of the squared norm of the
finite eta endpoint.  Thus the geometric energy carries exactly the same
vanishing information as the genuine alternating endpoint, with no extra
closure assumption.
-/
theorem etaAntisymmetricEnergy_eq_half_normSq_endpoint
    (N : ℕ) (s : ℂ) :
    etaAntisymmetricEnergy N s =
      (1 / 2 : ℝ) * Complex.normSq (etaPartialEndpoint N s) := by
  have hnorm :
      Complex.normSq (etaPartialEndpoint N s) =
        4 * Complex.normSq (etaPairOffset N s) := by
    rw [etaPartialEndpoint_eq_two_mul_pairOffset]
    simp [Complex.normSq_apply]
    ring
  unfold etaAntisymmetricEnergy
  rw [hnorm]
  ring

/--
A zero limit of the finite eta endpoints forces the antisymmetric Pair Energy
to vanish in the limit.
-/
theorem etaAntisymmetricEnergy_tendsto_zero_of_endpoint_tendsto_zero
    {s : ℂ}
    (hzero :
      Tendsto (fun N : ℕ => etaPartialEndpoint N s) atTop (nhds 0)) :
    Tendsto (fun N : ℕ => etaAntisymmetricEnergy N s) atTop (nhds 0) := by
  have hnorm :
      Tendsto
        (fun N : ℕ => Complex.normSq (etaPartialEndpoint N s))
        atTop (nhds (Complex.normSq 0)) :=
    Complex.continuous_normSq.continuousAt.tendsto.comp hzero
  have hscaled :
      Tendsto
        (fun N : ℕ => (1 / 2 : ℝ) * Complex.normSq (etaPartialEndpoint N s))
        atTop (nhds ((1 / 2 : ℝ) * Complex.normSq 0)) :=
    tendsto_const_nhds.mul hnorm
  have hfun :
      (fun N : ℕ => etaAntisymmetricEnergy N s) =
        (fun N : ℕ => (1 / 2 : ℝ) * Complex.normSq (etaPartialEndpoint N s)) := by
    funext N
    exact etaAntisymmetricEnergy_eq_half_normSq_endpoint N s
  rw [hfun]
  simpa using hscaled

/--
At every nonreal point of the open right half-plane, a standard zeta zero
forces the genuine finite eta antisymmetric energy to tend to zero.
-/
theorem etaAntisymmetricEnergy_tendsto_zero_of_riemannZeta_eq_zero_of_pos_re_of_im_ne_zero
    {s : ℂ} (hre : 0 < s.re) (him : s.im ≠ 0)
    (hz : riemannZeta s = 0) :
    Tendsto (fun N : ℕ => etaAntisymmetricEnergy N s) atTop (nhds 0) := by
  exact etaAntisymmetricEnergy_tendsto_zero_of_endpoint_tendsto_zero
    (etaPartialEndpoint_tendsto_zero_of_riemannZeta_eq_zero_of_pos_re_of_im_ne_zero
      hre him hz)

end DkMath.RH.Weave.Analytic
