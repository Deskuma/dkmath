/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.StandardZetaBridge
import DkMath.RH.Weave.Analytic.EtaEnergyLimit
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.EtaEnergyBridge"

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open scoped Topology
open DkMath.RH.Weave.Finite
open DkMath.RH.Weave.Analytic

/--
If the same finite antisymmetric eta energy tends both to zero and to the
square of the centered real coordinate, then that centered coordinate
vanishes.

This is the limit-uniqueness kernel of the eta-energy-to-CFBRC weave.  The
statement does not assume a critical-line conclusion.
-/
theorem centeredSigma_eq_zero_of_etaEnergy_limits
    {s : ℂ}
    (hzero :
      Tendsto (fun N : ℕ => etaAntisymmetricEnergy N s)
        atTop (nhds 0))
    (hcenter :
      Tendsto (fun N : ℕ => etaAntisymmetricEnergy N s)
        atTop (nhds (centeredSigma s.re ^ 2))) :
    centeredSigma s.re = 0 := by
  have hsq : (0 : ℝ) = centeredSigma s.re ^ 2 :=
    tendsto_nhds_unique hzero hcenter
  nlinarith [sq_nonneg (centeredSigma s.re)]

/--
Two compatible eta-energy limits map directly into the standard positive-
degree CFBRC zero locus.
-/
theorem offCriticalCFBRC_eq_zero_of_etaEnergy_limits
    {d : ℕ} (hd : 0 < d) {s : ℂ} (Θ : ℝ)
    (hzero :
      Tendsto (fun N : ℕ => etaAntisymmetricEnergy N s)
        atTop (nhds 0))
    (hcenter :
      Tendsto (fun N : ℕ => etaAntisymmetricEnergy N s)
        atTop (nhds (centeredSigma s.re ^ 2))) :
    offCriticalCFBRC d s.re Θ = 0 := by
  apply (offCriticalCFBRC_eq_zero_iff_re_eq_half hd s.re Θ).2
  exact (centeredSigma_eq_zero_iff s.re).mp
    (centeredSigma_eq_zero_of_etaEnergy_limits hzero hcenter)

/--
At a nonreal zeta zero in the open right half-plane, it is enough to identify
the limiting antisymmetric eta energy with `(s.re - 1/2)^2` in order to obtain
the standard CFBRC zero equation.
-/
theorem offCriticalCFBRC_eq_zero_of_riemannZeta_zero_of_etaEnergy_center_limit
    {d : ℕ} (hd : 0 < d) {s : ℂ} (Θ : ℝ)
    (hre : 0 < s.re) (him : s.im ≠ 0)
    (hz : riemannZeta s = 0)
    (hcenter :
      Tendsto (fun N : ℕ => etaAntisymmetricEnergy N s)
        atTop (nhds (centeredSigma s.re ^ 2))) :
    offCriticalCFBRC d s.re Θ = 0 := by
  exact offCriticalCFBRC_eq_zero_of_etaEnergy_limits hd Θ
    (etaAntisymmetricEnergy_tendsto_zero_of_riemannZeta_eq_zero_of_pos_re_of_im_ne_zero
      hre him hz)
    hcenter

/--
Abstract zero predicate whose selected points carry two compatible eta-energy
limits.  The first limit is zero; the second identifies the same energy with
the square of the centered real coordinate.
-/
structure EtaEnergyCFBRCBridge (Zero : ℂ → Prop) where
  d : ℕ
  hd : 0 < d
  phase : ℂ → ℝ
  energy_tendsto_zero : ∀ {s : ℂ}, Zero s →
    Tendsto (fun N : ℕ => etaAntisymmetricEnergy N s)
      atTop (nhds 0)
  energy_tendsto_centeredSq : ∀ {s : ℂ}, Zero s →
    Tendsto (fun N : ℕ => etaAntisymmetricEnergy N s)
      atTop (nhds (centeredSigma s.re ^ 2))

/-- Every eta-energy bridge supplies the existing zero-to-CFBRC bridge. -/
def EtaEnergyCFBRCBridge.toZeroToCFBRCBridge
    {Zero : ℂ → Prop} (bridge : EtaEnergyCFBRCBridge Zero) :
    ZeroToCFBRCBridge Zero where
  d := bridge.d
  hd := bridge.hd
  phase := bridge.phase
  map_zero := fun hs =>
    offCriticalCFBRC_eq_zero_of_etaEnergy_limits
      bridge.hd (bridge.phase _) (bridge.energy_tendsto_zero hs)
        (bridge.energy_tendsto_centeredSq hs)

/-- A selected zero carried by an eta-energy bridge lies on the critical line. -/
theorem re_eq_half_of_etaEnergyCFBRCBridge
    {Zero : ℂ → Prop} (bridge : EtaEnergyCFBRCBridge Zero)
    {s : ℂ} (hs : Zero s) :
    s.re = (1 : ℝ) / 2 := by
  exact re_eq_half_of_zeroToCFBRCBridge bridge.toZeroToCFBRCBridge hs

/-- Standard-zeta specialization of the eta-energy bridge. -/
abbrev StandardZetaEtaEnergyCFBRCBridge :=
  EtaEnergyCFBRCBridge NontrivialRiemannZetaZero

/-- A standard-zeta eta-energy bridge proves Mathlib's formal RH statement. -/
theorem riemannHypothesis_of_standardZetaEtaEnergyCFBRCBridge
    (bridge : StandardZetaEtaEnergyCFBRCBridge) :
    RiemannHypothesis := by
  exact riemannHypothesis_of_standardZetaToCFBRCBridge
    bridge.toZeroToCFBRCBridge

end DkMath.RH.CFBRCProjection
