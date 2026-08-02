/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaKUSLimit
import DkMath.RH.CFBRC.EtaKUSMirrorUnitBridge
import DkMath.RH.CFBRC.StandardZetaBridge
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.EtaKUSMirrorGapBridgeAudit"

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open scoped Topology
open DkMath.KUS
open DkMath.RH.Weave.Analytic

/-!
# Audit of the remaining KUS mirror-Gap bridge

A zeta zero makes the visible coefficient of the unit KUS trace tend to zero.
The mirror unit Gap, however, is reconstructed from the retained point and is
constant along the truncation trace.  Therefore an additional statement saying
that coefficient vanishing forces mirror-Gap vanishing is load-bearing.

This file fixes that boundary exactly.  At a nonreal right-half-plane zeta zero,
the coefficient-to-Gap coupling condition is equivalent to membership on the
critical line.  For the standard nontrivial-zero predicate, existence of a
uniform mirror-Gap bridge is equivalent to Mathlib's `RiemannHypothesis`.
-/

/-- Visible coefficient sequence of the unit-rotation eta KUS trace. -/
noncomputable def etaUnitKUSCoefficientTrace (s : ℂ) : ℕ → ℂ :=
  fun N => toCoeff (etaUnitKUSTrace s N)

/-- Mirror unit-Gap sequence reconstructed from the retained KUS point. -/
noncomputable def etaUnitKUSMirrorGapTrace (s : ℂ) : ℕ → ℝ :=
  fun N => etaKUSMirrorUnitGap (etaUnitKUSTrace s N) 1

@[simp] theorem etaUnitKUSCoefficientTrace_apply (s : ℂ) (N : ℕ) :
    etaUnitKUSCoefficientTrace s N = etaPartialEndpoint (N + 1) s := by
  rfl

@[simp] theorem etaUnitKUSMirrorGapTrace_apply (s : ℂ) (N : ℕ) :
    etaUnitKUSMirrorGapTrace s N = etaMirrorUnitGap s 1 := by
  rfl

/-- The KUS mirror-Gap trace is constant because every stage retains the same point. -/
theorem etaUnitKUSMirrorGapTrace_tendsto (s : ℂ) :
    Tendsto (etaUnitKUSMirrorGapTrace s) atTop
      (nhds (etaMirrorUnitGap s 1)) := by
  simpa only [etaUnitKUSMirrorGapTrace_apply] using
    (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => etaMirrorUnitGap s 1) atTop
        (nhds (etaMirrorUnitGap s 1)))

/-- Gap-trace convergence to zero is exactly the critical-line condition. -/
theorem etaUnitKUSMirrorGapTrace_tendsto_zero_iff_re_eq_half (s : ℂ) :
    Tendsto (etaUnitKUSMirrorGapTrace s) atTop (nhds 0) ↔
      s.re = (1 : ℝ) / 2 := by
  constructor
  · intro hzero
    have hgap : etaMirrorUnitGap s 1 = 0 :=
      tendsto_nhds_unique (etaUnitKUSMirrorGapTrace_tendsto s) hzero
    exact (etaMirrorUnitGap_one_eq_zero_iff_re_eq_half s).mp hgap
  · intro hre
    have hgap : etaMirrorUnitGap s 1 = 0 :=
      (etaMirrorUnitGap_one_eq_zero_iff_re_eq_half s).2 hre
    simpa only [hgap] using etaUnitKUSMirrorGapTrace_tendsto s

/--
Pointwise coupling assertion: if the visible eta coefficient tends to zero,
then the independently retained mirror unit Gap also tends to zero.
-/
def EtaKUSCoefficientMirrorGapCoupledAt (s : ℂ) : Prop :=
  Tendsto (etaUnitKUSCoefficientTrace s) atTop (nhds 0) →
    Tendsto (etaUnitKUSMirrorGapTrace s) atTop (nhds 0)

/-- A nonreal right-half-plane zeta zero supplies coefficient convergence. -/
theorem etaUnitKUSCoefficientTrace_tendsto_zero_of_riemannZeta_zero
    {s : ℂ} (hre : 0 < s.re) (him : s.im ≠ 0)
    (hz : riemannZeta s = 0) :
    Tendsto (etaUnitKUSCoefficientTrace s) atTop (nhds 0) := by
  simpa only [etaUnitKUSCoefficientTrace] using
    toCoeff_etaUnitKUSTrace_tendsto_zero_of_riemannZeta_zero hre him hz

/--
Load-bearing pointwise audit: at a zeta zero where coefficient convergence is
already known, coefficient-to-Gap coupling is equivalent to the critical line.
-/
theorem etaKUSCoefficientMirrorGapCoupledAt_iff_re_eq_half
    {s : ℂ} (hre : 0 < s.re) (him : s.im ≠ 0)
    (hz : riemannZeta s = 0) :
    EtaKUSCoefficientMirrorGapCoupledAt s ↔
      s.re = (1 : ℝ) / 2 := by
  constructor
  · intro hcoupled
    apply (etaUnitKUSMirrorGapTrace_tendsto_zero_iff_re_eq_half s).mp
    exact hcoupled
      (etaUnitKUSCoefficientTrace_tendsto_zero_of_riemannZeta_zero hre him hz)
  · intro hreHalf _
    exact (etaUnitKUSMirrorGapTrace_tendsto_zero_iff_re_eq_half s).2 hreHalf

/-- A uniform KUS mirror-Gap-zero bridge for an arbitrary zero predicate. -/
structure EtaKUSMirrorGapZeroBridge (Zero : ℂ → Prop) where
  gap_tendsto_zero : ∀ {s : ℂ}, Zero s →
    Tendsto (etaUnitKUSMirrorGapTrace s) atTop (nhds 0)

/-- Standard nontrivial-zeta specialization of the mirror-Gap bridge. -/
abbrev StandardZetaEtaKUSMirrorGapZeroBridge :=
  EtaKUSMirrorGapZeroBridge NontrivialRiemannZetaZero

/-- A standard-zeta mirror-Gap bridge proves Mathlib's formal RH statement. -/
theorem riemannHypothesis_of_standardZetaEtaKUSMirrorGapZeroBridge
    (bridge : StandardZetaEtaKUSMirrorGapZeroBridge) :
    RiemannHypothesis := by
  rw [riemannHypothesis_iff_nontrivialZero_re_eq_half]
  intro s hs
  exact (etaUnitKUSMirrorGapTrace_tendsto_zero_iff_re_eq_half s).mp
    (bridge.gap_tendsto_zero hs)

/-- RH constructs the corresponding standard-zeta mirror-Gap bridge. -/
noncomputable def standardZetaEtaKUSMirrorGapZeroBridge_of_riemannHypothesis
    (hRH : RiemannHypothesis) :
    StandardZetaEtaKUSMirrorGapZeroBridge where
  gap_tendsto_zero := fun {s} hs =>
    (etaUnitKUSMirrorGapTrace_tendsto_zero_iff_re_eq_half s).2
      ((riemannHypothesis_iff_nontrivialZero_re_eq_half.mp hRH) s hs)

/--
Exact global audit: merely inhabiting the standard mirror-Gap bridge is neither
weaker nor stronger than RH; it is an equivalent formulation of the remaining
analytic obligation.
-/
theorem nonempty_standardZetaEtaKUSMirrorGapZeroBridge_iff_riemannHypothesis :
    Nonempty StandardZetaEtaKUSMirrorGapZeroBridge ↔
      RiemannHypothesis := by
  constructor
  · rintro ⟨bridge⟩
    exact riemannHypothesis_of_standardZetaEtaKUSMirrorGapZeroBridge bridge
  · intro hRH
    exact ⟨standardZetaEtaKUSMirrorGapZeroBridge_of_riemannHypothesis hRH⟩

end DkMath.RH.CFBRCProjection
