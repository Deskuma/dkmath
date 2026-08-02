/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.Weave.Analytic.EtaFiniteFactorization
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Tactic

#print "file: DkMath.RH.Weave.Analytic.EtaZetaIdentification"

namespace DkMath.RH.Weave.Analytic

open Filter
open scoped Topology
open DkMath.RH.CFBRCProjection

/-- The finite dyadic coefficient is the standard analytic-eta coefficient. -/
theorem etaDyadicCoefficient_eq_cpow_one_sub (s : ℂ) :
    etaDyadicCoefficient s = (2 : ℂ) ^ (1 - s) := by
  unfold etaDyadicCoefficient
  rw [show (1 - s : ℂ) = 1 + (-s) by ring]
  rw [Complex.cpow_add 1 (-s) (by norm_num : (2 : ℂ) ≠ 0)]
  simp

/-- The unsigned eta tsum is the standard zeta Dirichlet series for `re s > 1`. -/
theorem tsum_etaUnsignedVector_eq_riemannZeta
    {s : ℂ} (hs : 1 < s.re) :
    (∑' m : ℕ, etaUnsignedVector s m) = riemannZeta s := by
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs]
  apply tsum_congr
  intro m
  simpa using etaUnsignedVector_eq_one_div_cpow s m

/-- Unsigned finite Dirichlet partial sums converge to standard zeta. -/
theorem etaUnsignedPartial_tendsto_riemannZeta
    {s : ℂ} (hs : 1 < s.re) :
    Tendsto (fun K : ℕ => etaUnsignedPartial K s)
      atTop (nhds (riemannZeta s)) := by
  have hsum :=
    (summable_etaUnsignedVector_of_one_lt_re hs).hasSum.tendsto_sum_nat
  rw [tsum_etaUnsignedVector_eq_riemannZeta hs] at hsum
  simpa [etaUnsignedPartial] using hsum

/-- The cofinal even unsigned partial sums have the same zeta limit. -/
theorem etaUnsignedPartial_two_mul_tendsto_riemannZeta
    {s : ℂ} (hs : 1 < s.re) :
    Tendsto (fun K : ℕ => etaUnsignedPartial (2 * K) s)
      atTop (nhds (riemannZeta s)) := by
  simpa only [Function.comp_apply] using
    (etaUnsignedPartial_tendsto_riemannZeta hs).comp tendsto_two_mul_atTop

/-- Algebraic normal form of the finite-factorization limit. -/
theorem riemannZeta_sub_etaDyadicCoefficient_mul_eq_analyticEta
    (s : ℂ) :
    riemannZeta s - etaDyadicCoefficient s * riemannZeta s =
      analyticEta s := by
  rw [analyticEta, etaDyadicCoefficient_eq_cpow_one_sub]
  ring

/--
In the absolute-convergence half-plane, even finite eta endpoints converge to
the analytically continued eta value.
-/
theorem etaPartialEndpoint_two_mul_tendsto_analyticEta
    {s : ℂ} (hs : 1 < s.re) :
    Tendsto (fun K : ℕ => etaPartialEndpoint (2 * K) s)
      atTop (nhds (analyticEta s)) := by
  have hbase := etaUnsignedPartial_tendsto_riemannZeta hs
  have heven := etaUnsignedPartial_two_mul_tendsto_riemannZeta hs
  have hfactor :
      Tendsto
        (fun K : ℕ =>
          etaUnsignedPartial (2 * K) s -
            etaDyadicCoefficient s * etaUnsignedPartial K s)
        atTop
        (nhds
          (riemannZeta s -
            etaDyadicCoefficient s * riemannZeta s)) :=
    heven.sub (tendsto_const_nhds.mul hbase)
  have heta :
      Tendsto (fun K : ℕ => etaPartialEndpoint (2 * K) s)
        atTop
        (nhds
          (riemannZeta s -
            etaDyadicCoefficient s * riemannZeta s)) := by
    refine hfactor.congr' (Eventually.of_forall fun K => ?_)
    exact (etaPartialEndpoint_two_mul_factorization K s).symm
  rw [riemannZeta_sub_etaDyadicCoefficient_mul_eq_analyticEta] at heta
  exact heta

/-- The absolutely convergent signed eta tsum equals analytic eta. -/
theorem etaTsumIdentifiesAnalyticAt_of_one_lt_re
    {s : ℂ} (hs : 1 < s.re) :
    EtaTsumIdentifiesAnalyticAt s := by
  unfold EtaTsumIdentifiesAnalyticAt
  have hfullEven :
      Tendsto (fun K : ℕ => etaPartialEndpoint (2 * K) s)
        atTop (nhds (∑' m : ℕ, etaSignedVector s m)) := by
    simpa only [Function.comp_apply] using
      (etaPartialEndpoint_tendsto_tsum_of_one_lt_re hs).comp
        tendsto_two_mul_atTop
  exact tendsto_nhds_unique hfullEven
    (etaPartialEndpoint_two_mul_tendsto_analyticEta hs)

/-- Genuine eta partial sums converge to analytic eta for every `re s > 1`. -/
theorem etaPartialConvergesAt_of_one_lt_re_unconditional
    {s : ℂ} (hs : 1 < s.re) :
    EtaPartialConvergesAt s := by
  exact etaPartialConvergesAt_of_one_lt_re hs
    (etaTsumIdentifiesAnalyticAt_of_one_lt_re hs)

end DkMath.RH.Weave.Analytic
