/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.Weave.Analytic.EtaTermDecay
import Mathlib.Tactic

#print "file: DkMath.RH.Weave.Analytic.EtaAbsoluteConvergence"

namespace DkMath.RH.Weave.Analytic

open Filter
open scoped Topology
open DkMath.RH.CFBRCProjection

/-- The unsigned eta vectors are summable in the absolute-convergence half-plane. -/
theorem summable_etaUnsignedVector_of_one_lt_re
    {s : ℂ} (hs : 1 < s.re) :
    Summable (etaUnsignedVector s) := by
  have hfull :
      Summable (fun n : ℕ => 1 / ((n : ℂ) ^ s)) :=
    (Complex.summable_one_div_nat_cpow).2 hs
  have hinj : Function.Injective (fun m : ℕ => m + 1) := by
    intro a b hab
    omega
  have hshift :
      Summable (fun m : ℕ => 1 / ((((m + 1 : ℕ) : ℂ) ^ s))) := by
    simpa only [Function.comp_apply] using hfull.comp_injective hinj
  exact hshift.congr fun m => (etaUnsignedVector_eq_one_div_cpow s m).symm

/-- Alternating eta vectors are absolutely summable for `1 < re s`. -/
theorem summable_etaSignedVector_of_one_lt_re
    {s : ℂ} (hs : 1 < s.re) :
    Summable (etaSignedVector s) := by
  rw [← summable_norm_iff]
  have hUnsignedNorm :
      Summable (fun m : ℕ => ‖etaUnsignedVector s m‖) := by
    rw [summable_norm_iff]
    exact summable_etaUnsignedVector_of_one_lt_re hs
  exact hUnsignedNorm.congr fun m => (norm_etaSignedVector s m).symm

/--
In the absolute-convergence half-plane, finite eta endpoints converge to the
actual infinite signed eta sum.
-/
theorem etaPartialEndpoint_tendsto_tsum_of_one_lt_re
    {s : ℂ} (hs : 1 < s.re) :
    Tendsto (fun N : ℕ => etaPartialEndpoint N s)
      atTop (nhds (∑' m : ℕ, etaSignedVector s m)) := by
  have hsum := (summable_etaSignedVector_of_one_lt_re hs).hasSum.tendsto_sum_nat
  simpa [etaPartialEndpoint, finiteEndpoint] using hsum

/--
The only remaining value-level obligation in the absolute-convergence region:
the signed eta tsum must agree with the analytic eta expression.
-/
def EtaTsumIdentifiesAnalyticAt (s : ℂ) : Prop :=
  (∑' m : ℕ, etaSignedVector s m) = analyticEta s

/-- Absolute convergence plus value identification realizes eta convergence. -/
theorem etaPartialConvergesAt_of_one_lt_re
    {s : ℂ} (hs : 1 < s.re)
    (hidentify : EtaTsumIdentifiesAnalyticAt s) :
    EtaPartialConvergesAt s := by
  unfold EtaTsumIdentifiesAnalyticAt at hidentify
  unfold EtaPartialConvergesAt
  rw [← hidentify]
  exact etaPartialEndpoint_tendsto_tsum_of_one_lt_re hs

end DkMath.RH.Weave.Analytic
