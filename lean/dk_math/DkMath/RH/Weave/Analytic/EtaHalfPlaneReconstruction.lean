/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.Weave.Analytic.EtaZetaIdentification
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

#print "file: DkMath.RH.Weave.Analytic.EtaHalfPlaneReconstruction"

namespace DkMath.RH.Weave.Analytic

open Filter
open scoped Topology
open DkMath.RH.CFBRCProjection

/-- The positive real bases `(m + 1)` escape to `+∞`. -/
theorem tendsto_nat_succ_cast_atTop :
    Tendsto (fun m : ℕ => ((m + 1 : ℕ) : ℝ)) atTop atTop := by
  refine tendsto_atTop.2 ?_
  intro b
  obtain ⟨N, hN⟩ := exists_nat_ge b
  exact eventually_atTop.2 ⟨N, by
    intro n hn
    exact hN.trans (by
      exact_mod_cast Nat.le_trans hn (Nat.le_succ n))⟩

/--
Every unsigned eta vector tends to zero on the open right half-plane.
The imaginary coordinate remains in the phase; only its norm is projected to
`(m + 1)^(-re s)`.
-/
theorem etaUnsignedVector_tendsto_zero_of_pos_re
    {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun m : ℕ => etaUnsignedVector s m) atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hr := (Real.tendsto_rpow_neg_atTop hs).comp tendsto_nat_succ_cast_atTop
  simpa only [norm_etaUnsignedVector] using hr

/-- The even-indexed unsigned eta remainder also tends to zero. -/
theorem etaUnsignedVector_two_mul_tendsto_zero_of_pos_re
    {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun K : ℕ => etaUnsignedVector s (2 * K)) atTop (nhds 0) := by
  have hcomp :=
    (etaUnsignedVector_tendsto_zero_of_pos_re hs).comp tendsto_two_mul_atTop
  exact hcomp.congr' (Eventually.of_forall fun K => rfl)

/--
An odd-length eta endpoint is the paired partial sum plus its one unpaired
positive remainder.
-/
theorem etaPartialEndpoint_two_mul_add_one
    (K : ℕ) (s : ℂ) :
    etaPartialEndpoint (2 * K + 1) s =
      etaPairedPartial K s + etaUnsignedVector s (2 * K) := by
  rw [etaPartialEndpoint_succ]
  rw [etaPartialEndpoint_two_mul_eq_etaPairedPartial]
  simp

/-- Paired-difference summability at a selected complex coordinate. -/
def EtaPairedSummableAt (s : ℂ) : Prop :=
  Summable (etaPairTerm s)

/-- Paired finite sums converge to their actual infinite sum. -/
theorem etaPairedPartial_tendsto_tsum
    {s : ℂ} (hsum : EtaPairedSummableAt s) :
    Tendsto (fun K : ℕ => etaPairedPartial K s)
      atTop (nhds (∑' k : ℕ, etaPairTerm s k)) := by
  unfold EtaPairedSummableAt at hsum
  have h := hsum.hasSum.tendsto_sum_nat
  simpa [etaPairedPartial] using h

/-- Even eta endpoints inherit the paired-difference sum. -/
theorem etaPartialEndpoint_two_mul_tendsto_tsum
    {s : ℂ} (hsum : EtaPairedSummableAt s) :
    Tendsto (fun K : ℕ => etaPartialEndpoint (2 * K) s)
      atTop (nhds (∑' k : ℕ, etaPairTerm s k)) := by
  have h := etaPairedPartial_tendsto_tsum hsum
  refine h.congr' (Eventually.of_forall fun K => ?_)
  exact (etaPartialEndpoint_two_mul_eq_etaPairedPartial K s).symm

/--
On `re s > 0`, odd eta endpoints have the same paired-difference limit because
their single unpaired remainder tends to zero.
-/
theorem etaPartialEndpoint_two_mul_add_one_tendsto_tsum
    {s : ℂ} (hre : 0 < s.re) (hsum : EtaPairedSummableAt s) :
    Tendsto (fun K : ℕ => etaPartialEndpoint (2 * K + 1) s)
      atTop (nhds (∑' k : ℕ, etaPairTerm s k)) := by
  have hpair := etaPairedPartial_tendsto_tsum hsum
  have hrem := etaUnsignedVector_two_mul_tendsto_zero_of_pos_re hre
  have hadd := hpair.add hrem
  refine hadd.congr' (Eventually.of_forall fun K => ?_)
  exact (etaPartialEndpoint_two_mul_add_one K s).symm

end DkMath.RH.Weave.Analytic
