/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.Weave.Analytic.EtaPairDerivative
import DkMath.RH.Weave.Analytic.EtaHalfPlaneReconstruction
import Mathlib.Analysis.PSeries
import Mathlib.Tactic

#print "file: DkMath.RH.Weave.Analytic.EtaPairedSummability"

noncomputable section

namespace DkMath.RH.Weave.Analytic

open Filter
open scoped Topology

/--
The real majorant supplied by the one-extra-power derivative estimate is
summable everywhere on the open right half-plane.
-/
theorem summable_etaPairMajorant
    {s : ℂ} (hre : 0 < s.re) :
    Summable
      (fun k : ℕ =>
        ‖s‖ * (((k + 1 : ℕ) : ℝ) ^ (-s.re - 1))) := by
  have hp : 1 < s.re + 1 := by linarith
  have hbase :
      Summable (fun n : ℕ => (n : ℝ) ^ (-(s.re + 1))) := by
    simpa only [one_div, Real.rpow_neg (Nat.cast_nonneg _)] using
      (summable_one_div_rpow.2 hp)
  have hshift :
      Summable
        (fun k : ℕ => (((k + 1 : ℕ) : ℝ) ^ (-(s.re + 1)))) := by
    exact (summable_nat_add_iff 1).2 hbase
  have hmul := hshift.mul_left ‖s‖
  simpa [show -s.re - 1 = -(s.re + 1) by ring] using hmul

/--
The paired eta term is bounded by the shifted real p-series majorant.
-/
theorem norm_etaPairTerm_le_summableMajorant
    {s : ℂ} (hre : 0 < s.re) (k : ℕ) :
    ‖etaPairTerm s k‖ ≤
      ‖s‖ * (((k + 1 : ℕ) : ℝ) ^ (-s.re - 1)) := by
  calc
    ‖etaPairTerm s k‖ ≤
        ‖s‖ * (((2 * k + 1 : ℕ) : ℝ) ^ (-s.re - 1)) :=
      norm_etaPairTerm_le_one_extra_decay hre k
    _ ≤ ‖s‖ * (((k + 1 : ℕ) : ℝ) ^ (-s.re - 1)) := by
      have hExp : -s.re - 1 ≤ 0 := by linarith
      have hkpos : 0 < (((k + 1 : ℕ) : ℝ)) := by positivity
      have h2kpos : 0 < (((2 * k + 1 : ℕ) : ℝ)) := by positivity
      have hle :
          (((k + 1 : ℕ) : ℝ)) ≤ (((2 * k + 1 : ℕ) : ℝ)) := by
        exact_mod_cast (by omega : k + 1 ≤ 2 * k + 1)
      have hrpow :
          (((2 * k + 1 : ℕ) : ℝ) ^ (-s.re - 1)) ≤
            (((k + 1 : ℕ) : ℝ) ^ (-s.re - 1)) :=
        Real.antitoneOn_rpow_Ioi_of_exponent_nonpos hExp
          hkpos h2kpos hle
      exact mul_le_mul_of_nonneg_left hrpow (norm_nonneg s)

/--
The paired eta difference series is summable at every point of the open right
half-plane.
-/
theorem etaPairedSummableAt_of_pos_re
    {s : ℂ} (hre : 0 < s.re) :
    EtaPairedSummableAt s := by
  unfold EtaPairedSummableAt
  exact
    (summable_etaPairMajorant hre).of_norm_bounded
      (norm_etaPairTerm_le_summableMajorant hre)

/--
On the open right half-plane, the complete finite eta endpoint sequence
converges unconditionally to the paired infinite sum.
-/
theorem etaPartialEndpoint_tendsto_pairedTsum_of_pos_re
    {s : ℂ} (hre : 0 < s.re) :
    Tendsto (fun N : ℕ => etaPartialEndpoint N s)
      atTop (nhds (∑' k : ℕ, etaPairTerm s k)) := by
  exact etaPartialEndpoint_tendsto_tsum_of_pairedSummable
    hre (etaPairedSummableAt_of_pos_re hre)

/--
After summability has been discharged, analytic value identification is the
only remaining obligation for genuine eta convergence on `re s > 0`.
-/
theorem etaPartialConvergesAt_of_pos_re
    {s : ℂ} (hre : 0 < s.re)
    (hidentify : EtaPairedTsumIdentifiesAnalyticAt s) :
    EtaPartialConvergesAt s := by
  exact etaPartialConvergesAt_of_pairedSummable
    hre (etaPairedSummableAt_of_pos_re hre) hidentify

/--
On `re s > 0`, finite eta endpoints tend to zero exactly when the paired
infinite sum is zero.
-/
theorem etaPartialEndpoint_tendsto_zero_iff_pairedTsum_eq_zero_of_pos_re
    {s : ℂ} (hre : 0 < s.re) :
    Tendsto (fun N : ℕ => etaPartialEndpoint N s) atTop (nhds 0) ↔
      (∑' k : ℕ, etaPairTerm s k) = 0 := by
  exact etaPartialEndpoint_tendsto_zero_iff_pairedTsum_eq_zero
    hre (etaPairedSummableAt_of_pos_re hre)

end DkMath.RH.Weave.Analytic
