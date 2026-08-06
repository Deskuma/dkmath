/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedAbelTransform
import DkMath.RH.Weave.Analytic.EtaPairedSummability
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.EtaCriticalMirrorPairedTail"

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open scoped Topology
open DkMath.RH.Weave.Analytic

/-- The paired critical-mirror defect series is summable in the open mirror strip. -/
theorem summable_etaCriticalMirrorDefectPairTerm
    {s : ℂ} (hs : 0 < s.re) (hm : 0 < (criticalMirror s).re) :
    Summable (etaCriticalMirrorDefectPairTerm s) := by
  have hMirror : Summable (etaPairTerm (criticalMirror s)) := by
    exact etaPairedSummableAt_of_pos_re hm
  have hOriginal : Summable (etaPairTerm s) := by
    exact etaPairedSummableAt_of_pos_re hs
  rw [show etaCriticalMirrorDefectPairTerm s =
      fun k : ℕ =>
        etaPairTerm (criticalMirror s) k - etaPairTerm s k by
    funext k
    exact etaCriticalMirrorDefectPairTerm_eq_etaPairTerm_sub s k]
  exact hMirror.sub hOriginal

/-- Every nontrivial zeta zero has a summable paired critical-mirror defect series. -/
theorem summable_etaCriticalMirrorDefectPairTerm_of_nontrivialRiemannZetaZero
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) :
    Summable (etaCriticalMirrorDefectPairTerm s) :=
  summable_etaCriticalMirrorDefectPairTerm
    (nontrivialRiemannZetaZero_re_pos hs)
    (criticalMirror_re_pos_of_nontrivialRiemannZetaZero hs)

/-- Tail of the paired critical-mirror defect series beginning at pair index `K`. -/
noncomputable def etaCriticalMirrorDefectPairTail
    (K : ℕ) (s : ℂ) : ℂ :=
  ∑' j : ℕ, etaCriticalMirrorDefectPairTerm s (j + K)

/-- A finite paired defect partial sum plus its tail equals the complete defect `tsum`. -/
theorem etaCriticalMirrorDefectPairedPartial_add_tail_eq_tsum
    {s : ℂ} (hsum : Summable (etaCriticalMirrorDefectPairTerm s))
    (K : ℕ) :
    etaCriticalMirrorDefectPairedPartial K s +
        etaCriticalMirrorDefectPairTail K s =
      ∑' k : ℕ, etaCriticalMirrorDefectPairTerm s k := by
  simpa [etaCriticalMirrorDefectPairedPartial,
    etaCriticalMirrorDefectPairTail] using
    hsum.sum_add_tsum_nat_add K

/-- At a nonreal nontrivial zero, the complex paired defect partial sums tend to zero. -/
theorem etaCriticalMirrorDefectPairedPartial_tendsto_zero_of_nontrivialRiemannZetaZero
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) (him : s.im ≠ 0) :
    Tendsto
      (fun K : ℕ => etaCriticalMirrorDefectPairedPartial K s)
      atTop (nhds 0) := by
  have heven :=
    (etaCriticalMirrorTransportDefectEndpoint_tendsto_zero_of_nontrivialRiemannZetaZero
      hs him).comp tendsto_two_mul_atTop
  refine heven.congr' (Eventually.of_forall fun K => ?_)
  exact
    etaCriticalMirrorTransportDefectEndpoint_two_mul_eq_pairedPartial K s

/-- At a nonreal nontrivial zero, the complete paired defect `tsum` is zero. -/
theorem tsum_etaCriticalMirrorDefectPairTerm_eq_zero_of_nontrivialRiemannZetaZero
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) (him : s.im ≠ 0) :
    (∑' k : ℕ, etaCriticalMirrorDefectPairTerm s k) = 0 := by
  have hsum :=
    summable_etaCriticalMirrorDefectPairTerm_of_nontrivialRiemannZetaZero hs
  have htsum :
      Tendsto
        (fun K : ℕ => etaCriticalMirrorDefectPairedPartial K s)
        atTop
        (nhds (∑' k : ℕ, etaCriticalMirrorDefectPairTerm s k)) := by
    simpa [etaCriticalMirrorDefectPairedPartial] using
      hsum.hasSum.tendsto_sum_nat
  exact
    tendsto_nhds_unique htsum
      (etaCriticalMirrorDefectPairedPartial_tendsto_zero_of_nontrivialRiemannZetaZero
        hs him)

/--
At a nonreal nontrivial zero, every paired defect partial sum is exactly the
negative of the remaining tail.  This is the form needed in the Abel
correction estimate.
-/
theorem etaCriticalMirrorDefectPairedPartial_eq_neg_tail_of_nontrivialRiemannZetaZero
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) (him : s.im ≠ 0)
    (K : ℕ) :
    etaCriticalMirrorDefectPairedPartial K s =
      -etaCriticalMirrorDefectPairTail K s := by
  have hsum :=
    summable_etaCriticalMirrorDefectPairTerm_of_nontrivialRiemannZetaZero hs
  have hsplit :=
    etaCriticalMirrorDefectPairedPartial_add_tail_eq_tsum hsum K
  rw [tsum_etaCriticalMirrorDefectPairTerm_eq_zero_of_nontrivialRiemannZetaZero
    hs him] at hsplit
  linear_combination hsplit

end DkMath.RH.CFBRCProjection
