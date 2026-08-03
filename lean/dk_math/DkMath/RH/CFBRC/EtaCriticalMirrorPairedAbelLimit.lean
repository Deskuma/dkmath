/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedAbelCorrection
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.EtaCriticalMirrorPairedAbelLimit"

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open scoped Topology

/-- The successor map on natural indices is cofinal at `atTop`. -/
theorem tendsto_nat_succ_atTop :
    Tendsto (fun K : ℕ => K + 1) atTop atTop := by
  refine tendsto_atTop.2 ?_
  intro n
  exact eventually_atTop.2 ⟨n, by
    intro K hK
    omega⟩

/--
At a nonreal nontrivial zero, the Abel boundary term tends to zero because its
rotation has unit norm and the ordinary paired defect partial sum tends to
zero.
-/
theorem etaCriticalMirrorPairedAbelBoundaryTerm_tendsto_zero_of_nontrivialRiemannZetaZero
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) (him : s.im ≠ 0) :
    Tendsto
      (fun K : ℕ => etaCriticalMirrorPairedAbelBoundaryTerm K s)
      atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hpartial :=
    etaCriticalMirrorDefectPairedPartial_tendsto_zero_of_nontrivialRiemannZetaZero
      hs him
  rw [tendsto_zero_iff_norm_tendsto_zero] at hpartial
  simpa only [norm_etaCriticalMirrorPairedAbelBoundaryTerm] using hpartial

/-- The successor-indexed Abel boundary term also tends to zero. -/
theorem etaCriticalMirrorPairedAbelBoundaryTerm_succ_tendsto_zero_of_nontrivialRiemannZetaZero
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) (him : s.im ≠ 0) :
    Tendsto
      (fun K : ℕ => etaCriticalMirrorPairedAbelBoundaryTerm (K + 1) s)
      atTop (nhds 0) :=
  (etaCriticalMirrorPairedAbelBoundaryTerm_tendsto_zero_of_nontrivialRiemannZetaZero
    hs him).comp tendsto_nat_succ_atTop

/-- Finite correction sums converge to the complete Abel correction `tsum`. -/
theorem etaCriticalMirrorPairedFrameCorrectionPartial_tendsto_tsum_of_nontrivialRiemannZetaZero
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) (him : s.im ≠ 0) :
    Tendsto
      (fun K : ℕ =>
        (Finset.range K).sum
          (etaCriticalMirrorPairedFrameCorrectionTerm s))
      atTop
      (nhds
        (∑' k : ℕ,
          etaCriticalMirrorPairedFrameCorrectionTerm s k)) := by
  have hsum :=
    summable_etaCriticalMirrorPairedFrameCorrectionTerm_of_nontrivialRiemannZetaZero
      hs him
  simpa using hsum.hasSum.tendsto_sum_nat

/--
Exact moving-frame limit at every nonreal nontrivial zero.

The terminal Abel boundary vanishes and the absolutely summable frame-motion
correction remains.  Thus the successor-indexed moving-frame paired defect
partial sums converge to the negative correction `tsum`.
-/
theorem etaCriticalMirrorRotatedDefectPairedPartial_succ_tendsto_neg_correction_tsum
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) (him : s.im ≠ 0) :
    Tendsto
      (fun K : ℕ =>
        etaCriticalMirrorRotatedDefectPairedPartial (K + 1) s)
      atTop
      (nhds
        (-(∑' k : ℕ,
          etaCriticalMirrorPairedFrameCorrectionTerm s k))) := by
  have hboundary :=
    etaCriticalMirrorPairedAbelBoundaryTerm_succ_tendsto_zero_of_nontrivialRiemannZetaZero
      hs him
  have hcorrection :=
    etaCriticalMirrorPairedFrameCorrectionPartial_tendsto_tsum_of_nontrivialRiemannZetaZero
      hs him
  have hlimit := hboundary.sub hcorrection
  have hlimit' :
      Tendsto
        (fun K : ℕ =>
          etaCriticalMirrorPairedAbelBoundaryTerm (K + 1) s -
            (Finset.range K).sum
              (etaCriticalMirrorPairedFrameCorrectionTerm s))
        atTop
        (nhds
          (-(∑' k : ℕ,
            etaCriticalMirrorPairedFrameCorrectionTerm s k))) := by
    simpa using hlimit
  refine hlimit'.congr' (Eventually.of_forall fun K => ?_)
  simpa using
    (etaCriticalMirrorRotatedDefectPairedPartial_eq_abel (K + 1) s).symm

end DkMath.RH.CFBRCProjection
