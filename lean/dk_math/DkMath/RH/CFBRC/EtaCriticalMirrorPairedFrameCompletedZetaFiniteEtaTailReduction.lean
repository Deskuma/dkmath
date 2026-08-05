/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameCompletedZetaFiniteEtaOrbitExpansion
import DkMath.RH.CFBRC.EtaCriticalMirrorPairedTail
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameCompletedZetaFiniteEtaTailReduction"

set_option linter.style.longLine false

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open ComplexConjugate
open scoped Topology

/-- The explicit finite eta defect is exactly the existing paired defect partial sum. -/
theorem etaCriticalMirrorFinitePairedEtaDefect_eq_defectPairedPartial
    (k : ℕ) (s : ℂ) :
    etaCriticalMirrorFinitePairedEtaDefect k s =
      etaCriticalMirrorDefectPairedPartial (k + 1) s := by
  exact
    (etaCriticalMirrorDefectPairedPartial_eq_etaPairedPartial_sub
      (k + 1) s).symm

/--
At a nonreal nontrivial zero, the finite eta defect is exactly the negative of
the complete remaining defect tail beginning at the same pair index.
-/
theorem etaCriticalMirrorFinitePairedEtaDefect_eq_neg_tail_of_zero
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (k : ℕ) :
    etaCriticalMirrorFinitePairedEtaDefect k s =
      -etaCriticalMirrorDefectPairTail (k + 1) s := by
  rw [etaCriticalMirrorFinitePairedEtaDefect_eq_defectPairedPartial]
  exact
    etaCriticalMirrorDefectPairedPartial_eq_neg_tail_of_nontrivialRiemannZetaZero
      hs him (k + 1)

/--
The unweighted completed-zeta projective residual written only with the
complete paired defect tail.  The finite partial sum has disappeared entirely.
-/
noncomputable def etaCriticalMirrorEndpointCompletedZetaUnweightedTailOrbitResidual
    (k : ℕ) (s : ℂ) : ℂ :=
  -etaCriticalMirrorDefectPairTail (k + 1) s +
    completedZetaCanonicalSlopeProjectivePhase s *
      conj (etaCriticalMirrorDefectPairTail (k + 1) s)

/-- The finite eta residual is exactly the complete-tail residual on the zero locus. -/
theorem etaCriticalMirrorEndpointCompletedZetaUnweightedFiniteEtaOrbitResidual_eq_tailOrbitResidual_of_zero
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (k : ℕ) :
    etaCriticalMirrorEndpointCompletedZetaUnweightedFiniteEtaOrbitResidual k s =
      etaCriticalMirrorEndpointCompletedZetaUnweightedTailOrbitResidual k s := by
  rw [etaCriticalMirrorEndpointCompletedZetaUnweightedFiniteEtaOrbitResidual_eq_phaseResidual]
  rw [etaCriticalMirrorFinitePairedEtaDefect_eq_neg_tail_of_zero hs him]
  unfold etaCriticalMirrorEndpointCompletedZetaUnweightedTailOrbitResidual
  simp
  ring

/-- The dominant-weighted complete-tail projective residual. -/
noncomputable def etaCriticalMirrorEndpointCompletedZetaWeightedTailOrbitResidual
    (k : ℕ) (s : ℂ) : ℂ :=
  etaCriticalMirrorDominantIndexPower k s *
    etaCriticalMirrorEndpointCompletedZetaUnweightedTailOrbitResidual k s

/-- The weighted finite eta residual is exactly the weighted complete-tail residual. -/
theorem etaCriticalMirrorEndpointCompletedZetaWeightedFiniteEtaOrbitResidual_eq_tailOrbitResidual_of_zero
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (k : ℕ) :
    etaCriticalMirrorDominantIndexPower k s *
        etaCriticalMirrorEndpointCompletedZetaUnweightedFiniteEtaOrbitResidual k s =
      etaCriticalMirrorEndpointCompletedZetaWeightedTailOrbitResidual k s := by
  unfold etaCriticalMirrorEndpointCompletedZetaWeightedTailOrbitResidual
  rw [etaCriticalMirrorEndpointCompletedZetaUnweightedFiniteEtaOrbitResidual_eq_tailOrbitResidual_of_zero
    hs him]

/--
Complete-tail orbit collapse: the same final obligation, now expressed entirely
through the remaining paired defect tail and the fixed completed-zeta phase.
-/
def EtaCriticalMirrorEndpointCompletedZetaWeightedTailOrbitResidualCollapse : Prop :=
  ∀ {s : ℂ},
    NontrivialRiemannZetaZero s →
    s.im ≠ 0 →
    Tendsto
      (fun k : ℕ =>
        etaCriticalMirrorEndpointCompletedZetaWeightedTailOrbitResidual k s)
      atTop (nhds 0)

/-- The weighted finite eta condition and the complete-tail condition are equivalent. -/
theorem etaCriticalMirrorEndpointCompletedZetaWeightedFiniteEtaOrbitResidualCollapse_iff_weightedTailOrbitResidualCollapse :
    EtaCriticalMirrorEndpointCompletedZetaWeightedFiniteEtaOrbitResidualCollapse ↔
      EtaCriticalMirrorEndpointCompletedZetaWeightedTailOrbitResidualCollapse := by
  constructor
  · intro hfinite s hs him
    have h := hfinite hs him
    refine h.congr' (Eventually.of_forall fun k => ?_)
    exact
      etaCriticalMirrorEndpointCompletedZetaWeightedFiniteEtaOrbitResidual_eq_tailOrbitResidual_of_zero
        hs him k
  · intro htail s hs him
    have h := htail hs him
    refine h.congr' (Eventually.of_forall fun k => ?_)
    exact
      (etaCriticalMirrorEndpointCompletedZetaWeightedFiniteEtaOrbitResidual_eq_tailOrbitResidual_of_zero
        hs him k).symm

/-- RH follows from collapse of the dominant-weighted complete-tail projective residual. -/
theorem riemannHypothesis_of_endpointCompletedZetaWeightedTailOrbitResidualCollapse
    (htail :
      EtaCriticalMirrorEndpointCompletedZetaWeightedTailOrbitResidualCollapse) :
    RiemannHypothesis :=
  riemannHypothesis_of_endpointCompletedZetaWeightedFiniteEtaOrbitResidualCollapse
    (etaCriticalMirrorEndpointCompletedZetaWeightedFiniteEtaOrbitResidualCollapse_iff_weightedTailOrbitResidualCollapse.mpr
      htail)

#print axioms etaCriticalMirrorFinitePairedEtaDefect_eq_neg_tail_of_zero
#print axioms etaCriticalMirrorEndpointCompletedZetaWeightedFiniteEtaOrbitResidualCollapse_iff_weightedTailOrbitResidualCollapse
#print axioms riemannHypothesis_of_endpointCompletedZetaWeightedTailOrbitResidualCollapse

end DkMath.RH.CFBRCProjection
