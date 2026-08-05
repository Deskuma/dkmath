/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameCompletedZetaSameTruncationOrbit
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameCompletedZetaFiniteEtaOrbitExpansion"

set_option linter.style.longLine false

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open ComplexConjugate
open scoped Topology
open DkMath.RH.Weave.Analytic

/-- Finite paired eta endpoints commute exactly with conjugation. -/
theorem etaPairedPartial_conj
    (K : ℕ) (s : ℂ) :
    etaPairedPartial K (conj s) = conj (etaPairedPartial K s) := by
  simp [etaPairedPartial, etaPairTerm_conj]

/--
The normalized even defect endpoint is exactly one index power times the
finite paired eta difference between the critical mirror and the original
point.
-/
theorem etaCriticalMirrorIndexNormalizedEvenDefectEndpoint_eq_indexPow_mul_etaPairedPartial_sub
    (a : ℝ) (s : ℂ) (k : ℕ) :
    etaCriticalMirrorIndexNormalizedEvenDefectEndpoint a s k =
      (((((k + 1 : ℕ) : ℝ)) ^ a : ℝ) : ℂ) *
        (etaPairedPartial (k + 1) (criticalMirror s) -
          etaPairedPartial (k + 1) s) := by
  unfold etaCriticalMirrorIndexNormalizedEvenDefectEndpoint
  rw [etaCriticalMirrorTransportDefectEndpoint_two_mul_eq_pairedPartial]
  rw [etaCriticalMirrorDefectPairedPartial_eq_etaPairedPartial_sub]

/-- The unscaled same-index finite paired eta defect. -/
noncomputable def etaCriticalMirrorFinitePairedEtaDefect
    (k : ℕ) (s : ℂ) : ℂ :=
  etaPairedPartial (k + 1) (criticalMirror s) -
    etaPairedPartial (k + 1) s

/-- Side-aware dominant index power used by the normalized endpoint carrier. -/
noncomputable def etaCriticalMirrorDominantIndexPower
    (k : ℕ) (s : ℂ) : ℂ :=
  if s.re ≤ (2 : ℝ)⁻¹ then
    (((((k + 1 : ℕ) : ℝ)) ^ s.re : ℝ) : ℂ)
  else
    (((((k + 1 : ℕ) : ℝ)) ^ (criticalMirror s).re : ℝ) : ℂ)

/-- The dominant endpoint written directly as a weighted finite eta defect. -/
noncomputable def etaCriticalMirrorDominantFiniteEtaCarrier
    (k : ℕ) (s : ℂ) : ℂ :=
  etaCriticalMirrorDominantIndexPower k s *
    etaCriticalMirrorFinitePairedEtaDefect k s

/--
The previously constructed dominant endpoint carrier is exactly the explicit
weighted finite eta carrier.
-/
theorem etaCriticalMirrorDominantNormalizedEndpointCarrier_eq_finiteEtaCarrier
    (k : ℕ) (s : ℂ) :
    etaCriticalMirrorDominantNormalizedEndpointCarrier k s =
      etaCriticalMirrorDominantFiniteEtaCarrier k s := by
  by_cases hside : s.re ≤ (2 : ℝ)⁻¹
  · have hside' : s.re ≤ (1 : ℝ) / 2 := by
      simpa using hside
    simp [etaCriticalMirrorDominantNormalizedEndpointCarrier,
      etaCriticalMirrorDominantFiniteEtaCarrier,
      etaCriticalMirrorDominantIndexPower,
      etaCriticalMirrorFinitePairedEtaDefect,
      hside, hside',
      etaCriticalMirrorIndexNormalizedEvenDefectEndpoint_eq_indexPow_mul_etaPairedPartial_sub]
  · have hside' : ¬ s.re ≤ (1 : ℝ) / 2 := by
      simpa using hside
    simp [etaCriticalMirrorDominantNormalizedEndpointCarrier,
      etaCriticalMirrorDominantFiniteEtaCarrier,
      etaCriticalMirrorDominantIndexPower,
      etaCriticalMirrorFinitePairedEtaDefect,
      hside, hside',
      etaCriticalMirrorIndexNormalizedEvenDefectEndpoint_eq_indexPow_mul_etaPairedPartial_sub]

/-- The dominant index power is unchanged by complex conjugation. -/
theorem etaCriticalMirrorDominantIndexPower_conj
    (k : ℕ) (s : ℂ) :
    etaCriticalMirrorDominantIndexPower k (conj s) =
      etaCriticalMirrorDominantIndexPower k s := by
  by_cases hside : s.re ≤ (2 : ℝ)⁻¹
  · have hsideConj : (conj s).re ≤ (2 : ℝ)⁻¹ := by
      simpa using hside
    simp [etaCriticalMirrorDominantIndexPower, hside, hsideConj,
      criticalMirror_conj]
  · have hsideConj : ¬ (conj s).re ≤ (2 : ℝ)⁻¹ := by
      simpa using hside
    simp [etaCriticalMirrorDominantIndexPower, hside, hsideConj,
      criticalMirror_conj]

/-- The finite paired eta defect commutes exactly with conjugation. -/
theorem etaCriticalMirrorFinitePairedEtaDefect_conj
    (k : ℕ) (s : ℂ) :
    etaCriticalMirrorFinitePairedEtaDefect k (conj s) =
      conj (etaCriticalMirrorFinitePairedEtaDefect k s) := by
  simp [etaCriticalMirrorFinitePairedEtaDefect,
    criticalMirror_conj, etaPairedPartial_conj]

/--
The explicit same-truncation finite eta orbit residual.  All four finite eta
partial sums use the same pair count `k + 1`.
-/
noncomputable def etaCriticalMirrorEndpointCompletedZetaFiniteEtaOrbitResidual
    (k : ℕ) (s : ℂ) : ℂ :=
  etaCriticalMirrorDominantFiniteEtaCarrier k s -
    completedZetaCanonicalSlopeProjectivePhase s *
      etaCriticalMirrorDominantFiniteEtaCarrier k (conj s)

/-- The abstract endpoint orbit residual is exactly the finite eta residual. -/
theorem etaCriticalMirrorEndpointCompletedZetaSameTruncationOrbitResidual_eq_finiteEtaOrbitResidual
    (k : ℕ) (s : ℂ) :
    etaCriticalMirrorEndpointCompletedZetaSameTruncationOrbitResidual k s =
      etaCriticalMirrorEndpointCompletedZetaFiniteEtaOrbitResidual k s := by
  simp [etaCriticalMirrorEndpointCompletedZetaSameTruncationOrbitResidual,
    etaCriticalMirrorEndpointCompletedZetaFiniteEtaOrbitResidual,
    etaCriticalMirrorDominantNormalizedEndpointCarrier_eq_finiteEtaCarrier]

/-- The unweighted finite eta orbit residual inside the dominant index power. -/
noncomputable def etaCriticalMirrorEndpointCompletedZetaUnweightedFiniteEtaOrbitResidual
    (k : ℕ) (s : ℂ) : ℂ :=
  etaCriticalMirrorFinitePairedEtaDefect k s -
    completedZetaCanonicalSlopeProjectivePhase s *
      etaCriticalMirrorFinitePairedEtaDefect k (conj s)

/-- The weighted finite eta residual factors by one common dominant index power. -/
theorem etaCriticalMirrorEndpointCompletedZetaFiniteEtaOrbitResidual_eq_indexPower_mul_unweighted
    (k : ℕ) (s : ℂ) :
    etaCriticalMirrorEndpointCompletedZetaFiniteEtaOrbitResidual k s =
      etaCriticalMirrorDominantIndexPower k s *
        etaCriticalMirrorEndpointCompletedZetaUnweightedFiniteEtaOrbitResidual k s := by
  unfold etaCriticalMirrorEndpointCompletedZetaFiniteEtaOrbitResidual
  unfold etaCriticalMirrorDominantFiniteEtaCarrier
  unfold etaCriticalMirrorEndpointCompletedZetaUnweightedFiniteEtaOrbitResidual
  rw [etaCriticalMirrorDominantIndexPower_conj]
  ring

/--
The unweighted residual is the completed-zeta phase residual of one finite eta
defect and its exact conjugate.
-/
theorem etaCriticalMirrorEndpointCompletedZetaUnweightedFiniteEtaOrbitResidual_eq_phaseResidual
    (k : ℕ) (s : ℂ) :
    etaCriticalMirrorEndpointCompletedZetaUnweightedFiniteEtaOrbitResidual k s =
      etaCriticalMirrorFinitePairedEtaDefect k s -
        completedZetaCanonicalSlopeProjectivePhase s *
          conj (etaCriticalMirrorFinitePairedEtaDefect k s) := by
  rw [etaCriticalMirrorEndpointCompletedZetaUnweightedFiniteEtaOrbitResidual]
  rw [etaCriticalMirrorFinitePairedEtaDefect_conj]

/--
Weighted finite eta orbit collapse: the final same-truncation obligation with
all endpoint definitions removed.
-/
def EtaCriticalMirrorEndpointCompletedZetaWeightedFiniteEtaOrbitResidualCollapse : Prop :=
  ∀ {s : ℂ},
    NontrivialRiemannZetaZero s →
    s.im ≠ 0 →
    Tendsto
      (fun k : ℕ =>
        etaCriticalMirrorDominantIndexPower k s *
          etaCriticalMirrorEndpointCompletedZetaUnweightedFiniteEtaOrbitResidual
            k s)
      atTop (nhds 0)

/-- The endpoint orbit condition is exactly the weighted finite eta condition. -/
theorem etaCriticalMirrorEndpointCompletedZetaSameTruncationOrbitResidualCollapse_iff_weightedFiniteEtaOrbitResidualCollapse :
    EtaCriticalMirrorEndpointCompletedZetaSameTruncationOrbitResidualCollapse ↔
      EtaCriticalMirrorEndpointCompletedZetaWeightedFiniteEtaOrbitResidualCollapse := by
  constructor
  · intro horbit s hs him
    have h := horbit hs him
    refine h.congr' (Eventually.of_forall fun k => ?_)
    rw [etaCriticalMirrorEndpointCompletedZetaSameTruncationOrbitResidual_eq_finiteEtaOrbitResidual]
    rw [etaCriticalMirrorEndpointCompletedZetaFiniteEtaOrbitResidual_eq_indexPower_mul_unweighted]
  · intro hfinite s hs him
    have h := hfinite hs him
    refine h.congr' (Eventually.of_forall fun k => ?_)
    rw [etaCriticalMirrorEndpointCompletedZetaSameTruncationOrbitResidual_eq_finiteEtaOrbitResidual]
    rw [etaCriticalMirrorEndpointCompletedZetaFiniteEtaOrbitResidual_eq_indexPower_mul_unweighted]

/-- RH follows from the fully expanded weighted finite eta orbit collapse. -/
theorem riemannHypothesis_of_endpointCompletedZetaWeightedFiniteEtaOrbitResidualCollapse
    (hfinite :
      EtaCriticalMirrorEndpointCompletedZetaWeightedFiniteEtaOrbitResidualCollapse) :
    RiemannHypothesis :=
  riemannHypothesis_of_endpointCompletedZetaSameTruncationOrbitResidualCollapse
    (etaCriticalMirrorEndpointCompletedZetaSameTruncationOrbitResidualCollapse_iff_weightedFiniteEtaOrbitResidualCollapse.mpr
      hfinite)

#print axioms etaCriticalMirrorIndexNormalizedEvenDefectEndpoint_eq_indexPow_mul_etaPairedPartial_sub
#print axioms etaCriticalMirrorDominantNormalizedEndpointCarrier_eq_finiteEtaCarrier
#print axioms etaCriticalMirrorEndpointCompletedZetaSameTruncationOrbitResidualCollapse_iff_weightedFiniteEtaOrbitResidualCollapse
#print axioms riemannHypothesis_of_endpointCompletedZetaWeightedFiniteEtaOrbitResidualCollapse

end DkMath.RH.CFBRCProjection
