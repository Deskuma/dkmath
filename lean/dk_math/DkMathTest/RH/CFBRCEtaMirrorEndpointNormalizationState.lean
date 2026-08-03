/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaMirrorEndpointNormalizationState

#print "file: DkMathTest.RH.CFBRCEtaMirrorEndpointNormalizationState"

noncomputable section

namespace DkMathTest.RH.CFBRCEtaMirrorEndpointNormalizationState

open DkMath.RH.CFBRCProjection

example (N : ℕ) (s : ℂ) :
    EtaMirrorEndpointRegularNormalization N s ∨
      EtaMirrorEndpointCollapsedNormalization N s := by
  exact etaMirrorEndpointNormalizationState_complete N s

example (N : ℕ) (s : ℂ)
    (hOuter : etaMirrorEndpointOuterBig N s ≠ 0) :
    EtaMirrorEndpointRegularNormalization N s := by
  exact etaMirrorEndpointRegularNormalization_of_outer_ne N s hOuter

example (N : ℕ) (s : ℂ)
    (hOuter : etaMirrorEndpointOuterBig N s = 0) :
    EtaMirrorEndpointCollapsedNormalization N s := by
  exact etaMirrorEndpointCollapsedNormalization_of_outer_eq_zero N s hOuter

example (N : ℕ) (s : ℂ) :
    ¬ (EtaMirrorEndpointRegularNormalization N s ∧
      EtaMirrorEndpointCollapsedNormalization N s) := by
  exact etaMirrorEndpointNormalizationStates_disjoint N s

example (N : ℕ) (s : ℂ)
    (h : EtaMirrorEndpointRegularNormalization N s) :
    0 ≤ etaMirrorEndpointCoreShare N s ∧
      0 ≤ etaMirrorEndpointGapShare N s ∧
      etaMirrorEndpointCoreShare N s + etaMirrorEndpointGapShare N s = 1 := by
  exact ⟨h.core_nonneg, h.gap_nonneg, h.shares_add_eq_one⟩

example (N : ℕ) (s : ℂ)
    (h : EtaMirrorEndpointCollapsedNormalization N s) :
    ¬ etaMirrorEndpointCoreShareDefined N s ∧
      ¬ etaMirrorEndpointGapShareDefined N s ∧
      etaMirrorEndpointTotalStructuralShare N s = 1 := by
  exact ⟨h.core_not_defined, h.gap_not_defined, h.total_structural_eq_one⟩

end DkMathTest.RH.CFBRCEtaMirrorEndpointNormalizationState
