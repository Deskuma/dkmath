/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaMirrorEndpointDefinedShares
import DkMath.RH.CFBRC.EtaMirrorEndpointRegularizedLimits

#print "file: DkMath.RH.CFBRC.EtaMirrorEndpointNormalizationState"

noncomputable section

namespace DkMath.RH.CFBRCProjection

/-!
# Complete normalization-state split for eta mirror endpoints

At every finite endpoint stage, exactly one of two mathematically meaningful
layers is available:

* the ordinary value layer, when `OuterBig ≠ 0`; or
* the collapsed layer, when `OuterBig = 0`.

The collapsed layer does not invent individual Core/Gap shares.  It keeps the
total structural share equal to one and records the punctured regularized
limits instead.
-/

/-- Data and laws available in the ordinary nonzero-denominator value layer. -/
structure EtaMirrorEndpointRegularNormalization
    (N : ℕ) (s : ℂ) : Prop where
  outer_ne : etaMirrorEndpointOuterBig N s ≠ 0
  core_defined : etaMirrorEndpointCoreShareDefined N s
  gap_defined : etaMirrorEndpointGapShareDefined N s
  core_nonneg : 0 ≤ etaMirrorEndpointCoreShare N s
  gap_nonneg : 0 ≤ etaMirrorEndpointGapShare N s
  shares_add_eq_one :
    etaMirrorEndpointCoreShare N s + etaMirrorEndpointGapShare N s = 1
  structural_eq_numeric :
    etaMirrorEndpointTotalStructuralShare N s =
      etaMirrorEndpointCoreShare N s + etaMirrorEndpointGapShare N s

/-- Data and laws available at a collapsed zero denominator. -/
structure EtaMirrorEndpointCollapsedNormalization
    (N : ℕ) (s : ℂ) : Prop where
  outer_eq_zero : etaMirrorEndpointOuterBig N s = 0
  core_not_defined : ¬ etaMirrorEndpointCoreShareDefined N s
  gap_not_defined : ¬ etaMirrorEndpointGapShareDefined N s
  total_structural_eq_one : etaMirrorEndpointTotalStructuralShare N s = 1
  punctured_limit :
    Filter.Tendsto
      (fun ε : ℝ => etaMirrorEndpointRegularizedTotalShare N s ε)
      (nhdsWithin 0 ({0}ᶜ : Set ℝ))
      (nhds 1)
  right_limit :
    Filter.Tendsto
      (fun ε : ℝ => etaMirrorEndpointRegularizedTotalShare N s ε)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds 1)

/-- A nonzero outer Big packages the complete ordinary normalization layer. -/
theorem etaMirrorEndpointRegularNormalization_of_outer_ne
    (N : ℕ) (s : ℂ)
    (hOuter : etaMirrorEndpointOuterBig N s ≠ 0) :
    EtaMirrorEndpointRegularNormalization N s := by
  have hOuterPos : 0 < etaMirrorEndpointOuterBig N s :=
    lt_of_le_of_ne
      (etaMirrorEndpointOuterBig_nonneg N s)
      (Ne.symm hOuter)
  have hSharesNonneg := etaMirrorEndpointShares_nonneg N s hOuterPos
  exact {
    outer_ne := hOuter
    core_defined := etaMirrorEndpointCoreShareDefined_of_outer_ne N s hOuter
    gap_defined := etaMirrorEndpointGapShareDefined_of_outer_ne N s hOuter
    core_nonneg := hSharesNonneg.1
    gap_nonneg := hSharesNonneg.2
    shares_add_eq_one := etaMirrorEndpointCoreShare_add_gapShare N s hOuter
    structural_eq_numeric :=
      etaMirrorEndpointTotalStructuralShare_eq_coreShare_add_gapShare N s hOuter
  }

/-- A zero outer Big packages the complete collapsed normalization layer. -/
theorem etaMirrorEndpointCollapsedNormalization_of_outer_eq_zero
    (N : ℕ) (s : ℂ)
    (hOuter : etaMirrorEndpointOuterBig N s = 0) :
    EtaMirrorEndpointCollapsedNormalization N s := by
  have hUndefined :=
    etaMirrorEndpointIndividualShares_not_defined_of_outer_eq_zero N s hOuter
  exact {
    outer_eq_zero := hOuter
    core_not_defined := hUndefined.1
    gap_not_defined := hUndefined.2
    total_structural_eq_one :=
      etaMirrorEndpointTotalStructuralShare_eq_one N s
    punctured_limit :=
      tendsto_etaMirrorEndpointRegularizedTotalShare_punctured_of_outer_eq_zero
        N s hOuter
    right_limit :=
      tendsto_etaMirrorEndpointRegularizedTotalShare_right_of_outer_eq_zero
        N s hOuter
  }

/--
Every finite eta mirror endpoint belongs to the ordinary normalization layer or
to the collapsed structural/regularized layer.
-/
theorem etaMirrorEndpointNormalizationState_complete
    (N : ℕ) (s : ℂ) :
    EtaMirrorEndpointRegularNormalization N s ∨
      EtaMirrorEndpointCollapsedNormalization N s := by
  by_cases hOuter : etaMirrorEndpointOuterBig N s ≠ 0
  · exact Or.inl
      (etaMirrorEndpointRegularNormalization_of_outer_ne N s hOuter)
  · have hOuterZero : etaMirrorEndpointOuterBig N s = 0 := by
      by_contra h
      exact hOuter h
    exact Or.inr
      (etaMirrorEndpointCollapsedNormalization_of_outer_eq_zero
        N s hOuterZero)

/-- The two normalization layers cannot hold simultaneously. -/
theorem etaMirrorEndpointNormalizationStates_disjoint
    (N : ℕ) (s : ℂ) :
    ¬ (EtaMirrorEndpointRegularNormalization N s ∧
      EtaMirrorEndpointCollapsedNormalization N s) := by
  rintro ⟨hRegular, hCollapsed⟩
  exact hRegular.outer_ne hCollapsed.outer_eq_zero

end DkMath.RH.CFBRCProjection
