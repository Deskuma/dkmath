/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaMirrorEndpointOuterNormalization

#print "file: DkMath.RH.CFBRC.EtaMirrorEndpointRegularizedLimits"

noncomputable section

namespace DkMath.RH.CFBRCProjection

/-!
# General regularized limits for eta mirror endpoint normalization

For a fixed finite endpoint stage, the regularized total share is the self-ratio
of `OuterBig + ε`.  Its unique collapsed offset is therefore
`ε = -OuterBig`.  Removing that offset gives unit value on both sides, without
changing Lean's ordinary pointwise division at the collapsed point.
-/

/-- Every offset other than the unique collapse offset gives unit total share. -/
theorem etaMirrorEndpointRegularizedTotalShare_eq_one_of_offset_ne_neg
    (N : ℕ) (s : ℂ) {ε : ℝ}
    (hε : ε ≠ -etaMirrorEndpointOuterBig N s) :
    etaMirrorEndpointRegularizedTotalShare N s ε = 1 := by
  exact DkMath.KUS.regularizedSelfRatio_eq_one_of_offset_ne_neg hε

/--
The regularized total share tends to one along the full punctured neighborhood
of its unique collapse offset.
-/
theorem tendsto_etaMirrorEndpointRegularizedTotalShare_punctured
    (N : ℕ) (s : ℂ) :
    Filter.Tendsto
      (fun ε : ℝ => etaMirrorEndpointRegularizedTotalShare N s ε)
      (nhdsWithin
        (-etaMirrorEndpointOuterBig N s)
        ({-etaMirrorEndpointOuterBig N s}ᶜ : Set ℝ))
      (nhds 1) := by
  simpa [etaMirrorEndpointRegularizedTotalShare] using
    DkMath.KUS.tendsto_regularizedSelfRatio_punctured
      (etaMirrorEndpointOuterBig N s)

/-- The right-hand path from the unique collapse offset has the same unit limit. -/
theorem tendsto_etaMirrorEndpointRegularizedTotalShare_right
    (N : ℕ) (s : ℂ) :
    Filter.Tendsto
      (fun ε : ℝ => etaMirrorEndpointRegularizedTotalShare N s ε)
      (nhdsWithin
        (-etaMirrorEndpointOuterBig N s)
        (Set.Ioi (-etaMirrorEndpointOuterBig N s)))
      (nhds 1) := by
  simpa [etaMirrorEndpointRegularizedTotalShare] using
    DkMath.KUS.tendsto_regularizedSelfRatio_right
      (etaMirrorEndpointOuterBig N s)

end DkMath.RH.CFBRCProjection
