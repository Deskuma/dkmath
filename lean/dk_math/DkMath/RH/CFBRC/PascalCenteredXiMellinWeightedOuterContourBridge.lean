/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Analysis.MellinCompactSupportHolomorphic
import DkMath.RH.CFBRC.MellinCenteredMirrorAdapter
import DkMath.RH.CFBRC.PascalCenteredXiOuterContourResidueBridge
import Mathlib.Tactic

/-!
# Mellin spectral weights on the fixed centered-Xi contour

This is the XDP-005 Route C bridge.  Positive compact Mellin data produce the
globally differentiable centered weight from
`DkMath.Analysis.centeredMellinSpectralWeight`; the existing generic fixed-Xi
outer-contour residue theorem then applies without redoing principal parts,
removable patches, or Cauchy-Goursat arguments.

The endpoint is a representation theorem: the weighted fixed contour equals a
finite weighted centered-Xi zero-disk moment, with the normalized contour equal
to its negative.  It does not identify the weight with `z ^ 2`, realize a hard
radial cutoff, produce a prime-side formula, or prove a defect sign, defect
vanishing, or RH.  In particular, no finite interpolation is promoted to a
global zero-sum identity here.
-/

namespace DkMath.RH.CFBRCProjection

open DkMath.Analysis

/-- The Mellin spectral weight of positive compact-support data is admissible
for the generic fixed centered-Xi outer-contour residue theorem. -/
theorem pascalCenteredXiMellinWeightedOuterContourMass_eq
    {h : ℝ → ℂ} {a b R : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupp : Function.support h ⊆ Set.Icc a b)
    (hcont : ContinuousOn h (Set.Icc a b))
    (hR : IsPascalCenteredXiBoundarySafeRadius R) :
    pascalCenteredXiWeightedOuterContourMass
        (centeredMellinSpectralWeight h) R =
      -(2 * Real.pi * Complex.I) *
        pascalCenteredXiZeroDiskWeightedMoment
          (centeredMellinSpectralWeight h) R := by
  exact pascalCenteredXiWeightedOuterContourMass_eq
    (differentiable_centeredMellinSpectralWeight_of_support_subset_Icc_pos
      ha hab hsupp hcont) hR

/-- The normalized Mellin-weighted fixed-Xi contour is the negative finite
weighted centered-Xi zero-disk moment. -/
theorem pascalCenteredXiNormalizedMellinWeightedOuterContourMass_eq
    {h : ℝ → ℂ} {a b R : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupp : Function.support h ⊆ Set.Icc a b)
    (hcont : ContinuousOn h (Set.Icc a b))
    (hR : IsPascalCenteredXiBoundarySafeRadius R) :
    (2 * Real.pi * Complex.I)⁻¹ *
        pascalCenteredXiWeightedOuterContourMass
          (centeredMellinSpectralWeight h) R =
      -pascalCenteredXiZeroDiskWeightedMoment
        (centeredMellinSpectralWeight h) R := by
  exact pascalCenteredXiNormalizedWeightedOuterContourMass_eq
    (differentiable_centeredMellinSpectralWeight_of_support_subset_Icc_pos
      ha hab hsupp hcont) hR

end DkMath.RH.CFBRCProjection
