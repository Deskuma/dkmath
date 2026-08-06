/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameNormalizedDefectTailTwoScaleChord
import Mathlib.Tactic

set_option linter.style.longLine false

#print "file: DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameNormalizedDefectTailChordCollapseCriterion"

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open scoped Topology

/--
The minimal same-object zero-locus condition for the two-scale chord route:
both the half-density and full-density normalized-defect-tail chords collapse
to zero.
-/
def EtaCriticalMirrorTwoScaleNormalizedDefectTailChordCollapse
    (a : ℝ) (s : ℂ) : Prop :=
  Tendsto
      (etaPairHalfDensityBlockSchedule.scheduledNormalizedDefectTailChord a s)
      atTop (nhds 0) ∧
    Tendsto
      (etaPairFullDensityBlockSchedule.scheduledNormalizedDefectTailChord a s)
      atTop (nhds 0)

/--
A nontrivial two-scale chord certificate and simultaneous zero collapse are
incompatible.  This is the exact zero/nonzero collision on the same gauge-
invariant defect quantity.
-/
theorem not_etaCriticalMirrorTwoScaleNormalizedDefectTailChordCollapse_of_certificate
    {a : ℝ} {s C : ℂ}
    (cert :
      EtaCriticalMirrorTwoScaleNormalizedDefectTailChordCertificate a s C) :
    ¬ EtaCriticalMirrorTwoScaleNormalizedDefectTailChordCollapse a s := by
  intro hcollapse
  rcases hcollapse with ⟨hhalfZero, hfullZero⟩
  have hhalfEq :
      ‖C -
          etaPairHalfDensityBlockSchedule.scheduledBlockRotationLimit s * C‖ =
        0 :=
    tendsto_nhds_unique cert.halfDensityChord_tendsto hhalfZero
  have hfullEq :
      ‖C -
          etaPairFullDensityBlockSchedule.scheduledBlockRotationLimit s * C‖ =
        0 :=
    tendsto_nhds_unique cert.fullDensityChord_tendsto hfullZero
  rcases cert.at_least_one_chord_limit_ne_zero with hhalf | hfull
  · exact hhalf hhalfEq
  · exact hfull hfullEq

/--
Side-aware zero-locus provider.  On either off-critical side it asks for zero
collapse of the same dominant normalized-tail chords used by the nonzero
certificate.
-/
structure EtaCriticalMirrorZeroLocusTwoScaleChordCollapse
    (s : ℂ) : Prop where
  left_collapse :
    s.re < (1 : ℝ) / 2 →
      EtaCriticalMirrorTwoScaleNormalizedDefectTailChordCollapse s.re s
  right_collapse :
    (1 : ℝ) / 2 < s.re →
      EtaCriticalMirrorTwoScaleNormalizedDefectTailChordCollapse
        (criticalMirror s).re s

/--
A nonreal nontrivial zero satisfying the same-object two-scale chord collapse
must lie on the critical line.
-/
theorem re_eq_half_of_nontrivialRiemannZetaZero_of_twoScaleChordCollapse
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0)
    (hcollapse : EtaCriticalMirrorZeroLocusTwoScaleChordCollapse s) :
    s.re = (1 : ℝ) / 2 := by
  by_contra hre
  rcases lt_or_gt_of_ne hre with hleft | hright
  · have cert :=
      etaCriticalMirrorLeftTwoScaleNormalizedDefectTailChordCertificate_of_zero
        hs him hleft
    exact
      not_etaCriticalMirrorTwoScaleNormalizedDefectTailChordCollapse_of_certificate
        cert (hcollapse.left_collapse hleft)
  · have cert :=
      etaCriticalMirrorRightTwoScaleNormalizedDefectTailChordCertificate_of_zero
        hs him hright
    exact
      not_etaCriticalMirrorTwoScaleNormalizedDefectTailChordCollapse_of_certificate
        cert (hcollapse.right_collapse hright)

/--
The chord-collapse provider maps a nonreal nontrivial zero into CFBRC closure.
-/
theorem offCriticalCFBRC_eq_zero_of_nontrivialRiemannZetaZero_of_twoScaleChordCollapse
    {d : ℕ} (hd : 0 < d) {s : ℂ} (Θ : ℝ)
    (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0)
    (hcollapse : EtaCriticalMirrorZeroLocusTwoScaleChordCollapse s) :
    offCriticalCFBRC d s.re Θ = 0 := by
  apply (offCriticalCFBRC_eq_zero_iff_re_eq_half hd s.re Θ).2
  exact
    re_eq_half_of_nontrivialRiemannZetaZero_of_twoScaleChordCollapse
      hs him hcollapse

/--
Equivalently, a nonreal off-critical nontrivial zero cannot satisfy the
same-object two-scale chord-collapse provider.
-/
theorem not_etaCriticalMirrorZeroLocusTwoScaleChordCollapse_of_offCriticalZero
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : s.re ≠ (1 : ℝ) / 2) :
    ¬ EtaCriticalMirrorZeroLocusTwoScaleChordCollapse s := by
  intro hcollapse
  exact hre
    (re_eq_half_of_nontrivialRiemannZetaZero_of_twoScaleChordCollapse
      hs him hcollapse)

end DkMath.RH.CFBRCProjection
