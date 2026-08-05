/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameBlockMarginDomination
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameFiniteBlockCertificate"

set_option linter.style.longLine false

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open scoped BigOperators

/--
Right of the critical line, all pair offsets in one fixed finite block are
eventually positive in the single frame chosen at the beginning of that block.
-/
theorem eventually_all_etaCriticalMirrorBlockStartDefectPairProjection_pos_on_range_of_half_lt_re
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : (1 : ℝ) / 2 < s.re)
    (N : ℕ) :
    ∀ᶠ K : ℕ in atTop,
      ∀ j : ℕ, j < N →
        0 < etaCriticalMirrorBlockStartDefectPairProjection s K j := by
  induction N with
  | zero => simp
  | succ N ih =>
      have hlast :=
        eventually_etaCriticalMirrorBlockStartDefectPairProjection_pos_of_half_lt_re
          hs him hre N
      filter_upwards [ih, hlast] with K hK hlastK
      intro j hj
      by_cases hjN : j < N
      · exact hK j hjN
      · have hEq : j = N := by omega
        simpa [hEq] using hlastK

/--
Left of the critical line, all pair offsets in one fixed finite block are
eventually negative in the single frame chosen at the beginning of that block.
-/
theorem eventually_all_etaCriticalMirrorBlockStartDefectPairProjection_neg_on_range_of_re_lt_half
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : s.re < (1 : ℝ) / 2)
    (N : ℕ) :
    ∀ᶠ K : ℕ in atTop,
      ∀ j : ℕ, j < N →
        etaCriticalMirrorBlockStartDefectPairProjection s K j < 0 := by
  induction N with
  | zero => simp
  | succ N ih =>
      have hlast :=
        eventually_etaCriticalMirrorBlockStartDefectPairProjection_neg_of_re_lt_half
          hs him hre N
      filter_upwards [ih, hlast] with K hK hlastK
      intro j hj
      by_cases hjN : j < N
      · exact hK j hjN
      · have hEq : j = N := by omega
        simpa [hEq] using hlastK

/-- Complex sum of one finite defect block viewed in its initial pair frame. -/
noncomputable def etaCriticalMirrorBlockStartRotatedDefectBlockTerm
    (s : ℂ) (K N : ℕ) : ℂ :=
  (Finset.range N).sum fun j : ℕ =>
    etaCriticalMirrorBlockStartRotatedDefectPairTerm s K j

/-- Signed vertical projection of the preceding common-frame defect block. -/
noncomputable def etaCriticalMirrorBlockStartDefectBlockProjection
    (s : ℂ) (K N : ℕ) : ℝ :=
  etaCriticalMirrorSignedVerticalProjection s
    (etaCriticalMirrorBlockStartRotatedDefectBlockTerm s K N)

/--
Projection of a common-frame finite block is the sum of the projections of all
of its pair terms.
-/
theorem etaCriticalMirrorBlockStartDefectBlockProjection_eq_sum
    (s : ℂ) (K N : ℕ) :
    etaCriticalMirrorBlockStartDefectBlockProjection s K N =
      (Finset.range N).sum fun j : ℕ =>
        etaCriticalMirrorBlockStartDefectPairProjection s K j := by
  unfold etaCriticalMirrorBlockStartDefectBlockProjection
  unfold etaCriticalMirrorBlockStartRotatedDefectBlockTerm
  unfold etaCriticalMirrorBlockStartDefectPairProjection
  unfold etaCriticalMirrorSignedVerticalProjection
  simp [Finset.mul_sum]

/--
Every nonempty fixed-length late block has strictly positive total projection
in its own single initial frame, right of the critical line.
-/
theorem eventually_etaCriticalMirrorBlockStartDefectBlockProjection_pos_of_half_lt_re
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : (1 : ℝ) / 2 < s.re)
    {N : ℕ} (hN : 0 < N) :
    ∀ᶠ K : ℕ in atTop,
      0 < etaCriticalMirrorBlockStartDefectBlockProjection s K N := by
  induction N with
  | zero => omega
  | succ N ih =>
      by_cases hzero : N = 0
      · subst N
        have hfirst :=
          eventually_etaCriticalMirrorBlockStartDefectPairProjection_pos_of_half_lt_re
            hs him hre 0
        filter_upwards [hfirst] with K hfirstK
        rw [etaCriticalMirrorBlockStartDefectBlockProjection_eq_sum]
        simpa using hfirstK
      · have hprev :
          ∀ᶠ K : ℕ in atTop,
            0 < etaCriticalMirrorBlockStartDefectBlockProjection s K N :=
          ih (Nat.pos_of_ne_zero hzero)
        have hlast :=
          eventually_etaCriticalMirrorBlockStartDefectPairProjection_pos_of_half_lt_re
            hs him hre N
        filter_upwards [hprev, hlast] with K hprevK hlastK
        rw [etaCriticalMirrorBlockStartDefectBlockProjection_eq_sum] at hprevK ⊢
        rw [Finset.sum_range_succ]
        exact add_pos hprevK hlastK

/--
Every nonempty fixed-length late block has strictly negative total projection
in its own single initial frame, left of the critical line.
-/
theorem eventually_etaCriticalMirrorBlockStartDefectBlockProjection_neg_of_re_lt_half
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : s.re < (1 : ℝ) / 2)
    {N : ℕ} (hN : 0 < N) :
    ∀ᶠ K : ℕ in atTop,
      etaCriticalMirrorBlockStartDefectBlockProjection s K N < 0 := by
  induction N with
  | zero => omega
  | succ N ih =>
      by_cases hzero : N = 0
      · subst N
        have hfirst :=
          eventually_etaCriticalMirrorBlockStartDefectPairProjection_neg_of_re_lt_half
            hs him hre 0
        filter_upwards [hfirst] with K hfirstK
        rw [etaCriticalMirrorBlockStartDefectBlockProjection_eq_sum]
        simpa using hfirstK
      · have hprev :
          ∀ᶠ K : ℕ in atTop,
            etaCriticalMirrorBlockStartDefectBlockProjection s K N < 0 :=
          ih (Nat.pos_of_ne_zero hzero)
        have hlast :=
          eventually_etaCriticalMirrorBlockStartDefectPairProjection_neg_of_re_lt_half
            hs him hre N
        filter_upwards [hprev, hlast] with K hprevK hlastK
        rw [etaCriticalMirrorBlockStartDefectBlockProjection_eq_sum] at hprevK ⊢
        rw [Finset.sum_range_succ]
        exact add_neg hprevK hlastK

end DkMath.RH.CFBRCProjection
