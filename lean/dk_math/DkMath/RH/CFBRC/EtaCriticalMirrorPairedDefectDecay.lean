/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedPhaseProjection
import DkMath.RH.Weave.Analytic.EtaPairDerivative
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.EtaCriticalMirrorPairedDefectDecay"

noncomputable section

namespace DkMath.RH.CFBRCProjection

open DkMath.RH.Weave.Analytic

/-- One transported defect term is exactly mirror term minus original term. -/
theorem etaCriticalMirrorDefectTerm_eq_mirror_sub_original
    (s : ℂ) (m : ℕ) :
    etaCriticalMirrorDefectTerm s m =
      etaSignedVector (criticalMirror s) m - etaSignedVector s m := by
  rw [etaSignedVector_criticalMirror_eq_weight_mul]
  unfold etaCriticalMirrorDefectTerm
  ring

/--
One adjacent defect pair is exactly the eta pair at the critical mirror minus
the eta pair at the original point.
-/
theorem etaCriticalMirrorDefectPairTerm_eq_etaPairTerm_sub
    (s : ℂ) (k : ℕ) :
    etaCriticalMirrorDefectPairTerm s k =
      etaPairTerm (criticalMirror s) k - etaPairTerm s k := by
  rw [etaCriticalMirrorDefectPairTerm,
    etaCriticalMirrorDefectTerm_eq_mirror_sub_original,
    etaCriticalMirrorDefectTerm_eq_mirror_sub_original]
  simp [etaPairTerm]
  ring

/--
The finite paired defect is exactly mirror paired endpoint minus original
paired endpoint.
-/
theorem etaCriticalMirrorDefectPairedPartial_eq_etaPairedPartial_sub
    (K : ℕ) (s : ℂ) :
    etaCriticalMirrorDefectPairedPartial K s =
      etaPairedPartial K (criticalMirror s) - etaPairedPartial K s := by
  unfold etaCriticalMirrorDefectPairedPartial etaPairedPartial
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  exact etaCriticalMirrorDefectPairTerm_eq_etaPairTerm_sub s k

/--
General one-extra-decay estimate for one paired mirror defect.  It is the sum
of the existing eta-pair derivative bounds at the mirror and original points.
-/
theorem norm_etaCriticalMirrorDefectPairTerm_le_one_extra_decay
    {s : ℂ} (hs : 0 < s.re) (hm : 0 < (criticalMirror s).re)
    (k : ℕ) :
    ‖etaCriticalMirrorDefectPairTerm s k‖ ≤
      ‖criticalMirror s‖ *
          (((2 * k + 1 : ℕ) : ℝ) ^ (-(criticalMirror s).re - 1)) +
        ‖s‖ * (((2 * k + 1 : ℕ) : ℝ) ^ (-s.re - 1)) := by
  rw [etaCriticalMirrorDefectPairTerm_eq_etaPairTerm_sub]
  calc
    ‖etaPairTerm (criticalMirror s) k - etaPairTerm s k‖ ≤
        ‖etaPairTerm (criticalMirror s) k‖ + ‖etaPairTerm s k‖ :=
      norm_sub_le _ _
    _ ≤
        ‖criticalMirror s‖ *
            (((2 * k + 1 : ℕ) : ℝ) ^ (-(criticalMirror s).re - 1)) +
          ‖s‖ * (((2 * k + 1 : ℕ) : ℝ) ^ (-s.re - 1)) :=
      add_le_add
        (norm_etaPairTerm_le_one_extra_decay hm k)
        (norm_etaPairTerm_le_one_extra_decay hs k)

/--
At every nontrivial zeta zero, the paired mirror defect inherits one full
extra decay power on both sides of the critical mirror.
-/
theorem norm_etaCriticalMirrorDefectPairTerm_le_one_extra_decay_of_nontrivialRiemannZetaZero
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) (k : ℕ) :
    ‖etaCriticalMirrorDefectPairTerm s k‖ ≤
      ‖criticalMirror s‖ *
          (((2 * k + 1 : ℕ) : ℝ) ^ (-(criticalMirror s).re - 1)) +
        ‖s‖ * (((2 * k + 1 : ℕ) : ℝ) ^ (-s.re - 1)) := by
  exact
    norm_etaCriticalMirrorDefectPairTerm_le_one_extra_decay
      (nontrivialRiemannZetaZero_re_pos hs)
      (criticalMirror_re_pos_of_nontrivialRiemannZetaZero hs)
      k

end DkMath.RH.CFBRCProjection
