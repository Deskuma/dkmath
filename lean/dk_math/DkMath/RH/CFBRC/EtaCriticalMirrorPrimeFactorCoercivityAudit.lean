/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPrimeFactorFiniteSourceBridge
import Mathlib.Tactic

/-!
# ZDI-006: P2-F coercivity and cancellation feasibility audit

This module records only the convergent consequence of the existing P2-F/Q2-F
bridge.  The prime-factor source is already exactly the old Eta defect partial,
so no coercivity or no-cancellation theorem is introduced here.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open scoped Topology

/--
The explicit Eta defect-tail power majorant tends to zero in the open mirror
strip.  This is a Q2-F rate statement only; it supplies no lower bound for
`centeredSigma`.
-/
theorem etaCriticalMirrorDefectPairTailPowerBound_tendsto_zero
    {s : ℂ} (hs : 0 < s.re) (hm : 0 < (criticalMirror s).re) :
    Tendsto
      (fun L : ℕ => etaCriticalMirrorDefectPairTailPowerBound s L)
      atTop (nhds 0) := by
  unfold etaCriticalMirrorDefectPairTailPowerBound
  have hnat : Tendsto (fun L : ℕ => (L : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hmirror := (tendsto_rpow_neg_atTop hm).comp hnat
  have horiginal := (tendsto_rpow_neg_atTop hs).comp hnat
  have hmirror' : Tendsto
      (fun L : ℕ =>
        ‖criticalMirror s‖ *
          (((L : ℝ) ^ (-(criticalMirror s).re)) /
            (criticalMirror s).re))
      atTop (nhds 0) := by
    simpa [div_eq_mul_inv, mul_assoc] using
      (tendsto_const_nhds.mul hmirror).mul
        (show Tendsto (fun _ : ℕ => ((criticalMirror s).re)⁻¹)
            atTop (nhds ((criticalMirror s).re)⁻¹) from
          tendsto_const_nhds)
  have horiginal' : Tendsto
      (fun L : ℕ =>
        ‖s‖ * (((L : ℝ) ^ (-s.re)) / s.re))
      atTop (nhds 0) := by
    simpa [div_eq_mul_inv, mul_assoc] using
      (tendsto_const_nhds.mul horiginal).mul
        (show Tendsto (fun _ : ℕ => (s.re)⁻¹)
            atTop (nhds s.re⁻¹) from
          tendsto_const_nhds)
  simpa using hmirror'.add horiginal'

/--
The existing Eta defect tail tends to zero at every standard nontrivial zero
with nonzero imaginary part.  The proof uses the established norm majorant and
does not turn convergence into a coercive estimate.
-/
theorem etaCriticalMirrorDefectPairTail_tendsto_zero_of_nontrivialRiemannZetaZero
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) :
    Tendsto
      (fun K : ℕ => etaCriticalMirrorDefectPairTail K s)
      atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hbound : ∀ᶠ K : ℕ in atTop,
      ‖etaCriticalMirrorDefectPairTail K s‖ ≤
        etaCriticalMirrorDefectPairTailPowerBound s K := by
    filter_upwards [eventually_atTop.2 ⟨1, fun K hK => hK⟩] with K hK
    exact norm_etaCriticalMirrorDefectPairTail_le_powerBound
      (nontrivialRiemannZetaZero_re_pos hs)
      (criticalMirror_re_pos_of_nontrivialRiemannZetaZero hs) hK
  exact
    tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds
      (etaCriticalMirrorDefectPairTailPowerBound_tendsto_zero
        (nontrivialRiemannZetaZero_re_pos hs)
        (criticalMirror_re_pos_of_nontrivialRiemannZetaZero hs))
      (Eventually.of_forall fun _ => norm_nonneg _)
      hbound

/--
The P2-F finite prime-factor source also tends to zero at a nonreal
nontrivial zero.  This is exactly the old Eta tail convergence transported
through the ZDI-005 equality, and therefore is not a coercivity result.
-/
theorem etaPrimeFactorMirrorDefectPairedPartial_tendsto_zero_of_nontrivialRiemannZetaZero
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) (him : s.im ≠ 0) :
    Tendsto
      (fun K : ℕ => etaPrimeFactorMirrorDefectPairedPartial K s)
      atTop (nhds 0) := by
  have htail :=
    etaCriticalMirrorDefectPairTail_tendsto_zero_of_nontrivialRiemannZetaZero
      hs
  have hsource :
      (fun K : ℕ => etaPrimeFactorMirrorDefectPairedPartial K s) =
        (fun K : ℕ => -etaCriticalMirrorDefectPairTail K s) := by
    funext K
    exact etaPrimeFactorMirrorDefectPairedPartial_eq_neg_tail_of_nontrivialRiemannZetaZero
      hs him K
  rw [hsource]
  simpa using htail.neg

end DkMath.RH.CFBRCProjection
