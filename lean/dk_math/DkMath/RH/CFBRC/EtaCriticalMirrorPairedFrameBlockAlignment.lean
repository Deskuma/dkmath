/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameGaugeAudit
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameBlockAlignment"

set_option linter.style.longLine false

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open scoped BigOperators Topology

/-- Adding a fixed natural offset remains cofinal at `atTop`. -/
private theorem tendsto_nat_add_const_atTop
    (N : ℕ) :
    Tendsto (fun K : ℕ => K + N) atTop atTop := by
  refine tendsto_atTop.2 ?_
  intro n
  exact eventually_atTop.2 ⟨n, by
    intro K hK
    omega⟩

/--
The signed frame phase accumulated across the finite block
`K, ..., K + N - 1` telescopes to the endpoint log difference.
-/
theorem sum_range_etaPairFrameStepPhase_nat_add
    (s : ℂ) (K N : ℕ) :
    (Finset.range N).sum
        (fun j : ℕ => etaPairFrameStepPhase s (K + j)) =
      s.im *
        (Real.log (etaPairFrameLeftEndpoint (K + N)) -
          Real.log (etaPairFrameLeftEndpoint K)) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      unfold etaPairFrameStepPhase
      simp only [Nat.succ_eq_add_one, Nat.add_assoc]
      ring

/--
The total absolute frame variation across a finite block also telescopes to
its endpoint log difference.
-/
theorem sum_range_etaPairFrameStepSpan_nat_add
    (s : ℂ) (K N : ℕ) :
    (Finset.range N).sum
        (fun j : ℕ => etaPairFrameStepSpan s (K + j)) =
      |s.im| *
        (Real.log (etaPairFrameLeftEndpoint (K + N)) -
          Real.log (etaPairFrameLeftEndpoint K)) := by
  induction N with
  | zero => simp
  | succ N ih =>
      have ha : 0 < etaPairFrameLeftEndpoint (K + N) :=
        etaPairFrameLeftEndpoint_pos (K + N)
      have hb : 0 < etaPairFrameLeftEndpoint (K + N + 1) :=
        etaPairFrameLeftEndpoint_pos (K + N + 1)
      rw [Finset.sum_range_succ, ih]
      unfold etaPairFrameStepSpan
      rw [Real.log_div hb.ne' ha.ne']
      simp only [Nat.succ_eq_add_one, Nat.add_assoc]
      ring

/-- Total adjacent-frame variation across a finite block. -/
noncomputable def etaPairFrameBlockSpan
    (s : ℂ) (K N : ℕ) : ℝ :=
  (Finset.range N).sum
    (fun j : ℕ => etaPairFrameStepSpan s (K + j))

/-- The finite block span is the endpoint logarithmic phase width. -/
theorem etaPairFrameBlockSpan_eq
    (s : ℂ) (K N : ℕ) :
    etaPairFrameBlockSpan s K N =
      |s.im| *
        (Real.log (etaPairFrameLeftEndpoint (K + N)) -
          Real.log (etaPairFrameLeftEndpoint K)) := by
  exact sum_range_etaPairFrameStepSpan_nat_add s K N

/-- Every finite block span is nonnegative. -/
theorem etaPairFrameBlockSpan_nonneg
    (s : ℂ) (K N : ℕ) :
    0 ≤ etaPairFrameBlockSpan s K N := by
  unfold etaPairFrameBlockSpan
  exact Finset.sum_nonneg fun j hj =>
    etaPairFrameStepSpan_nonneg s (K + j)

/--
For every fixed block length, the total frame variation in that block tends to
zero as the block is moved to infinity.
-/
theorem etaPairFrameBlockSpan_tendsto_zero
    (s : ℂ) (N : ℕ) :
    Tendsto
      (fun K : ℕ => etaPairFrameBlockSpan s K N)
      atTop (nhds 0) := by
  induction N with
  | zero =>
      simp [etaPairFrameBlockSpan]
  | succ N ih =>
      have hlast :
          Tendsto
            (fun K : ℕ => etaPairFrameStepSpan s (K + N))
            atTop (nhds 0) :=
        (etaPairFrameStepSpan_tendsto_zero s).comp
          (tendsto_nat_add_const_atTop N)
      have hadd := ih.add hlast
      simpa [etaPairFrameBlockSpan, Finset.sum_range_succ,
        Nat.add_assoc] using hadd

/--
Every fixed-length late block eventually fits inside one half-plane angular
window.
-/
theorem eventually_etaPairFrameBlockSpan_lt_pi_div_two
    (s : ℂ) (N : ℕ) :
    ∀ᶠ K : ℕ in atTop,
      etaPairFrameBlockSpan s K N < Real.pi / 2 :=
  (etaPairFrameBlockSpan_tendsto_zero s N).eventually_lt_const
    (by positivity)

/--
Exact relation between the frame at the beginning and the frame at the end of
a finite block.
-/
theorem etaPairBaseRotation_add_eq
    (s : ℂ) (K N : ℕ) :
    etaPairBaseRotation s (K + N) =
      etaPairBaseRotation s K *
        Complex.exp
          (Complex.I *
            ((((Finset.range N).sum
              (fun j : ℕ => etaPairFrameStepPhase s (K + j)) : ℝ) : ℂ)) := by
  rw [etaPairBaseRotation, etaPairBaseRotation, ← Complex.exp_add]
  congr 1
  rw [sum_range_etaPairFrameStepPhase_nat_add]
  push_cast
  ring

/-- Relative unit rotation across a finite pair-frame block. -/
noncomputable def etaPairFrameBlockRotation
    (s : ℂ) (K N : ℕ) : ℂ :=
  (etaPairBaseRotation s K)⁻¹ *
    etaPairBaseRotation s (K + N)

/-- The block-relative rotation is exactly the exponential of the block phase. -/
theorem etaPairFrameBlockRotation_eq_exp
    (s : ℂ) (K N : ℕ) :
    etaPairFrameBlockRotation s K N =
      Complex.exp
        (Complex.I *
          ((((Finset.range N).sum
            (fun j : ℕ => etaPairFrameStepPhase s (K + j)) : ℝ) : ℂ)) := by
  unfold etaPairFrameBlockRotation
  rw [etaPairBaseRotation_add_eq]
  rw [← mul_assoc,
    inv_mul_cancel₀ (etaPairBaseRotation_ne_zero s K), one_mul]

/-- Every finite block-relative frame rotation has unit norm. -/
theorem norm_etaPairFrameBlockRotation
    (s : ℂ) (K N : ℕ) :
    ‖etaPairFrameBlockRotation s K N‖ = 1 := by
  rw [etaPairFrameBlockRotation_eq_exp, Complex.norm_exp]
  simp

end DkMath.RH.CFBRCProjection
