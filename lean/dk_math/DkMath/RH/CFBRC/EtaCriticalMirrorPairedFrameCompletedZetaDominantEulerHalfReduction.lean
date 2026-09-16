/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameCompletedZetaEulerMainLineReduction
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameCompletedZetaDominantEulerHalfReduction"

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open scoped Topology

/-- One Euler half-endpoint with an arbitrary real successor-index exponent. -/
noncomputable def etaPairIndexScaledEulerHalfEndpoint
    (a : ℝ) (z : ℂ) (k : ℕ) : ℂ :=
  (((((k + 1 : ℕ) : ℝ)) ^ a : ℝ) : ℂ) *
    (((1 : ℂ) / 2) * etaUnsignedVector z (2 * (k + 1)))

/-- Exact norm of one unsigned eta vector. -/
theorem norm_etaUnsignedVector
    (z : ℂ) (m : ℕ) :
    ‖etaUnsignedVector z m‖ =
      (((m + 1 : ℕ) : ℝ) ^ (-z.re)) := by
  unfold etaUnsignedVector
  rw [← Complex.ofReal_natCast]
  rw [Complex.norm_cpow_eq_rpow_re_of_pos]
  · simp
  · exact_mod_cast Nat.succ_pos m

/--
A half-endpoint normalized by a strictly weaker exponent is bounded by one
negative real power of the successor index.
-/
theorem norm_etaPairIndexScaledEulerHalfEndpoint_le_decay
    {a : ℝ} {z : ℂ} (hzre : 0 < z.re) (_ha : a < z.re) (k : ℕ) :
    ‖etaPairIndexScaledEulerHalfEndpoint a z k‖ ≤
      ((1 : ℝ) / 2) *
        ((((k + 1 : ℕ) : ℝ)) ^ (a - z.re)) := by
  let n : ℝ := (((k + 1 : ℕ) : ℝ))
  let m : ℝ := (((2 * (k + 1) + 1 : ℕ) : ℝ))
  have hn : 0 < n := by
    dsimp [n]
    positivity
  have hm : 0 < m := by
    dsimp [m]
    positivity
  have hnm : n ≤ m := by
    dsimp [n, m]
    exact_mod_cast (by omega : k + 1 ≤ 2 * (k + 1) + 1)
  have hexp : -z.re ≤ 0 := by linarith
  have hradial : m ^ (-z.re) ≤ n ^ (-z.re) :=
    Real.antitoneOn_rpow_Ioi_of_exponent_nonpos hexp hn hm hnm
  have hna : 0 ≤ n ^ a := Real.rpow_nonneg hn.le _
  unfold etaPairIndexScaledEulerHalfEndpoint
  rw [norm_mul, norm_mul, norm_etaUnsignedVector]
  have hhalf : ‖((1 : ℂ) / 2)‖ = (1 : ℝ) / 2 := by norm_num
  rw [hhalf]
  simp only [Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_nonneg hna]
  change n ^ a * ((1 / 2 : ℝ) * m ^ (-z.re)) ≤
    (1 / 2 : ℝ) * n ^ (a - z.re)
  calc
    n ^ a * ((1 / 2 : ℝ) * m ^ (-z.re)) =
        (1 / 2 : ℝ) * (n ^ a * m ^ (-z.re)) := by ring
    _ ≤ (1 / 2 : ℝ) * (n ^ a * n ^ (-z.re)) := by
      gcongr
    _ = (1 / 2 : ℝ) * n ^ (a - z.re) := by
      rw [← Real.rpow_add hn]
      congr 2

/-- Every strictly subdominant Euler half-endpoint tends to zero. -/
theorem etaPairIndexScaledEulerHalfEndpoint_tendsto_zero
    {a : ℝ} {z : ℂ} (hzre : 0 < z.re) (ha : a < z.re) :
    Tendsto
      (etaPairIndexScaledEulerHalfEndpoint a z)
      atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hbase :
      Tendsto (fun k : ℕ => (((k + 1 : ℕ) : ℝ))) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp tendsto_nat_succ_atTop
  have hpow0 :
      Tendsto
        (fun k : ℕ =>
          (((k + 1 : ℕ) : ℝ) ^ (-(z.re - a))))
        atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (sub_pos.mpr ha)).comp hbase
  have hupper :
      Tendsto
        (fun k : ℕ =>
          ((1 : ℝ) / 2) *
            (((k + 1 : ℕ) : ℝ) ^ (a - z.re)))
        atTop (nhds 0) := by
    have hpow :
        Tendsto
          (fun k : ℕ =>
            (((k + 1 : ℕ) : ℝ) ^ (a - z.re)))
          atTop (nhds 0) := by
      convert hpow0 using 1; ring_nf
    simpa using
      (show Tendsto (fun _ : ℕ => (1 : ℝ) / 2) atTop
          (nhds ((1 : ℝ) / 2)) from tendsto_const_nhds).mul hpow
  exact
    tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hupper
      (Eventually.of_forall fun k => norm_nonneg _)
      (Eventually.of_forall fun k =>
        norm_etaPairIndexScaledEulerHalfEndpoint_le_decay hzre ha k)

/--
The single dominant Euler half-endpoint carrier.

On the critical line the full Euler main carrier is retained; it is exactly
zero there.  Off the critical line only the slower-decaying half-endpoint is
retained.
-/
noncomputable def etaCriticalMirrorDominantEulerHalfEndpointCarrier
    (k : ℕ) (s : ℂ) : ℂ :=
  if s.re = (1 : ℝ) / 2 then
    etaCriticalMirrorDominantWeightedTailEulerMainCarrier k s
  else if s.re < (1 : ℝ) / 2 then
    etaPairIndexScaledEulerHalfEndpoint s.re s k
  else
    -etaPairIndexScaledEulerHalfEndpoint
      (criticalMirror s).re (criticalMirror s) k

/-- The Euler-main part discarded after selecting the single dominant half-endpoint. -/
noncomputable def etaCriticalMirrorSuppressedEulerHalfEndpointCarrier
    (k : ℕ) (s : ℂ) : ℂ :=
  etaCriticalMirrorDominantWeightedTailEulerMainCarrier k s -
    etaCriticalMirrorDominantEulerHalfEndpointCarrier k s

/-- Exact dominant-plus-suppressed decomposition of the Euler main carrier. -/
theorem etaCriticalMirrorDominantWeightedTailEulerMainCarrier_eq_dominant_add_suppressed
    (k : ℕ) (s : ℂ) :
    etaCriticalMirrorDominantWeightedTailEulerMainCarrier k s =
      etaCriticalMirrorDominantEulerHalfEndpointCarrier k s +
        etaCriticalMirrorSuppressedEulerHalfEndpointCarrier k s := by
  unfold etaCriticalMirrorSuppressedEulerHalfEndpointCarrier
  ring

/-- The discarded Euler half-endpoint tends to zero at every nontrivial zero. -/
theorem etaCriticalMirrorSuppressedEulerHalfEndpointCarrier_tendsto_zero
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) :
    Tendsto
      (fun k : ℕ =>
        etaCriticalMirrorSuppressedEulerHalfEndpointCarrier k s)
      atTop (nhds 0) := by
  have hsre : 0 < s.re := nontrivialRiemannZetaZero_re_pos hs
  have hmre : 0 < (criticalMirror s).re :=
    criticalMirror_re_pos_of_nontrivialRiemannZetaZero hs
  by_cases hcritical : s.re = (1 : ℝ) / 2
  · have hzero :
        (fun k : ℕ =>
          etaCriticalMirrorSuppressedEulerHalfEndpointCarrier k s) =
        fun _ : ℕ => 0 := by
      funext k
      simp [etaCriticalMirrorSuppressedEulerHalfEndpointCarrier,
        etaCriticalMirrorDominantEulerHalfEndpointCarrier, hcritical]
    rw [hzero]
    exact tendsto_const_nhds
  · rcases lt_or_gt_of_ne hcritical with hleft | hright
    · have hside : s.re ≤ (2 : ℝ)⁻¹ := by simpa using le_of_lt hleft
      have hstrict : s.re < (criticalMirror s).re := by
        simp only [criticalMirror_re]
        linarith
      have htail :=
        (etaPairIndexScaledEulerHalfEndpoint_tendsto_zero
          (a := s.re) (z := criticalMirror s) hmre hstrict).neg
      have htail' :
          Tendsto (fun k : ℕ => -etaPairIndexScaledEulerHalfEndpoint s.re
            (criticalMirror s) k) atTop (nhds 0) := by
        simpa using htail
      refine htail'.congr' (Eventually.of_forall fun k => ?_)
      simp only [etaPairIndexScaledEulerHalfEndpoint, Nat.cast_add, Nat.cast_one, one_div,
        etaCriticalMirrorSuppressedEulerHalfEndpointCarrier,
        etaCriticalMirrorDominantWeightedTailEulerMainCarrier, etaCriticalMirrorDominantIndexPower,
        hside, ↓reduceIte, etaCriticalMirrorDominantEulerHalfEndpointCarrier, criticalMirror_re]
      split <;> simp_all; ring
    · have hside : ¬ s.re ≤ (2 : ℝ)⁻¹ := by
        have : (1 : ℝ) / 2 < s.re := hright
        simpa using not_le.mpr this
      have hnotlt : ¬ s.re < (1 : ℝ) / 2 := not_lt_of_ge (le_of_lt hright)
      have hnotltHalf : ¬ s.re < (1 : ℝ) / 2 := by
        exact hnotlt
      have hstrict : (criticalMirror s).re < s.re := by
        simp only [criticalMirror_re]
        linarith
      have htail :=
        etaPairIndexScaledEulerHalfEndpoint_tendsto_zero
          (a := (criticalMirror s).re) (z := s) hsre hstrict
      refine htail.congr' (Eventually.of_forall fun k => ?_)
      simp only [etaPairIndexScaledEulerHalfEndpoint, Nat.cast_add, Nat.cast_one, criticalMirror_re,
        one_div, etaCriticalMirrorSuppressedEulerHalfEndpointCarrier,
        etaCriticalMirrorDominantWeightedTailEulerMainCarrier, etaCriticalMirrorDominantIndexPower,
        hside, ↓reduceIte, etaCriticalMirrorDominantEulerHalfEndpointCarrier]
      split
      · simp_all
      · have hnh : ¬ s.re < (1 : ℝ) / 2 := by linarith
        have hnhInv : ¬ s.re < (2 : ℝ)⁻¹ := by
          exact not_lt_of_ge (le_of_lt (lt_of_not_ge hside))
        rw [ite_eq_right hnhInv]
        ring

/-- Transverse defect of the single dominant Euler half-endpoint carrier. -/
noncomputable def etaCriticalMirrorDominantEulerHalfEndpointCarrierTransverseError
    (k : ℕ) (s : ℂ) : ℝ :=
  complexRealLineDefect
    (completedZetaCanonicalSlopeDirection s)
    (etaCriticalMirrorDominantEulerHalfEndpointCarrier k s)

/-- The suppressed half-endpoint contributes no asymptotic transverse defect. -/
theorem etaCriticalMirrorSuppressedEulerHalfEndpointCarrierTransverseError_tendsto_zero
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) :
    Tendsto
      (fun k : ℕ =>
        complexRealLineDefect
          (completedZetaCanonicalSlopeDirection s)
          (etaCriticalMirrorSuppressedEulerHalfEndpointCarrier k s))
      atTop (nhds 0) := by
  have hcarrier :=
    etaCriticalMirrorSuppressedEulerHalfEndpointCarrier_tendsto_zero hs
  have hrotated :
      Tendsto
        (fun k : ℕ =>
          (completedZetaCanonicalSlopeDirection s)⁻¹ *
            etaCriticalMirrorSuppressedEulerHalfEndpointCarrier k s)
        atTop (nhds 0) := by
    simpa only [mul_zero] using
      (show Tendsto
          (fun _ : ℕ => (completedZetaCanonicalSlopeDirection s)⁻¹)
          atTop (nhds (completedZetaCanonicalSlopeDirection s)⁻¹) from
        tendsto_const_nhds).mul hcarrier
  have himaginary := (Complex.continuous_im.tendsto 0).comp hrotated
  simpa [complexRealLineDefect, Function.comp_def] using himaginary

/-- Direct line-collapse contract for the single dominant half-endpoint carrier. -/
def EtaCriticalMirrorDominantEulerHalfEndpointCarrierTransverseCollapse : Prop :=
  ∀ {s : ℂ},
    NontrivialRiemannZetaZero s →
    s.im ≠ 0 →
    Tendsto
      (fun k : ℕ =>
        etaCriticalMirrorDominantEulerHalfEndpointCarrierTransverseError k s)
      atTop (nhds 0)

/-- The Euler-main line contract is equivalent to its single dominant half-endpoint. -/
theorem etaCriticalMirrorWeightedTailEulerMainCarrierTransverseCollapse_iff_dominantHalfEndpoint :
    EtaCriticalMirrorWeightedTailEulerMainCarrierTransverseCollapse ↔
      EtaCriticalMirrorDominantEulerHalfEndpointCarrierTransverseCollapse := by
  constructor
  · intro hmain s hs him
    have hm := hmain hs him
    have hsuppressed :=
      etaCriticalMirrorSuppressedEulerHalfEndpointCarrierTransverseError_tendsto_zero hs
    have hdiff := hm.sub hsuppressed
    have hdiff' :
        Tendsto
          (fun k : ℕ =>
            etaCriticalMirrorWeightedTailEulerMainCarrierTransverseError k s -
              complexRealLineDefect
                (completedZetaCanonicalSlopeDirection s)
                (etaCriticalMirrorSuppressedEulerHalfEndpointCarrier k s))
          atTop (nhds 0) := by
      simpa only [sub_zero] using hdiff
    refine hdiff'.congr' (Eventually.of_forall fun k => ?_)
    unfold etaCriticalMirrorWeightedTailEulerMainCarrierTransverseError
    unfold etaCriticalMirrorDominantEulerHalfEndpointCarrierTransverseError
    rw [etaCriticalMirrorDominantWeightedTailEulerMainCarrier_eq_dominant_add_suppressed]
    simp [complexRealLineDefect, mul_add]
  · intro hdominant s hs him
    have hd := hdominant hs him
    have hsuppressed :=
      etaCriticalMirrorSuppressedEulerHalfEndpointCarrierTransverseError_tendsto_zero hs
    have hsum := hd.add hsuppressed
    have hsum' :
        Tendsto
          (fun k : ℕ =>
            etaCriticalMirrorDominantEulerHalfEndpointCarrierTransverseError k s +
              complexRealLineDefect
                (completedZetaCanonicalSlopeDirection s)
                (etaCriticalMirrorSuppressedEulerHalfEndpointCarrier k s))
          atTop (nhds 0) := by
      simpa only [add_zero] using hsum
    refine hsum'.congr' (Eventually.of_forall fun k => ?_)
    change complexRealLineDefect (completedZetaCanonicalSlopeDirection s)
        (etaCriticalMirrorDominantEulerHalfEndpointCarrier k s) +
        complexRealLineDefect (completedZetaCanonicalSlopeDirection s)
          (etaCriticalMirrorSuppressedEulerHalfEndpointCarrier k s) =
      complexRealLineDefect (completedZetaCanonicalSlopeDirection s)
        (etaCriticalMirrorDominantWeightedTailEulerMainCarrier k s)
    rw [etaCriticalMirrorDominantWeightedTailEulerMainCarrier_eq_dominant_add_suppressed]
    simp [complexRealLineDefect, mul_add]

/-- RH follows from line collapse of the single dominant half-endpoint carrier. -/
theorem riemannHypothesis_of_dominantEulerHalfEndpointCarrierTransverseCollapse
    (hdominant :
      EtaCriticalMirrorDominantEulerHalfEndpointCarrierTransverseCollapse) :
    RiemannHypothesis :=
  riemannHypothesis_of_weightedTailEulerMainCarrierTransverseCollapse
    (etaCriticalMirrorWeightedTailEulerMainCarrierTransverseCollapse_iff_dominantHalfEndpoint.mpr
      hdominant)

#print axioms etaPairIndexScaledEulerHalfEndpoint_tendsto_zero
#print axioms etaCriticalMirrorSuppressedEulerHalfEndpointCarrier_tendsto_zero
#print axioms etaCriticalMirrorWeightedTailEulerMainCarrierTransverseCollapse_iff_dominantHalfEndpoint
#print axioms riemannHypothesis_of_dominantEulerHalfEndpointCarrierTransverseCollapse

end DkMath.RH.CFBRCProjection
