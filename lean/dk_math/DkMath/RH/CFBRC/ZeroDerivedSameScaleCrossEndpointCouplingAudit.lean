/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.ZeroDerivedDualTailRateNormalizedModeBridgeAudit
import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameCompletedZetaFiniteEtaTailReduction
import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameCompletedZetaFirstOrderOrbitAudit
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.ZeroDerivedSameScaleCrossEndpointCouplingAudit"

/-!
# ZDSS-005: same-scale cross-endpoint coupling source audit

ZDSS-004 identifies the raw mirror/original endpoint-norm ratio as the exact
product of the horizontal increment ratio and a separately normalized ratio
with a finite positive limit.  This file derives the sharp common-scale
frontier from that factorization.

If the centered coordinate is positive, the raw ratio tends to `+∞`; if it is
negative, the raw ratio tends to zero.  Consequently it is enough to bound the
raw ratio above merely frequently (equivalently, at infinitely many natural
cutoffs) at a zero and at its critical mirror.  Mirror reapplication then
forces the critical line.  At one zero, an eventual positive lower bound and
frequent upper control also force the critical line.

These are frontier implications, not new zero-derived providers.  The current
finite completed-zeta orbit API expands an already RH-sufficient residual
collapse, first-order functional reflection transports derivative data, and
prime-coordinate decomposition retains cancellation.  None supplies the
frequent common-scale upper control formalized here.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open scoped Topology
open DkMath.RH.Weave.Analytic

/-! ## Exact raw-ratio asymptotic dichotomy -/

/-- Positive horizontal offset makes the endpoint increment ratio diverge. -/
theorem etaEndpointIncrementMirrorRatio_tendsto_atTop_of_centeredSigma_pos
    {s : ℂ} (hdelta : 0 < centeredSigma s.re) :
    Tendsto (fun k : ℕ => etaEndpointIncrementMirrorRatio s k)
      atTop atTop := by
  simpa only [etaEndpointIncrementMirrorRatio_eq_etaMirrorAmplitudeRatio,
    etaMirrorAmplitudeRatio_eq_rpow, Function.comp_def] using
    (tendsto_rpow_atTop (by linarith : 0 < 2 * centeredSigma s.re)).comp
      tendsto_nat_succ_cast_atTop

/-- Negative horizontal offset makes the endpoint increment ratio tend to zero. -/
theorem etaEndpointIncrementMirrorRatio_tendsto_zero_of_centeredSigma_neg
    {s : ℂ} (hdelta : centeredSigma s.re < 0) :
    Tendsto (fun k : ℕ => etaEndpointIncrementMirrorRatio s k)
      atTop (nhds 0) := by
  have hpow :=
    (tendsto_rpow_neg_atTop
      (by linarith : 0 < -(2 * centeredSigma s.re))).comp
        tendsto_nat_succ_cast_atTop
  simpa only [etaEndpointIncrementMirrorRatio_eq_etaMirrorAmplitudeRatio,
    etaMirrorAmplitudeRatio_eq_rpow, Function.comp_def, neg_neg] using hpow

/--
At a nonreal standard zero on the right of the critical line, the common-scale
raw endpoint-norm ratio tends to `+∞`.  The proof uses the exact ZDSS-004
factorization and the positive limit of its self-normalized factor.
-/
theorem etaDualEndpointRawNormRatio_tendsto_atTop_of_centeredSigma_pos
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) (him : s.im ≠ 0)
    (hdelta : 0 < centeredSigma s.re) :
    Tendsto (fun k : ℕ => etaDualEndpointRawNormRatio k s)
      atTop atTop := by
  have hmode :=
    etaEndpointIncrementMirrorRatio_tendsto_atTop_of_centeredSigma_pos
      hdelta
  have hnormalized :=
    etaDualEndpointNormalizedNormRatio_tendsto_limit_of_nontrivialRiemannZetaZero
      hs him
  have hproduct := hmode.atTop_mul_pos
    (etaDualEndpointNormalizedNormRatioLimit_pos s) hnormalized
  exact hproduct.congr'
    (Filter.EventuallyEq.symm
      (eventually_etaDualEndpointRawNormRatio_eq_incrementRatio_mul_normalizedNormRatio_of_nontrivialRiemannZetaZero
        hs him))

/--
At a nonreal standard zero on the left of the critical line, the common-scale
raw endpoint-norm ratio tends to zero.  Thus eventual upper boundedness alone
contains no information against this horizontal direction.
-/
theorem etaDualEndpointRawNormRatio_tendsto_zero_of_centeredSigma_neg
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) (him : s.im ≠ 0)
    (hdelta : centeredSigma s.re < 0) :
    Tendsto (fun k : ℕ => etaDualEndpointRawNormRatio k s)
      atTop (nhds 0) := by
  have hmode :=
    etaEndpointIncrementMirrorRatio_tendsto_zero_of_centeredSigma_neg
      hdelta
  have hnormalized :=
    etaDualEndpointNormalizedNormRatio_tendsto_limit_of_nontrivialRiemannZetaZero
      hs him
  have hproduct := hmode.mul hnormalized
  have hproduct' :
      Tendsto
        (fun k : ℕ =>
          etaEndpointIncrementMirrorRatio s k *
            etaDualEndpointNormalizedNormRatio k s)
        atTop (nhds 0) := by
    simpa only [zero_mul] using hproduct
  exact hproduct'.congr'
    (Filter.EventuallyEq.symm
      (eventually_etaDualEndpointRawNormRatio_eq_incrementRatio_mul_normalizedNormRatio_of_nontrivialRiemannZetaZero
        hs him))

/-! ## Weak common-scale frontier predicates -/

/--
The raw endpoint ratio is bounded above at infinitely many cutoffs.  On the
natural-number `atTop` filter, `Frequently` is the cofinal/subsequential form
of upper control.  This is a diagnostic U1X frontier, not a source theorem.
-/
def EtaDualEndpointRawNormRatioFrequentlyBoundedAboveAt (s : ℂ) : Prop :=
  ∃ C : ℝ,
    ∃ᶠ k : ℕ in atTop,
      etaDualEndpointRawNormRatio k s ≤ C

/--
The raw endpoint ratio is eventually bounded away from zero.  Together with
frequent upper control at the same zero, this gives two-sided common-scale
comparability without requiring convergence of the raw ratio.
-/
def EtaDualEndpointRawNormRatioEventuallyBoundedAwayFromZeroAt
    (s : ℂ) : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ᶠ k : ℕ in atTop,
      c ≤ etaDualEndpointRawNormRatio k s

/-- Frequent upper control excludes only a positive centered coordinate. -/
theorem centeredSigma_nonpos_of_rawNormRatio_frequently_boundedAbove
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) (him : s.im ≠ 0)
    (hupper : EtaDualEndpointRawNormRatioFrequentlyBoundedAboveAt s) :
    centeredSigma s.re ≤ 0 := by
  by_contra hnot
  have hdelta : 0 < centeredSigma s.re := lt_of_not_ge hnot
  rcases hupper with ⟨C, hfrequent⟩
  have hgt :=
    (etaDualEndpointRawNormRatio_tendsto_atTop_of_centeredSigma_pos
      hs him hdelta).eventually_gt_atTop C
  rcases (hfrequent.and_eventually hgt).exists with ⟨k, hle, hlt⟩
  exact (not_lt_of_ge hle) hlt

/-- An eventual positive lower bound excludes only a negative centered coordinate. -/
theorem centeredSigma_nonneg_of_rawNormRatio_eventually_boundedAwayFromZero
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) (him : s.im ≠ 0)
    (hlower :
      EtaDualEndpointRawNormRatioEventuallyBoundedAwayFromZeroAt s) :
    0 ≤ centeredSigma s.re := by
  by_contra hnot
  have hdelta : centeredSigma s.re < 0 := lt_of_not_ge hnot
  rcases hlower with ⟨c, hc, heventual⟩
  have hlt :
      ∀ᶠ k : ℕ in atTop,
        etaDualEndpointRawNormRatio k s < c :=
    (etaDualEndpointRawNormRatio_tendsto_zero_of_centeredSigma_neg
      hs him hdelta).eventually (eventually_lt_nhds hc)
  rcases (heventual.and hlt).exists with ⟨k, hle, hlt'⟩
  exact (not_lt_of_ge hle) hlt'

/--
Two-sided common-scale comparability at one zero forces the critical line.
The hypotheses are intentionally exposed as frontier data and are not claimed
to follow from the standard zero predicate.
-/
theorem re_eq_half_of_rawNormRatio_twoSided_comparability
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) (him : s.im ≠ 0)
    (hupper : EtaDualEndpointRawNormRatioFrequentlyBoundedAboveAt s)
    (hlower :
      EtaDualEndpointRawNormRatioEventuallyBoundedAwayFromZeroAt s) :
    s.re = (1 : ℝ) / 2 := by
  have hnonpos :=
    centeredSigma_nonpos_of_rawNormRatio_frequently_boundedAbove
      hs him hupper
  have hnonneg :=
    centeredSigma_nonneg_of_rawNormRatio_eventually_boundedAwayFromZero
      hs him hlower
  exact (centeredSigma_eq_zero_iff s.re).mp (le_antisymm hnonpos hnonneg)

/-! ## Mirror reapplication and the global source frontier -/

/--
Frequent upper control at a zero and its critical mirror forces the critical
line.  Each application supplies only one inequality; mirror reflection
reverses the centered coordinate and closes the missing direction.
-/
theorem re_eq_half_of_rawNormRatio_frequently_boundedAbove_at_zero_and_mirror
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) (him : s.im ≠ 0)
    (hupper : EtaDualEndpointRawNormRatioFrequentlyBoundedAboveAt s)
    (hupperMirror :
      EtaDualEndpointRawNormRatioFrequentlyBoundedAboveAt
        (criticalMirror s)) :
    s.re = (1 : ℝ) / 2 := by
  have hnonpos :=
    centeredSigma_nonpos_of_rawNormRatio_frequently_boundedAbove
      hs him hupper
  have himMirror : (criticalMirror s).im ≠ 0 := by
    simpa using him
  have hmirrorNonpos :=
    centeredSigma_nonpos_of_rawNormRatio_frequently_boundedAbove
      (criticalMirror_nontrivialRiemannZetaZero hs) himMirror hupperMirror
  have hzero : centeredSigma s.re = 0 := by
    rw [criticalMirror_re] at hmirrorNonpos
    unfold centeredSigma at hnonpos hmirrorNonpos ⊢
    linarith
  exact (centeredSigma_eq_zero_iff s.re).mp hzero

/--
Global candidate provider: every nonreal standard zero has a raw endpoint
ratio bounded above at infinitely many common cutoffs.  The definition names
the exact missing source obligation and does not assert it.
-/
def EtaDualEndpointRawNormRatioFrequentlyBoundedAboveOnZeros : Prop :=
  ∀ {s : ℂ},
    NontrivialRiemannZetaZero s →
    s.im ≠ 0 →
    EtaDualEndpointRawNormRatioFrequentlyBoundedAboveAt s

/--
The global frequent-upper-control provider is RH-load-bearing: applying it at
each zero and again at its critical mirror proves the Riemann hypothesis.
-/
theorem riemannHypothesis_of_rawNormRatio_frequently_boundedAboveOnZeros
    (hprovider :
      EtaDualEndpointRawNormRatioFrequentlyBoundedAboveOnZeros) :
    RiemannHypothesis := by
  rw [riemannHypothesis_iff_nontrivialZero_re_eq_half]
  intro s hs
  have him := nontrivialRiemannZetaZero_im_ne_zero hs
  have himMirror : (criticalMirror s).im ≠ 0 := by
    simpa using him
  exact
    re_eq_half_of_rawNormRatio_frequently_boundedAbove_at_zero_and_mirror
      hs him (hprovider hs him)
      (hprovider (criticalMirror_nontrivialRiemannZetaZero hs) himMirror)

/--
On the critical line the critical mirror is the point itself, so the raw ratio
is at most one at every cutoff (including a possible `0 / 0`, interpreted as
zero in the field).  Hence the frequent-upper-control frontier is realizable
under the critical-line conclusion.
-/
theorem rawNormRatio_frequently_boundedAbove_of_re_eq_half
    {s : ℂ} (hre : s.re = (1 : ℝ) / 2) :
    EtaDualEndpointRawNormRatioFrequentlyBoundedAboveAt s := by
  refine ⟨1, Frequently.of_forall fun k => ?_⟩
  rw [etaDualEndpointRawNormRatio]
  rw [(criticalMirror_eq_self_iff_re_eq_half s).2 hre]
  by_cases hpartial : etaPairedPartial (k + 1) s = 0
  · simp [hpartial]
  · rw [div_self (norm_ne_zero_iff.mpr hpartial)]

/--
The global frequent common-scale upper-control proposition is exactly
RH-equivalent.  This classifies the frontier sharply; it does not provide the
forward source implication from the standard zero equations.
-/
theorem rawNormRatio_frequently_boundedAboveOnZeros_iff_riemannHypothesis :
    EtaDualEndpointRawNormRatioFrequentlyBoundedAboveOnZeros ↔
      RiemannHypothesis := by
  constructor
  · exact riemannHypothesis_of_rawNormRatio_frequently_boundedAboveOnZeros
  · intro hRH s hs _him
    exact rawNormRatio_frequently_boundedAbove_of_re_eq_half
      ((riemannHypothesis_iff_nontrivialZero_re_eq_half.mp hRH) s hs)

/-!
The existing source inventory supplies no inhabitant of
`EtaDualEndpointRawNormRatioFrequentlyBoundedAboveOnZeros`.  In particular,
the finite completed-zeta orbit residual is an expansion of an RH-sufficient
collapse condition, completed-zeta first-order reflection is transported
orbit data, and the prime-factor endpoint difference retains the established
cancellation firewall.
-/

#print axioms etaEndpointIncrementMirrorRatio_tendsto_atTop_of_centeredSigma_pos
#print axioms etaEndpointIncrementMirrorRatio_tendsto_zero_of_centeredSigma_neg
#print axioms etaDualEndpointRawNormRatio_tendsto_atTop_of_centeredSigma_pos
#print axioms etaDualEndpointRawNormRatio_tendsto_zero_of_centeredSigma_neg
#print axioms centeredSigma_nonpos_of_rawNormRatio_frequently_boundedAbove
#print axioms centeredSigma_nonneg_of_rawNormRatio_eventually_boundedAwayFromZero
#print axioms re_eq_half_of_rawNormRatio_twoSided_comparability
#print axioms re_eq_half_of_rawNormRatio_frequently_boundedAbove_at_zero_and_mirror
#print axioms riemannHypothesis_of_rawNormRatio_frequently_boundedAboveOnZeros
#print axioms rawNormRatio_frequently_boundedAboveOnZeros_iff_riemannHypothesis

end DkMath.RH.CFBRCProjection
