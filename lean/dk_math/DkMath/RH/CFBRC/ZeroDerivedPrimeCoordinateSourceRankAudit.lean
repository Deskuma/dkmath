/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPrimeFactorCoordinateCertificateReentryAudit
import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameFunctionalEquationOrbitAsymptoticAudit
import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameRotatedDefectTailSplit
import Mathlib.Tactic

/-!
# ZDSS-001: zero-derived prime-coordinate source-rank audit

This module separates the two ordinary paired-Eta endpoint sources hidden
behind the P2-F mirror-minus-original defect.  At a nonreal standard zeta zero,
each finite endpoint has its own exact finite-partial-plus-tail identity.  The
P2-F source is their difference, so the endpoint pair contains one more
complex coordinate than the P2-F whole value.

The module also records that evaluating P2-F around the mirror/conjugation/
functional-equation orbit produces only sign and conjugation transports, and
that consecutive-cutoff subtraction is unconditional.  No positive energy,
centered-coordinate coercivity, DkReal interval, or RH provider is introduced.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open ComplexConjugate
open scoped Topology
open DkMath.RH.Weave.Analytic

/-! ## Separate finite endpoint sources -/

/--
An ordinary paired-Eta finite partial plus its ordinary paired tail is the
complete paired sum.  This is an unconditional summability identity on the
open right half-plane.
-/
theorem etaPairedPartial_add_etaPairTail_eq_tsum
    {z : ℂ} (hz : 0 < z.re) (K : ℕ) :
    etaPairedPartial K z + etaPairTail K z =
      ∑' k : ℕ, etaPairTerm z k := by
  have hsum := etaPairedSummableAt_of_pos_re hz
  simpa [etaPairedPartial, etaPairTail] using
    hsum.sum_add_tsum_nat_add K

/--
If the complete ordinary paired sum is zero, every finite partial is exactly
the negative of its own tail.
-/
theorem etaPairedPartial_eq_neg_etaPairTail_of_tsum_eq_zero
    {z : ℂ} (hz : 0 < z.re)
    (htsum : (∑' k : ℕ, etaPairTerm z k) = 0)
    (K : ℕ) :
    etaPairedPartial K z = -etaPairTail K z := by
  have hsplit := etaPairedPartial_add_etaPairTail_eq_tsum hz K
  rw [htsum] at hsplit
  linear_combination hsplit

/--
The original endpoint of a nonreal standard zeta zero is a finite source with
its own exact tail identity.
-/
theorem etaPairedPartial_eq_neg_etaPairTail_of_nontrivialRiemannZetaZero
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) (him : s.im ≠ 0)
    (K : ℕ) :
    etaPairedPartial K s = -etaPairTail K s := by
  have hendpoint :=
    etaPartialEndpoint_tendsto_zero_of_nontrivialRiemannZetaZero hs him
  have htsum : (∑' k : ℕ, etaPairTerm s k) = 0 :=
    (etaPartialEndpoint_tendsto_zero_iff_pairedTsum_eq_zero_of_pos_re
      (nontrivialRiemannZetaZero_re_pos hs)).mp hendpoint
  exact etaPairedPartial_eq_neg_etaPairTail_of_tsum_eq_zero
    (nontrivialRiemannZetaZero_re_pos hs) htsum K

/--
The critical-mirror endpoint has a separate finite-partial-plus-tail identity.
Its zero provenance is the existing functional-equation/conjugation transport
of the standard zero; its finite value is not a sign or conjugate rewrite of
the original endpoint value.
-/
theorem etaPairedPartial_criticalMirror_eq_neg_etaPairTail_of_nontrivialRiemannZetaZero
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) (him : s.im ≠ 0)
    (K : ℕ) :
    etaPairedPartial K (criticalMirror s) =
      -etaPairTail K (criticalMirror s) := by
  have himMirror : (criticalMirror s).im ≠ 0 := by
    simpa using him
  exact etaPairedPartial_eq_neg_etaPairTail_of_nontrivialRiemannZetaZero
    (criticalMirror_nontrivialRiemannZetaZero hs) himMirror K

/-- The original endpoint source inherits the ordinary paired-tail power bound. -/
theorem norm_etaPairedPartial_le_powerBound_of_nontrivialRiemannZetaZero
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) (him : s.im ≠ 0)
    {K : ℕ} (hK : 1 ≤ K) :
    ‖etaPairedPartial K s‖ ≤
      ‖s‖ * (((K : ℝ) ^ (-s.re)) / s.re) := by
  rw [etaPairedPartial_eq_neg_etaPairTail_of_nontrivialRiemannZetaZero
    hs him K, norm_neg]
  exact norm_etaPairTail_le (nontrivialRiemannZetaZero_re_pos hs) hK

/-- The mirror endpoint source has its own ordinary paired-tail power bound. -/
theorem norm_etaPairedPartial_criticalMirror_le_powerBound_of_nontrivialRiemannZetaZero
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) (him : s.im ≠ 0)
    {K : ℕ} (hK : 1 ≤ K) :
    ‖etaPairedPartial K (criticalMirror s)‖ ≤
      ‖criticalMirror s‖ *
        (((K : ℝ) ^ (-(criticalMirror s).re)) / (criticalMirror s).re) := by
  rw [etaPairedPartial_criticalMirror_eq_neg_etaPairTail_of_nontrivialRiemannZetaZero
    hs him K, norm_neg]
  exact norm_etaPairTail_le
    (criticalMirror_re_pos_of_nontrivialRiemannZetaZero hs) hK

/--
ZDSS-001 dual-source certificate.  The same zero supplies exact tail control
for both finite endpoint coordinates, and P2-F is their
mirror-minus-original projection.
-/
theorem etaDualEndpointFiniteSourceCertificate_of_nontrivialRiemannZetaZero
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) (him : s.im ≠ 0)
    (K : ℕ) :
    etaPairedPartial K s = -etaPairTail K s ∧
      etaPairedPartial K (criticalMirror s) =
        -etaPairTail K (criticalMirror s) ∧
      etaPrimeFactorMirrorDefectPairedPartial K s =
        etaPairedPartial K (criticalMirror s) - etaPairedPartial K s := by
  exact
    ⟨etaPairedPartial_eq_neg_etaPairTail_of_nontrivialRiemannZetaZero
        hs him K,
      etaPairedPartial_criticalMirror_eq_neg_etaPairTail_of_nontrivialRiemannZetaZero
        hs him K,
      etaPrimeFactorMirrorDefectPairedPartial_eq_separate_endpoint_difference
        K s⟩

/--
The mirror-minus-original projection from an endpoint pair is not injective.
Thus the P2-F whole value alone cannot reconstruct both endpoint coordinates.
This algebraic fact is used only to classify information loss; it is not a
coercivity theorem for the Eta endpoints.
-/
theorem endpointDifference_not_injective :
    ¬Function.Injective (fun p : ℂ × ℂ => p.1 - p.2) := by
  intro hinjective
  have hsame :
      (fun p : ℂ × ℂ => p.1 - p.2) (0, 0) =
        (fun p : ℂ × ℂ => p.1 - p.2) (1, 1) := by
    norm_num
  have hpairs := hinjective hsame
  norm_num at hpairs

/-! ## Invertible transports of the endpoint pair -/

/-- Ordinary finite paired-Eta endpoints commute with complex conjugation. -/
theorem etaPairedPartial_conj_sourceRank
    (K : ℕ) (s : ℂ) :
    etaPairedPartial K (conj s) = conj (etaPairedPartial K s) := by
  simp [etaPairedPartial, etaPairTerm_conj]

/-- Critical reflection swaps the two ordered endpoint coordinates. -/
theorem etaEndpointPair_criticalMirror_eq_swap
    (K : ℕ) (s : ℂ) :
    (etaPairedPartial K (criticalMirror (criticalMirror s)),
        etaPairedPartial K (criticalMirror s)) =
      (etaPairedPartial K s, etaPairedPartial K (criticalMirror s)) := by
  rw [criticalMirror_involutive]

/-- Conjugation acts componentwise and invertibly on the endpoint pair. -/
theorem etaEndpointPair_conj_eq_componentwise_conj
    (K : ℕ) (s : ℂ) :
    (etaPairedPartial K (criticalMirror (conj s)),
        etaPairedPartial K (conj s)) =
      (conj (etaPairedPartial K (criticalMirror s)),
        conj (etaPairedPartial K s)) := by
  rw [criticalMirror_conj, etaPairedPartial_conj_sourceRank,
    etaPairedPartial_conj_sourceRank]

/-- Functional reflection acts by conjugation followed by swapping endpoints. -/
theorem etaEndpointPair_one_sub_eq_conj_swap
    (K : ℕ) (s : ℂ) :
    (etaPairedPartial K (criticalMirror (1 - s)),
        etaPairedPartial K (1 - s)) =
      (conj (etaPairedPartial K s),
        conj (etaPairedPartial K (criticalMirror s))) := by
  rw [one_sub_eq_conj_criticalMirror, criticalMirror_conj,
    criticalMirror_involutive, etaPairedPartial_conj_sourceRank,
    etaPairedPartial_conj_sourceRank]

/-! ## Duplicate transports of the P2-F whole source -/

/-- Critical reflection changes the P2-F source only by the invertible sign map. -/
theorem etaPrimeFactorMirrorDefectPairedPartial_criticalMirror_eq_neg
    (K : ℕ) (s : ℂ) :
    etaPrimeFactorMirrorDefectPairedPartial K (criticalMirror s) =
      -etaPrimeFactorMirrorDefectPairedPartial K s := by
  rw [etaPrimeFactorMirrorDefectPairedPartial_eq_etaCriticalMirrorDefectPairedPartial]
  rw [etaCriticalMirrorDefectPairedPartial_criticalMirror_eq_neg]
  rw [etaPrimeFactorMirrorDefectPairedPartial_eq_etaCriticalMirrorDefectPairedPartial]

/-- Complex conjugation transports the P2-F source by complex conjugation. -/
theorem etaPrimeFactorMirrorDefectPairedPartial_conj
    (K : ℕ) (s : ℂ) :
    etaPrimeFactorMirrorDefectPairedPartial K (conj s) =
      conj (etaPrimeFactorMirrorDefectPairedPartial K s) := by
  rw [etaPrimeFactorMirrorDefectPairedPartial_eq_etaCriticalMirrorDefectPairedPartial]
  rw [etaCriticalMirrorDefectPairedPartial_conj]
  rw [etaPrimeFactorMirrorDefectPairedPartial_eq_etaCriticalMirrorDefectPairedPartial]

/--
Functional-equation reflection gives the negative conjugate P2-F value, hence
no additional P2-F whole-source coordinate.
-/
theorem etaPrimeFactorMirrorDefectPairedPartial_one_sub_eq_neg_conj
    (K : ℕ) (s : ℂ) :
    etaPrimeFactorMirrorDefectPairedPartial K (1 - s) =
      -conj (etaPrimeFactorMirrorDefectPairedPartial K s) := by
  rw [one_sub_eq_conj_criticalMirror]
  rw [etaPrimeFactorMirrorDefectPairedPartial_conj]
  rw [etaPrimeFactorMirrorDefectPairedPartial_criticalMirror_eq_neg]
  simp

/-! ## Multi-cutoff audit -/

/--
Consecutive P2-F cutoffs recover one prime-factor defect term.  The identity
is unconditional, so subtraction of cutoffs does not add zero-specific source
information.
-/
theorem etaPrimeFactorMirrorDefectPairedPartial_succ_sub
    (K : ℕ) (s : ℂ) :
    etaPrimeFactorMirrorDefectPairedPartial (K + 1) s -
        etaPrimeFactorMirrorDefectPairedPartial K s =
      etaPrimeFactorMirrorDefectPairTerm s K := by
  simp [etaPrimeFactorMirrorDefectPairedPartial, Finset.sum_range_succ]

#print axioms etaPairedPartial_eq_neg_etaPairTail_of_nontrivialRiemannZetaZero
#print axioms etaPairedPartial_criticalMirror_eq_neg_etaPairTail_of_nontrivialRiemannZetaZero
#print axioms norm_etaPairedPartial_le_powerBound_of_nontrivialRiemannZetaZero
#print axioms norm_etaPairedPartial_criticalMirror_le_powerBound_of_nontrivialRiemannZetaZero
#print axioms etaDualEndpointFiniteSourceCertificate_of_nontrivialRiemannZetaZero
#print axioms endpointDifference_not_injective
#print axioms etaEndpointPair_one_sub_eq_conj_swap
#print axioms etaPrimeFactorMirrorDefectPairedPartial_one_sub_eq_neg_conj
#print axioms etaPrimeFactorMirrorDefectPairedPartial_succ_sub

end DkMath.RH.CFBRCProjection
