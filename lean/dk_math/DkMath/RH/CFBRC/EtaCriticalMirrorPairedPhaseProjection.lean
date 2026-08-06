/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPhaseProjection
import DkMath.RH.Weave.Analytic.EtaPairedLimit
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.EtaCriticalMirrorPairedPhaseProjection"

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open scoped Topology
open DkMath.RH.Weave.Analytic

/-- One adjacent pair of critical-mirror defect terms. -/
noncomputable def etaCriticalMirrorDefectPairTerm
    (s : ℂ) (k : ℕ) : ℂ :=
  etaCriticalMirrorDefectTerm s (2 * k) +
    etaCriticalMirrorDefectTerm s (2 * k + 1)

/-- Finite sum of the first `K` adjacent critical-mirror defect pairs. -/
noncomputable def etaCriticalMirrorDefectPairedPartial
    (K : ℕ) (s : ℂ) : ℂ :=
  (Finset.range K).sum (etaCriticalMirrorDefectPairTerm s)

/-- Real projection of one adjacent defect pair after one common rotation. -/
noncomputable def etaCriticalMirrorProjectedDefectPairTerm
    (ω s : ℂ) (k : ℕ) : ℝ :=
  (ω * etaCriticalMirrorDefectPairTerm s k).re

/-- Real projection of the first `K` adjacent defect pairs. -/
noncomputable def etaCriticalMirrorProjectedDefectPairedPartial
    (K : ℕ) (ω s : ℂ) : ℝ :=
  (ω * etaCriticalMirrorDefectPairedPartial K s).re

/-- Adding one natural index appends exactly one complex defect term. -/
theorem etaCriticalMirrorTransportDefectEndpoint_succ
    (N : ℕ) (s : ℂ) :
    etaCriticalMirrorTransportDefectEndpoint (N + 1) s =
      etaCriticalMirrorTransportDefectEndpoint N s +
        etaCriticalMirrorDefectTerm s N := by
  rw [etaCriticalMirrorTransportDefectEndpoint_eq_sum_defectTerm,
    etaCriticalMirrorTransportDefectEndpoint_eq_sum_defectTerm,
    Finset.sum_range_succ]

/-- Adding one pair appends exactly one adjacent defect pair. -/
theorem etaCriticalMirrorDefectPairedPartial_succ
    (K : ℕ) (s : ℂ) :
    etaCriticalMirrorDefectPairedPartial (K + 1) s =
      etaCriticalMirrorDefectPairedPartial K s +
        etaCriticalMirrorDefectPairTerm s K := by
  simp [etaCriticalMirrorDefectPairedPartial, Finset.sum_range_succ]

/--
The first `2K` defect terms are exactly the first `K` adjacent defect pairs.
This is a finite identity and uses no convergence theorem.
-/
theorem etaCriticalMirrorTransportDefectEndpoint_two_mul_eq_pairedPartial
    (K : ℕ) (s : ℂ) :
    etaCriticalMirrorTransportDefectEndpoint (2 * K) s =
      etaCriticalMirrorDefectPairedPartial K s := by
  induction K with
  | zero =>
      simp [etaCriticalMirrorTransportDefectEndpoint_eq_sum_defectTerm,
        etaCriticalMirrorDefectPairedPartial]
  | succ K ih =>
      rw [show 2 * (K + 1) = (2 * K + 1) + 1 by omega]
      rw [etaCriticalMirrorTransportDefectEndpoint_succ]
      rw [etaCriticalMirrorTransportDefectEndpoint_succ]
      rw [etaCriticalMirrorDefectPairedPartial_succ, ← ih]
      simp [etaCriticalMirrorDefectPairTerm]
      abel

/-- Common rotation and real projection commute with the finite paired sum. -/
theorem etaCriticalMirrorProjectedDefectPairedPartial_eq_sum
    (K : ℕ) (ω s : ℂ) :
    etaCriticalMirrorProjectedDefectPairedPartial K ω s =
      (Finset.range K).sum
        (etaCriticalMirrorProjectedDefectPairTerm ω s) := by
  unfold etaCriticalMirrorProjectedDefectPairedPartial
  unfold etaCriticalMirrorDefectPairedPartial
  rw [Finset.mul_sum]
  simp [etaCriticalMirrorProjectedDefectPairTerm]

/-- The projected even defect endpoint is exactly the projected paired partial sum. -/
theorem etaCriticalMirrorProjectedDefectEndpoint_two_mul_eq_pairedPartial
    (K : ℕ) (ω s : ℂ) :
    etaCriticalMirrorProjectedDefectEndpoint (2 * K) ω s =
      etaCriticalMirrorProjectedDefectPairedPartial K ω s := by
  unfold etaCriticalMirrorProjectedDefectEndpoint
  unfold etaCriticalMirrorProjectedDefectPairedPartial
  rw [etaCriticalMirrorTransportDefectEndpoint_two_mul_eq_pairedPartial]

/--
A common-half-plane witness package for adjacent defect pairs.

This is weaker than the termwise certificate: cancellation inside each
adjacent pair is allowed.  Only the paired blocks must share one closed
half-plane, with at least one pair lying in its interior.
-/
structure EtaCriticalMirrorDefectPairHalfPlaneCertificate (s : ℂ) where
  rotation : ℂ
  nonnegative :
    ∀ k : ℕ, 0 ≤ etaCriticalMirrorProjectedDefectPairTerm rotation s k
  positive :
    ∃ k : ℕ, 0 < etaCriticalMirrorProjectedDefectPairTerm rotation s k

/-- A paired half-plane certificate gives an eventual strictly positive lower bound. -/
theorem EtaCriticalMirrorDefectPairHalfPlaneCertificate.eventually_pos_lowerBound
    {s : ℂ} (cert : EtaCriticalMirrorDefectPairHalfPlaneCertificate s) :
    ∃ c : ℝ, 0 < c ∧
      ∀ᶠ K : ℕ in atTop,
        c ≤ etaCriticalMirrorProjectedDefectPairedPartial
          K cert.rotation s := by
  rcases cert.positive with ⟨k, hk⟩
  refine ⟨etaCriticalMirrorProjectedDefectPairTerm cert.rotation s k, hk, ?_⟩
  refine eventually_atTop.2 ⟨(k + 1 : ℕ), ?_⟩
  intro K hK
  rw [etaCriticalMirrorProjectedDefectPairedPartial_eq_sum]
  apply Finset.single_le_sum
  · intro i hi
    exact cert.nonnegative i
  · exact Finset.mem_range.mpr (by omega)

/-- A paired half-plane certificate prevents the paired partial sums from tending to zero. -/
theorem not_tendsto_etaCriticalMirrorProjectedDefectPairedPartial_zero_of_halfPlane
    {s : ℂ} (cert : EtaCriticalMirrorDefectPairHalfPlaneCertificate s) :
    ¬ Tendsto
      (fun K : ℕ =>
        etaCriticalMirrorProjectedDefectPairedPartial K cert.rotation s)
      atTop (nhds 0) := by
  intro hzero
  rcases cert.eventually_pos_lowerBound with ⟨c, hc, hLower⟩
  have hle : c ≤ (0 : ℝ) :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hzero hLower
  exact (not_le_of_gt hc) hle

/--
At a nonreal nontrivial zeta zero, every fixed projection of the adjacent
paired defect partial sums tends to zero.
-/
theorem etaCriticalMirrorProjectedDefectPairedPartial_tendsto_zero_of_nontrivialRiemannZetaZero
    {s ω : ℂ} (hs : NontrivialRiemannZetaZero s) (him : s.im ≠ 0) :
    Tendsto
      (fun K : ℕ => etaCriticalMirrorProjectedDefectPairedPartial K ω s)
      atTop (nhds 0) := by
  have heven :=
    (etaCriticalMirrorProjectedDefectEndpoint_tendsto_zero_of_nontrivialRiemannZetaZero
      (s := s) (ω := ω) hs him).comp tendsto_two_mul_atTop
  refine heven.congr' (Eventually.of_forall fun K => ?_)
  exact etaCriticalMirrorProjectedDefectEndpoint_two_mul_eq_pairedPartial K ω s

/-- A nonreal nontrivial zero cannot carry an adjacent-pair half-plane certificate. -/
theorem not_etaCriticalMirrorDefectPairHalfPlaneCertificate_of_nontrivialRiemannZetaZero
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) (him : s.im ≠ 0) :
    EtaCriticalMirrorDefectPairHalfPlaneCertificate s → False := by
  intro cert
  exact
    not_tendsto_etaCriticalMirrorProjectedDefectPairedPartial_zero_of_halfPlane cert
      (etaCriticalMirrorProjectedDefectPairedPartial_tendsto_zero_of_nontrivialRiemannZetaZero
        hs him)

/--
Minimal off-critical adjacent-pair phase-separation provider.  It permits
cancellation inside each natural eta pair and asks only for one common
half-plane after pairing.
-/
def EtaCriticalMirrorOffCriticalPairHalfPlaneSeparation (s : ℂ) : Type :=
  s.re ≠ (1 : ℝ) / 2 →
    EtaCriticalMirrorDefectPairHalfPlaneCertificate s

/-- Adjacent-pair phase separation forces a nonreal nontrivial zero onto the critical line. -/
theorem re_eq_half_of_nontrivialRiemannZetaZero_of_offCriticalPairHalfPlaneSeparation
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) (him : s.im ≠ 0)
    (hsep : EtaCriticalMirrorOffCriticalPairHalfPlaneSeparation s) :
    s.re = (1 : ℝ) / 2 := by
  by_contra hre
  exact
    (not_etaCriticalMirrorDefectPairHalfPlaneCertificate_of_nontrivialRiemannZetaZero
      hs him) (hsep hre)

/-- Adjacent-pair phase separation maps a nonreal nontrivial zero into CFBRC closure. -/
theorem offCriticalCFBRC_eq_zero_of_nontrivialRiemannZetaZero_of_offCriticalPairHalfPlaneSeparation
    {d : ℕ} (hd : 0 < d) {s : ℂ} (Θ : ℝ)
    (hs : NontrivialRiemannZetaZero s) (him : s.im ≠ 0)
    (hsep : EtaCriticalMirrorOffCriticalPairHalfPlaneSeparation s) :
    offCriticalCFBRC d s.re Θ = 0 := by
  apply (offCriticalCFBRC_eq_zero_iff_re_eq_half hd s.re Θ).2
  exact
    re_eq_half_of_nontrivialRiemannZetaZero_of_offCriticalPairHalfPlaneSeparation
      hs him hsep

end DkMath.RH.CFBRCProjection
