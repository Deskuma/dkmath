/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameMirrorInvolutionAsymptoticAudit
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameConjugationAsymptoticAudit"

set_option linter.style.longLine false

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open ComplexConjugate
open scoped Topology
open DkMath.RH.Weave.Analytic

/-- The local nontrivial-zero predicate is closed under complex conjugation. -/
theorem nontrivialRiemannZetaZero_conj
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) :
    NontrivialRiemannZetaZero (conj s) := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [riemannZeta_conj, hs.1, map_zero]
  · rintro ⟨n, hn⟩
    apply hs.2.1
    refine ⟨n, ?_⟩
    have h := congrArg (conj : ℂ → ℂ) hn
    simp only [starRingEnd_apply, star_star, map_neg, map_mul] at h
    norm_num [Complex.star_def] at h
    simpa [neg_mul] using h
  · intro h
    apply hs.2.2
    have h' := congrArg (conj : ℂ → ℂ) h
    simpa using h'

/-- Critical reflection commutes with complex conjugation. -/
theorem criticalMirror_conj
    (s : ℂ) :
    criticalMirror (conj s) = conj (criticalMirror s) := by
  apply Complex.ext <;> simp [criticalMirror]

/-- Positive-natural Dirichlet vectors commute with complex conjugation. -/
theorem etaUnsignedVector_conj
    (s : ℂ) (m : ℕ) :
    etaUnsignedVector (conj s) m =
      conj (etaUnsignedVector s m) := by
  unfold etaUnsignedVector
  have harg : ((((m + 1 : ℕ) : ℂ))).arg ≠ Real.pi := by
    have hm : (0 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by positivity
    intro hpi
    have hzero : ((((m + 1 : ℕ) : ℂ))).arg = 0 :=
      Complex.arg_ofReal_of_nonneg hm
    rw [hzero] at hpi
    exact (ne_of_gt Real.pi_pos) hpi.symm
  simpa using
    (Complex.cpow_conj ((((m + 1 : ℕ) : ℂ))) (-s) harg)

/-- Alternating eta vectors commute with complex conjugation. -/
theorem etaSignedVector_conj
    (s : ℂ) (m : ℕ) :
    etaSignedVector (conj s) m =
      conj (etaSignedVector s m) := by
  by_cases hm : Even m <;>
    simp [etaSignedVector, hm, etaUnsignedVector_conj]

/-- Paired eta differences commute with complex conjugation. -/
theorem etaPairTerm_conj
    (s : ℂ) (k : ℕ) :
    etaPairTerm (conj s) k = conj (etaPairTerm s k) := by
  simp [etaPairTerm, etaUnsignedVector_conj]

/-- Paired critical-mirror defects commute with complex conjugation. -/
theorem etaCriticalMirrorDefectPairTerm_conj
    (s : ℂ) (k : ℕ) :
    etaCriticalMirrorDefectPairTerm (conj s) k =
      conj (etaCriticalMirrorDefectPairTerm s k) := by
  calc
    etaCriticalMirrorDefectPairTerm (conj s) k =
        etaPairTerm (criticalMirror (conj s)) k -
          etaPairTerm (conj s) k :=
      etaCriticalMirrorDefectPairTerm_eq_etaPairTerm_sub (conj s) k
    _ = etaPairTerm (conj (criticalMirror s)) k -
          etaPairTerm (conj s) k := by
      rw [criticalMirror_conj]
    _ = conj (etaPairTerm (criticalMirror s) k) -
          conj (etaPairTerm s k) := by
      rw [etaPairTerm_conj, etaPairTerm_conj]
    _ = conj
          (etaPairTerm (criticalMirror s) k - etaPairTerm s k) := by
      simp
    _ = conj (etaCriticalMirrorDefectPairTerm s k) := by
      rw [etaCriticalMirrorDefectPairTerm_eq_etaPairTerm_sub]

/-- Every finite paired defect endpoint commutes with complex conjugation. -/
theorem etaCriticalMirrorDefectPairedPartial_conj
    (K : ℕ) (s : ℂ) :
    etaCriticalMirrorDefectPairedPartial K (conj s) =
      conj (etaCriticalMirrorDefectPairedPartial K s) := by
  simp [etaCriticalMirrorDefectPairedPartial,
    etaCriticalMirrorDefectPairTerm_conj]

/-- The pair-left base rotation at the conjugate point is the conjugate rotation. -/
theorem etaPairBaseRotation_conj
    (s : ℂ) (k : ℕ) :
    etaPairBaseRotation (conj s) k =
      conj (etaPairBaseRotation s k) := by
  unfold etaPairBaseRotation
  rw [show (conj s).im = -s.im by simp]
  rw [← Complex.exp_conj]
  congr 1
  simp

/-- Dominant-power normalized even defect endpoints commute with conjugation. -/
theorem etaCriticalMirrorIndexNormalizedEvenDefectEndpoint_conj
    (a : ℝ) (s : ℂ) (k : ℕ) :
    etaCriticalMirrorIndexNormalizedEvenDefectEndpoint a (conj s) k =
      conj (etaCriticalMirrorIndexNormalizedEvenDefectEndpoint a s k) := by
  unfold etaCriticalMirrorIndexNormalizedEvenDefectEndpoint
  rw [etaCriticalMirrorTransportDefectEndpoint_two_mul_eq_pairedPartial,
    etaCriticalMirrorTransportDefectEndpoint_two_mul_eq_pairedPartial,
    etaCriticalMirrorDefectPairedPartial_conj]
  simp

/-- Rotating-frame normalized even endpoints commute with conjugation. -/
theorem etaCriticalMirrorIndexNormalizedRotatedEvenDefectEndpoint_conj
    (a : ℝ) (s : ℂ) (k : ℕ) :
    etaCriticalMirrorIndexNormalizedRotatedEvenDefectEndpoint
        a (conj s) k =
      conj
        (etaCriticalMirrorIndexNormalizedRotatedEvenDefectEndpoint a s k) := by
  unfold etaCriticalMirrorIndexNormalizedRotatedEvenDefectEndpoint
  rw [etaPairBaseRotation_conj,
    etaCriticalMirrorIndexNormalizedEvenDefectEndpoint_conj]
  simp

/-- The explicit normalized half-tail constant is real and conjugation invariant. -/
theorem etaPairIndexNormalizedTailConstant_conj
    (z : ℂ) :
    etaPairIndexNormalizedTailConstant (conj z) =
      conj (etaPairIndexNormalizedTailConstant z) := by
  norm_num [etaPairIndexNormalizedTailConstant]
  left
  norm_num [starRingEnd_apply]

/-- Conjugation transports every rotating endpoint limit to the conjugate limit. -/
theorem etaCriticalMirrorIndexNormalizedRotatedEvenDefectEndpoint_conj_tendsto
    {a : ℝ} {s C : ℂ}
    (hendpoint :
      Tendsto
        (etaCriticalMirrorIndexNormalizedRotatedEvenDefectEndpoint a s)
        atTop (nhds C)) :
    Tendsto
      (etaCriticalMirrorIndexNormalizedRotatedEvenDefectEndpoint
        a (conj s))
      atTop (nhds (conj C)) := by
  have hconj := (Complex.continuous_conj.tendsto C).comp hendpoint
  refine hconj.congr' (Eventually.of_forall fun k => ?_)
  exact
    (etaCriticalMirrorIndexNormalizedRotatedEvenDefectEndpoint_conj
      a s k).symm

/--
Certificate showing that conjugate endpoint asymptotics are exact conjugate
partners, not competing limits of one sequence.
-/
structure EtaCriticalMirrorEndpointConjugationAsymptoticCompatibilityCertificate
    (a : ℝ) (s C : ℂ) : Prop where
  original_endpoint_tendsto :
    Tendsto
      (etaCriticalMirrorIndexNormalizedRotatedEvenDefectEndpoint a s)
      atTop (nhds C)
  conjugate_endpoint_tendsto :
    Tendsto
      (etaCriticalMirrorIndexNormalizedRotatedEvenDefectEndpoint
        a (conj s))
      atTop (nhds (conj C))
  exact_conjugation :
    ∀ k : ℕ,
      etaCriticalMirrorIndexNormalizedRotatedEvenDefectEndpoint
          a (conj s) k =
        conj
          (etaCriticalMirrorIndexNormalizedRotatedEvenDefectEndpoint a s k)

/-- Build the conjugation compatibility certificate from either endpoint limit. -/
theorem etaCriticalMirrorEndpointConjugationAsymptoticCompatibilityCertificate_of_limit
    {a : ℝ} {s C : ℂ}
    (hendpoint :
      Tendsto
        (etaCriticalMirrorIndexNormalizedRotatedEvenDefectEndpoint a s)
        atTop (nhds C)) :
    EtaCriticalMirrorEndpointConjugationAsymptoticCompatibilityCertificate
      a s C :=
  { original_endpoint_tendsto := hendpoint
    conjugate_endpoint_tendsto :=
      etaCriticalMirrorIndexNormalizedRotatedEvenDefectEndpoint_conj_tendsto
        hendpoint
    exact_conjugation :=
      etaCriticalMirrorIndexNormalizedRotatedEvenDefectEndpoint_conj a s }

/-- Right-side off-critical endpoint asymptotics are conjugation compatible. -/
theorem etaCriticalMirrorRightEndpointConjugationAsymptoticCompatibilityCertificate_of_zero
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : (1 : ℝ) / 2 < s.re) :
    EtaCriticalMirrorEndpointConjugationAsymptoticCompatibilityCertificate
      (criticalMirror s).re s
      (-etaPairIndexNormalizedTailConstant (criticalMirror s)) := by
  apply
    etaCriticalMirrorEndpointConjugationAsymptoticCompatibilityCertificate_of_limit
  exact
    (etaCriticalMirrorRightNormalizedEvenDefectEndpointAsymptoticCertificate_of_zero
      hs him hre).rotated_endpoint_tendsto

/-- Left-side off-critical endpoint asymptotics are conjugation compatible. -/
theorem etaCriticalMirrorLeftEndpointConjugationAsymptoticCompatibilityCertificate_of_zero
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : s.re < (1 : ℝ) / 2) :
    EtaCriticalMirrorEndpointConjugationAsymptoticCompatibilityCertificate
      s.re s (etaPairIndexNormalizedTailConstant s) := by
  apply
    etaCriticalMirrorEndpointConjugationAsymptoticCompatibilityCertificate_of_limit
  simpa only [neg_neg] using
    (etaCriticalMirrorLeftNormalizedEvenDefectEndpointAsymptoticCertificate_of_zero
      hs him hre).rotated_endpoint_tendsto

end DkMath.RH.CFBRCProjection
