/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorWeightPressure
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.EtaCriticalMirrorPhaseProjection"

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open scoped Topology

/-- One term of the critical-mirror weighted-minus-unweighted defect. -/
noncomputable def etaCriticalMirrorDefectTerm
    (s : ℂ) (m : ℕ) : ℂ :=
  (etaCriticalMirrorTermWeight s m - 1) * etaSignedVector s m

/-- Real projection of one defect term after one common complex rotation. -/
noncomputable def etaCriticalMirrorProjectedDefectTerm
    (ω s : ℂ) (m : ℕ) : ℝ :=
  (ω * etaCriticalMirrorDefectTerm s m).re

/-- Real projection of the finite critical-mirror transport defect endpoint. -/
noncomputable def etaCriticalMirrorProjectedDefectEndpoint
    (N : ℕ) (ω s : ℂ) : ℝ :=
  (ω * etaCriticalMirrorTransportDefectEndpoint N s).re

/-- The complex transport defect is the finite sum of its defect terms. -/
theorem etaCriticalMirrorTransportDefectEndpoint_eq_sum_defectTerm
    (N : ℕ) (s : ℂ) :
    etaCriticalMirrorTransportDefectEndpoint N s =
      (Finset.range N).sum (etaCriticalMirrorDefectTerm s) := by
  simpa [etaCriticalMirrorDefectTerm] using
    etaCriticalMirrorTransportDefectEndpoint_eq_sum N s

/-- Common rotation and real projection commute with the finite defect sum. -/
theorem etaCriticalMirrorProjectedDefectEndpoint_eq_sum
    (N : ℕ) (ω s : ℂ) :
    etaCriticalMirrorProjectedDefectEndpoint N ω s =
      (Finset.range N).sum
        (etaCriticalMirrorProjectedDefectTerm ω s) := by
  unfold etaCriticalMirrorProjectedDefectEndpoint
  rw [etaCriticalMirrorTransportDefectEndpoint_eq_sum_defectTerm]
  rw [Finset.mul_sum]
  simp [etaCriticalMirrorProjectedDefectTerm]

/-- Adding one index appends exactly one projected defect term. -/
theorem etaCriticalMirrorProjectedDefectEndpoint_succ
    (N : ℕ) (ω s : ℂ) :
    etaCriticalMirrorProjectedDefectEndpoint (N + 1) ω s =
      etaCriticalMirrorProjectedDefectEndpoint N ω s +
        etaCriticalMirrorProjectedDefectTerm ω s N := by
  rw [etaCriticalMirrorProjectedDefectEndpoint_eq_sum,
    etaCriticalMirrorProjectedDefectEndpoint_eq_sum,
    Finset.sum_range_succ]

/--
A common-half-plane certificate for the projected defect terms.

Every projected term lies in the closed positive half-line and at least one
term lies in its interior.  This is the exact phase-separation input needed to
prevent cancellation of the one-sided mirror-weight pressure.
-/
structure EtaCriticalMirrorDefectHalfPlaneCertificate (s : ℂ) : Prop where
  rotation : ℂ
  nonnegative :
    ∀ m : ℕ, 0 ≤ etaCriticalMirrorProjectedDefectTerm rotation s m
  positive :
    ∃ m : ℕ, 0 < etaCriticalMirrorProjectedDefectTerm rotation s m

/-- A half-plane certificate gives an eventual strictly positive lower bound. -/
theorem EtaCriticalMirrorDefectHalfPlaneCertificate.eventually_pos_lowerBound
    {s : ℂ} (cert : EtaCriticalMirrorDefectHalfPlaneCertificate s) :
    ∃ c : ℝ, 0 < c ∧
      ∀ᶠ N : ℕ in atTop,
        c ≤ etaCriticalMirrorProjectedDefectEndpoint N cert.rotation s := by
  rcases cert.positive with ⟨m, hm⟩
  refine ⟨etaCriticalMirrorProjectedDefectTerm cert.rotation s m, hm, ?_⟩
  refine eventually_atTop.2 ⟨m + 1, ?_⟩
  intro N hN
  rw [etaCriticalMirrorProjectedDefectEndpoint_eq_sum]
  apply Finset.single_le_sum
  · intro i hi
    exact cert.nonnegative i
  · exact Finset.mem_range.mpr (by omega)

/--
A projected defect whose terms admit a common-half-plane certificate cannot
converge to zero.
-/
theorem not_tendsto_etaCriticalMirrorProjectedDefectEndpoint_zero_of_halfPlane
    {s : ℂ} (cert : EtaCriticalMirrorDefectHalfPlaneCertificate s) :
    ¬ Tendsto
      (fun N : ℕ =>
        etaCriticalMirrorProjectedDefectEndpoint N cert.rotation s)
      atTop (nhds 0) := by
  intro hzero
  rcases cert.eventually_pos_lowerBound with ⟨c, hc, hLower⟩
  have hle : c ≤ (0 : ℝ) :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hzero hLower
  exact (not_le_of_gt hc) hle

/--
Every fixed real projection of the complex transport defect tends to zero at a
nonreal nontrivial zeta zero.
-/
theorem etaCriticalMirrorProjectedDefectEndpoint_tendsto_zero_of_nontrivialRiemannZetaZero
    {s ω : ℂ} (hs : NontrivialRiemannZetaZero s) (him : s.im ≠ 0) :
    Tendsto
      (fun N : ℕ => etaCriticalMirrorProjectedDefectEndpoint N ω s)
      atTop (nhds 0) := by
  have hdefect :=
    etaCriticalMirrorTransportDefectEndpoint_tendsto_zero_of_nontrivialRiemannZetaZero
      hs him
  have hω : Tendsto (fun _ : ℕ => ω) atTop (nhds ω) :=
    tendsto_const_nhds
  have hmul :
      Tendsto
        (fun N : ℕ =>
          ω * etaCriticalMirrorTransportDefectEndpoint N s)
        atTop (nhds (ω * 0)) :=
    hω.mul hdefect
  have hre := Complex.continuous_re.tendsto (ω * 0)
  simpa [etaCriticalMirrorProjectedDefectEndpoint] using hre.comp hmul

/--
A nonreal nontrivial zeta zero cannot carry a common-half-plane defect
certificate: the certificate forces a positive lower bound, while the
completed-zeta mirror relation forces the projected defect to vanish.
-/
theorem not_etaCriticalMirrorDefectHalfPlaneCertificate_of_nontrivialRiemannZetaZero
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) (him : s.im ≠ 0) :
    ¬ EtaCriticalMirrorDefectHalfPlaneCertificate s := by
  intro cert
  exact
    not_tendsto_etaCriticalMirrorProjectedDefectEndpoint_zero_of_halfPlane cert
      (etaCriticalMirrorProjectedDefectEndpoint_tendsto_zero_of_nontrivialRiemannZetaZero
        hs him)

/--
Minimal off-critical phase-separation obligation.  It asserts only that an
off-critical point supplies one common-half-plane certificate for its defect
terms; it does not assume the critical-line conclusion.
-/
def EtaCriticalMirrorOffCriticalHalfPlaneSeparation (s : ℂ) : Prop :=
  s.re ≠ (1 : ℝ) / 2 → EtaCriticalMirrorDefectHalfPlaneCertificate s

/--
At a nonreal nontrivial zero, the minimal off-critical phase-separation law
forces the real part onto the critical line.
-/
theorem re_eq_half_of_nontrivialRiemannZetaZero_of_offCriticalHalfPlaneSeparation
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) (him : s.im ≠ 0)
    (hsep : EtaCriticalMirrorOffCriticalHalfPlaneSeparation s) :
    s.re = (1 : ℝ) / 2 := by
  by_contra hre
  exact
    (not_etaCriticalMirrorDefectHalfPlaneCertificate_of_nontrivialRiemannZetaZero
      hs him) (hsep hre)

/-- The phase-separation law maps a nonreal nontrivial zero into positive-degree CFBRC closure. -/
theorem offCriticalCFBRC_eq_zero_of_nontrivialRiemannZetaZero_of_offCriticalHalfPlaneSeparation
    {d : ℕ} (hd : 0 < d) {s : ℂ} (Θ : ℝ)
    (hs : NontrivialRiemannZetaZero s) (him : s.im ≠ 0)
    (hsep : EtaCriticalMirrorOffCriticalHalfPlaneSeparation s) :
    offCriticalCFBRC d s.re Θ = 0 := by
  apply (offCriticalCFBRC_eq_zero_iff_re_eq_half hd s.re Θ).2
  exact
    re_eq_half_of_nontrivialRiemannZetaZero_of_offCriticalHalfPlaneSeparation
      hs him hsep

end DkMath.RH.CFBRCProjection
