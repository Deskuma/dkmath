/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.PascalCriticalMirrorZeroWindowEnergyBridge
import DkMath.RH.CFBRC.PascalCenteredXiMellinWitnessShiftedEnergyDominanceAudit
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Tactic

/-!
# GWSS-003H: critical-mirror pair feasibility

This module records the finite part of the critical-mirror audit.  In the
centered coordinate the project-level mirror is `z ↦ -conj z`; it preserves
the actual Xi disk and sends a squared orbit to its conjugate.  The resulting
`Fin`-index statement is existential, because the actual orbit carrier is
enumerated by an arbitrary finite equivalence.

The mass used by the Mellin witness is multiplicity-weighted.  This module
proves its transport through conjugation and, consequently, through the
centered critical mirror.  It also records the induced finite mass-vector
transport.  The audit deliberately stops before asserting an extractor row
relation, shifted-energy oddness, or any analytic source estimate.  The final
theorem is only the ordered-algebra implication “paired P1 plus oddness implies
P2 equality”; it is not a positivity provider.

No limit exchange, RH assumption, classical Guinand--Weil theorem, or new
source-rank claim is introduced here.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open scoped ComplexConjugate
open scoped Topology

/-! ## H1: centered critical-mirror geometry -/

/-- The critical mirror written in the centered Xi coordinate. -/
noncomputable def pascalCenteredXiCriticalMirror (z : ℂ) : ℂ :=
  -conj z

/-- The centered mirror is the translated form of `criticalMirror`. -/
theorem pascalCenteredXiCriticalMirror_eq_centeredCriticalMirror (z : ℂ) :
    pascalCenteredXiCriticalMirror z =
      pascalCenterZeroShift
        (criticalMirror (pascalUncenterZeroShift z)) := by
  apply Complex.ext <;> simp [pascalCenteredXiCriticalMirror,
    pascalCenterZeroShift, pascalUncenterZeroShift, criticalMirror,
    criticalLineCenter]
  all_goals linarith

/-- Squaring the centered mirror is complex conjugation of the square. -/
theorem pascalCenteredXiCriticalMirror_sq (z : ℂ) :
    pascalCenteredXiCriticalMirror z ^ 2 = conj (z ^ 2) := by
  apply Complex.ext <;>
    simp [pascalCenteredXiCriticalMirror, pow_two, Complex.mul_re,
      Complex.mul_im]

@[simp] theorem pascalCenteredXiCriticalMirror_sq_re (z : ℂ) :
    (pascalCenteredXiCriticalMirror z ^ 2).re = (z ^ 2).re := by
  simpa only [Complex.conj_re] using
    congrArg Complex.re (pascalCenteredXiCriticalMirror_sq z)

@[simp] theorem pascalCenteredXiCriticalMirror_sq_im (z : ℂ) :
    (pascalCenteredXiCriticalMirror z ^ 2).im = -(z ^ 2).im := by
  simpa only [Complex.conj_im] using
    congrArg Complex.im (pascalCenteredXiCriticalMirror_sq z)

/-! ## H2: actual finite zero-window closure -/

private theorem pascalCenteredXiCriticalMirror_uncenter_eq
    (z : ℂ) :
    pascalUncenterZeroShift (pascalCenteredXiCriticalMirror z) =
      criticalMirror (pascalUncenterZeroShift z) := by
  rw [pascalCenteredXiCriticalMirror_eq_centeredCriticalMirror]
  simp [pascalUncenterZeroShift, pascalCenterZeroShift]

/-- The centered mirror preserves membership in the actual finite Xi disk. -/
theorem pascalCenteredXiCriticalMirror_mem_zeroDiskFinset_iff
    {R : ℝ} {z : ℂ} :
    pascalCenteredXiCriticalMirror z ∈ pascalCenteredXiZeroDiskFinset R ↔
      z ∈ pascalCenteredXiZeroDiskFinset R := by
  rw [mem_pascalCenteredXiZeroDiskFinset_iff,
    mem_pascalCenteredXiZeroDiskFinset_iff]
  constructor
  · rintro ⟨hmBall, hmZero⟩
    refine ⟨?_, ?_⟩
    · simpa [pascalCenteredXiCriticalMirror, dist_eq_norm] using hmBall
    · rw [mem_pascalCenteredXiZeros_iff_nontrivial_shift] at hmZero ⊢
      change NontrivialRiemannZetaZero
        (pascalUncenterZeroShift (pascalCenteredXiCriticalMirror z)) at hmZero
      change NontrivialRiemannZetaZero (pascalUncenterZeroShift z)
      rw [pascalCenteredXiCriticalMirror_uncenter_eq] at hmZero
      simpa only [criticalMirror_involutive] using
        criticalMirror_nontrivialRiemannZetaZero hmZero
  · rintro ⟨hBall, hZero⟩
    refine ⟨?_, ?_⟩
    · simpa [pascalCenteredXiCriticalMirror, dist_eq_norm] using hBall
    · rw [mem_pascalCenteredXiZeros_iff_nontrivial_shift] at hZero ⊢
      change NontrivialRiemannZetaZero (pascalUncenterZeroShift z) at hZero
      change NontrivialRiemannZetaZero
        (pascalUncenterZeroShift (pascalCenteredXiCriticalMirror z))
      rw [pascalCenteredXiCriticalMirror_uncenter_eq]
      exact criticalMirror_nontrivialRiemannZetaZero hZero

/-- The centered mirror is an involution. -/
theorem pascalCenteredXiCriticalMirror_involutive (z : ℂ) :
    pascalCenteredXiCriticalMirror
        (pascalCenteredXiCriticalMirror z) = z := by
  simp [pascalCenteredXiCriticalMirror]

/-! ## H3: squared-orbit closure and finite reindexing -/

/-- Conjugation preserves the occupied squared-orbit carrier. -/
theorem conj_mem_pascalCenteredXiSquaredOrbitFinset_iff
    {R : ℝ} {q : ℂ} :
    conj q ∈ pascalCenteredXiSquaredOrbitFinset R ↔
      q ∈ pascalCenteredXiSquaredOrbitFinset R := by
  constructor
  · intro hq
    rcases (mem_pascalCenteredXiSquaredOrbitFinset_iff.mp hq) with
      ⟨z, hz, hzq⟩
    refine mem_pascalCenteredXiSquaredOrbitFinset_iff.mpr
      ⟨pascalCenteredXiCriticalMirror z,
        (pascalCenteredXiCriticalMirror_mem_zeroDiskFinset_iff).mpr hz, ?_⟩
    rw [pascalCenteredXiCriticalMirror_sq, hzq]
    simp only [starRingEnd_apply, star_star]
  · intro hq
    rcases (mem_pascalCenteredXiSquaredOrbitFinset_iff.mp hq) with
      ⟨z, hz, hzq⟩
    refine mem_pascalCenteredXiSquaredOrbitFinset_iff.mpr
      ⟨pascalCenteredXiCriticalMirror z,
        (pascalCenteredXiCriticalMirror_mem_zeroDiskFinset_iff).mpr hz, ?_⟩
    rw [pascalCenteredXiCriticalMirror_sq, hzq]

/-- Every finite orbit coordinate has an existential conjugate coordinate. -/
theorem exists_pascalCenteredXiSquaredOrbitMirrorIndex
    (R : ℝ) (j : Fin (pascalCenteredXiSquaredOrbitIndexCard R)) :
    ∃ jMirror,
      pascalCenteredXiSquaredOrbitCoordinate R jMirror =
        conj (pascalCenteredXiSquaredOrbitCoordinate R j) := by
  have hj : pascalCenteredXiSquaredOrbitCoordinate R j ∈
      pascalCenteredXiSquaredOrbitFinset R :=
    pascalCenteredXiSquaredOrbitCoordinate_mem R j
  have hmirror := (conj_mem_pascalCenteredXiSquaredOrbitFinset_iff).mpr hj
  obtain ⟨jMirror, hjMirror⟩ :=
    exists_pascalCenteredXiSquaredOrbitCoordinate_eq R
      ⟨conj (pascalCenteredXiSquaredOrbitCoordinate R j), hmirror⟩
  exact ⟨jMirror, hjMirror⟩

/-! ## H3.5: filtered fibre closure before multiplicity transport -/

/-- The centered mirror maps the filtered `q`-fibre to the filtered
`conj q`-fibre.  This is a set-level statement; it does not identify the
analytic multiplicity attached to corresponding zeros. -/
theorem image_pascalCenteredXiCriticalMirror_filter_sq
    (R : ℝ) (q : ℂ) :
    ((pascalCenteredXiZeroDiskFinset R).filter (fun z => z ^ 2 = q)).image
        pascalCenteredXiCriticalMirror =
      (pascalCenteredXiZeroDiskFinset R).filter
        (fun z => z ^ 2 = conj q) := by
  classical
  ext z
  constructor
  · intro hz
    rcases Finset.mem_image.mp hz with ⟨w, hw, hwm⟩
    rw [← hwm]
    refine Finset.mem_filter.mpr ⟨
      (pascalCenteredXiCriticalMirror_mem_zeroDiskFinset_iff).mpr
        (Finset.mem_filter.mp hw).1, ?_⟩
    rw [pascalCenteredXiCriticalMirror_sq]
    exact congrArg conj (Finset.mem_filter.mp hw).2
  · intro hz
    refine Finset.mem_image.mpr ⟨pascalCenteredXiCriticalMirror z, ?_,
      pascalCenteredXiCriticalMirror_involutive z⟩
    refine Finset.mem_filter.mpr ⟨
      (pascalCenteredXiCriticalMirror_mem_zeroDiskFinset_iff).mpr
        (Finset.mem_filter.mp hz).1, ?_⟩
    rw [pascalCenteredXiCriticalMirror_sq]
    simpa using congrArg conj (Finset.mem_filter.mp hz).2

/-! ## H4a: multiplicity transport -/

private theorem pascalCenteredXiZeroMultiplicity_conj
    {z : ℂ} (hz : z ∈ pascalCenteredXiZeros) :
    pascalCenteredXiZeroMultiplicity (conj z) =
      pascalCenteredXiZeroMultiplicity z := by
  obtain ⟨g, hg, hg0, hfactor⟩ :=
    exists_pascalCenteredXi_local_factorization hz
  let G : ℂ → ℂ := fun w =>
    conj (pascalCenteredRiemannXiKernel (conj w))
  let gs : ℂ → ℂ := fun w => conj (g (conj w))
  have hconj_tendsto :
      Filter.Tendsto (fun w : ℂ => conj w) (𝓝 (conj z)) (𝓝 z) := by
    have hconj : ContinuousAt (fun w : ℂ => conj w) (conj z) :=
      Complex.continuous_conj.continuousAt
    change Filter.Tendsto (fun w : ℂ => conj w)
      (𝓝 (conj z)) (𝓝 (conj (conj z))) at hconj
    simpa only [starRingEnd_apply, star_star] using hconj
  have hfactor_conj :
      ∀ᶠ w : ℂ in 𝓝 (conj z),
        G w = (w - conj z) ^ pascalCenteredXiZeroMultiplicity z * gs w := by
    have hfactor' := hfactor.comp_tendsto hconj_tendsto
    filter_upwards [hfactor'] with w hw
    change pascalCenteredRiemannXiKernel (conj w) =
      (conj w - z) ^ pascalCenteredXiZeroMultiplicity z * g (conj w) at hw
    change conj (pascalCenteredRiemannXiKernel (conj w)) = _
    rw [hw]
    simp only [map_mul, map_pow, map_sub, starRingEnd_apply, star_star, gs]
  have hG : AnalyticAt ℂ G (conj z) := by
    have hGdiff : Differentiable ℂ G := by
      intro w
      change DifferentiableAt ℂ
        (conj ∘ pascalCenteredRiemannXiKernel ∘ conj) w
      apply differentiableAt_conj_conj_iff.mpr
      exact differentiable_pascalCenteredRiemannXiKernel (conj w)
    exact hGdiff.analyticAt (conj z)
  have hgs : AnalyticAt ℂ gs (conj z) := by
    obtain ⟨p, hp⟩ := hg
    obtain ⟨r, hr⟩ := hp
    have hgsdiff : DifferentiableOn ℂ gs (Metric.eball (conj z) r) := by
      intro w hw
      have hw' : conj w ∈ Metric.eball z r := by
        rw [Metric.mem_eball, edist_eq_enorm_sub] at hw ⊢
        calc
          ‖conj w - z‖ₑ = ‖conj (w - conj z)‖ₑ := by
            rw [map_sub]
            simp only [starRingEnd_apply, star_star]
          _ = ‖w - conj z‖ₑ := RCLike.enorm_conj _
          _ < r := hw
      have hlocal := hr.analyticAt_of_mem hw'
      have hlocal' := differentiableAt_conj_conj_iff.mpr hlocal.differentiableAt
      simpa [gs, Function.comp_def] using hlocal'.differentiableWithinAt
    exact (hgsdiff.analyticOnNhd Metric.isOpen_eball)
      (conj z) (Metric.mem_eball_self hr.r_pos)
  have hgs0 : gs (conj z) ≠ 0 := by
    intro hzero
    apply hg0
    have hzero' := congrArg conj hzero
    simpa only [gs, starRingEnd_apply, star_star, map_zero] using hzero'
  have hGorder :
      analyticOrderAt G (conj z) =
        (pascalCenteredXiZeroMultiplicity z : ℕ∞) :=
    hG.analyticOrderAt_eq_natCast.mpr ⟨gs, hgs, hgs0, hfactor_conj⟩
  have hG_eq : G = pascalCenteredRiemannXiKernel := by
    funext w
    dsimp [G]
    have h := pascalCenteredRiemannXiKernel_conj w
    have h' := congrArg conj h
    simpa only [starRingEnd_apply, star_star] using h'
  have hzorder :
      analyticOrderAt pascalCenteredRiemannXiKernel z =
        (pascalCenteredXiZeroMultiplicity z : ℕ∞) :=
    analyticOrderAt_pascalCenteredXi_eq_multiplicity hz
  have hconjzero : conj z ∈ pascalCenteredXiZeros := by
    rw [mem_pascalCenteredXiZeros, pascalCenteredRiemannXiKernel_conj]
    calc
      conj (pascalCenteredRiemannXiKernel z) = conj 0 :=
        congrArg conj (mem_pascalCenteredXiZeros.mp hz)
      _ = 0 := map_zero (starRingEnd ℂ)
  have hconj_order :
      analyticOrderAt pascalCenteredRiemannXiKernel (conj z) =
        analyticOrderAt pascalCenteredRiemannXiKernel z := by
    calc
      analyticOrderAt pascalCenteredRiemannXiKernel (conj z) =
          analyticOrderAt G (conj z) := by rw [hG_eq]
      _ = (pascalCenteredXiZeroMultiplicity z : ℕ∞) := hGorder
      _ = analyticOrderAt pascalCenteredRiemannXiKernel z := hzorder.symm
  have hmult :
      (pascalCenteredXiZeroMultiplicity (conj z) : ℕ∞) =
        (pascalCenteredXiZeroMultiplicity z : ℕ∞) := by
    calc
      (pascalCenteredXiZeroMultiplicity (conj z) : ℕ∞) =
          analyticOrderAt pascalCenteredRiemannXiKernel (conj z) :=
        (analyticOrderAt_pascalCenteredXi_eq_multiplicity hconjzero).symm
      _ = analyticOrderAt pascalCenteredRiemannXiKernel z := hconj_order
      _ = (pascalCenteredXiZeroMultiplicity z : ℕ∞) := hzorder
  exact_mod_cast hmult

private theorem pascalCenteredXiZeroMultiplicity_neg
    {z : ℂ} (hz : z ∈ pascalCenteredXiZeros) :
    pascalCenteredXiZeroMultiplicity (-z) =
      pascalCenteredXiZeroMultiplicity z := by
  have hneg : AnalyticAt ℂ (fun w : ℂ => -w) z := by fun_prop
  have hneg' : deriv (fun w : ℂ => -w) z ≠ 0 := by simp
  have hcomp := analyticOrderAt_comp_of_deriv_ne_zero
    (f := pascalCenteredRiemannXiKernel) (z₀ := z) hneg hneg'
  have heven :
      pascalCenteredRiemannXiKernel ∘ (fun w : ℂ => -w) =
        pascalCenteredRiemannXiKernel := by
    funext w
    simp only [Function.comp_apply, pascalCenteredRiemannXiKernel_neg]
  have horder :
      analyticOrderAt pascalCenteredRiemannXiKernel (-z) =
        analyticOrderAt pascalCenteredRiemannXiKernel z := by
    calc
      analyticOrderAt pascalCenteredRiemannXiKernel (-z) =
          analyticOrderAt
            (pascalCenteredRiemannXiKernel ∘ (fun w : ℂ => -w)) z :=
        hcomp.symm
      _ = analyticOrderAt pascalCenteredRiemannXiKernel z := by rw [heven]
  have hmz : -z ∈ pascalCenteredXiZeros := by
    rw [mem_pascalCenteredXiZeros, pascalCenteredRiemannXiKernel_neg]
    exact mem_pascalCenteredXiZeros.mp hz
  have hmzorder := analyticOrderAt_pascalCenteredXi_eq_multiplicity hmz
  have hzorder := analyticOrderAt_pascalCenteredXi_eq_multiplicity hz
  have hmult :
      (pascalCenteredXiZeroMultiplicity (-z) : ℕ∞) =
        (pascalCenteredXiZeroMultiplicity z : ℕ∞) := by
    exact hmzorder.symm.trans (horder.trans hzorder)
  exact_mod_cast hmult

/-- Critical-mirror transport preserves arbitrary Xi-zero multiplicity. -/
theorem pascalCenteredXiZeroMultiplicity_criticalMirror
    {z : ℂ} (hz : z ∈ pascalCenteredXiZeros) :
    pascalCenteredXiZeroMultiplicity (pascalCenteredXiCriticalMirror z) =
      pascalCenteredXiZeroMultiplicity z := by
  have hconjzero : conj z ∈ pascalCenteredXiZeros := by
    rw [mem_pascalCenteredXiZeros, pascalCenteredRiemannXiKernel_conj]
    calc
      conj (pascalCenteredRiemannXiKernel z) = conj 0 :=
        congrArg conj (mem_pascalCenteredXiZeros.mp hz)
      _ = 0 := map_zero (starRingEnd ℂ)
  rw [pascalCenteredXiCriticalMirror]
  rw [pascalCenteredXiZeroMultiplicity_neg hconjzero]
  exact pascalCenteredXiZeroMultiplicity_conj hz

/-! ## H4b: multiplicity-weighted orbit mass -/

/-- The multiplicity-weighted squared-orbit mass is invariant under conjugation. -/
theorem pascalCenteredXiSquaredOrbitMass_conj (R : ℝ) (q : ℂ) :
    pascalCenteredXiSquaredOrbitMass R (conj q) =
      pascalCenteredXiSquaredOrbitMass R q := by
  classical
  let S := (pascalCenteredXiZeroDiskFinset R).filter
    (fun z => z ^ 2 = q)
  have himage : S.image pascalCenteredXiCriticalMirror =
      (pascalCenteredXiZeroDiskFinset R).filter
        (fun z => z ^ 2 = conj q) := by
    simpa [S] using image_pascalCenteredXiCriticalMirror_filter_sq R q
  have hinj : Function.Injective pascalCenteredXiCriticalMirror := by
    intro a b hab
    rw [← pascalCenteredXiCriticalMirror_involutive a,
      ← pascalCenteredXiCriticalMirror_involutive b, hab]
  simp only [pascalCenteredXiSquaredOrbitMass]
  rw [← himage, Finset.sum_image hinj.injOn]
  apply Finset.sum_congr rfl
  intro z hz
  have hzmem : z ∈ pascalCenteredXiZeroDiskFinset R :=
    (Finset.mem_filter.mp hz).1
  have hzzero : z ∈ pascalCenteredXiZeros :=
    (mem_pascalCenteredXiZeroDiskFinset_iff.mp hzmem).2
  rw [pascalCenteredXiZeroMultiplicity_criticalMirror hzzero]

/-! ## H4c: finite mass-vector transport -/

/-- A conjugate orbit coordinate has the same multiplicity-weighted mass. -/
theorem exists_pascalCenteredXiSquaredOrbitMirrorIndex_with_mass
    (R : ℝ) (j : Fin (pascalCenteredXiSquaredOrbitIndexCard R)) :
    ∃ jMirror,
      pascalCenteredXiSquaredOrbitCoordinate R jMirror =
        conj (pascalCenteredXiSquaredOrbitCoordinate R j) ∧
      pascalCenteredXiSquaredOrbitMassVec R jMirror =
        pascalCenteredXiSquaredOrbitMassVec R j := by
  obtain ⟨jMirror, hjMirror⟩ :=
    exists_pascalCenteredXiSquaredOrbitMirrorIndex R j
  refine ⟨jMirror, hjMirror, ?_⟩
  simp only [pascalCenteredXiSquaredOrbitMassVec, hjMirror]
  exact pascalCenteredXiSquaredOrbitMass_conj R _

/-! ## H8: conditional paired P1 implies P2 -/

/-- Oddness plus the two paired P1 inequalities forces equality of the pair. -/
theorem paired_shifted_difference_odd_forces_P2_equality
    {d dMirror ePlus eMinus ePlusMirror eMinusMirror : ℝ}
    (hodd : dMirror = -d)
    (hd : d = ePlus - eMinus)
    (hdMirror : dMirror = ePlusMirror - eMinusMirror)
    (hP1 : eMinus ≤ ePlus)
    (hP1Mirror : eMinusMirror ≤ ePlusMirror) :
    ePlus = eMinus := by
  rw [hd] at hodd
  rw [hdMirror] at hodd
  linarith

end DkMath.RH.CFBRCProjection
