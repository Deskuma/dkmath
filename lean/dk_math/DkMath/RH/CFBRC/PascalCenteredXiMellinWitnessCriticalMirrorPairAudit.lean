/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.PascalCriticalMirrorZeroWindowEnergyBridge
import DkMath.RH.CFBRC.PascalCenteredXiMellinWitnessShiftedEnergyDominanceAudit
import Mathlib.Tactic

/-!
# GWSS-003H: critical-mirror pair feasibility

This module records the finite part of the critical-mirror audit.  In the
centered coordinate the project-level mirror is `z ↦ -conj z`; it preserves
the actual Xi disk and sends a squared orbit to its conjugate.  The resulting
`Fin`-index statement is existential, because the actual orbit carrier is
enumerated by an arbitrary finite equivalence.

The mass used by the Mellin witness is multiplicity-weighted.  The current
API proves closure of the filtered zero fibres but does not yet transport
`pascalCenteredXiZeroMultiplicity` through the mirror.  Consequently this
file deliberately stops before asserting a mirror mass equality, an extractor
row relation, or shifted-energy oddness.  The final theorem is only the
ordered-algebra implication “paired P1 plus oddness implies P2 equality”; it
is not a positivity provider.

No limit exchange, RH assumption, classical Guinand--Weil theorem, or new
source-rank claim is introduced here.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open scoped ComplexConjugate

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

/-! ## H4 boundary: multiplicity-weighted mass -/

/-
The current mass API is weighted by `pascalCenteredXiZeroMultiplicity`.
The preceding fibre theorem only transports the underlying finite carrier.
An equality of the two weighted masses therefore requires the missing
theorem
`pascalCenteredXiZeroMultiplicity (pascalCenteredXiCriticalMirror z) =
 pascalCenteredXiZeroMultiplicity z` on actual zeros.  It is intentionally
not postulated in this module.
-/

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
