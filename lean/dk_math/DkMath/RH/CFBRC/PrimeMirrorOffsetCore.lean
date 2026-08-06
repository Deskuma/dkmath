/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.CosmicFormula.Rotation.CF2D.ThreeElementBridge
import DkMath.RH.CFBRC.OffCriticalExclusion
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.PrimeMirrorOffsetCore"

/-!
# Prime-mirror offset Core

This module isolates the horizontal critical-line offset in one positive-base
mode.  The construction is independent of zeta zeros, eta limits, infinite
series, and RH.

For a positive integer mode `n` and a real offset `δ`, the two mirror
amplitudes are

`exp (-δ * log n)` and `exp (δ * log n)`.

Their product is exactly one.  Hence their CF2D three-element interaction is
exactly two, while the difference whole is the nonnegative mirror-offset Gap.
For `1 < n`, that Gap vanishes exactly when `δ = 0`.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open DkMath.CosmicFormula.ThreeElement
open DkMath.CosmicFormula.Rotation.CF2D

/-- The left critical-mirror amplitude of one positive-base mode. -/
noncomputable def primeMirrorLeftAmplitude (n : ℕ) (δ : ℝ) : ℝ :=
  Real.exp (-δ * Real.log (n : ℝ))

/-- The right critical-mirror amplitude of one positive-base mode. -/
noncomputable def primeMirrorRightAmplitude (n : ℕ) (δ : ℝ) : ℝ :=
  Real.exp (δ * Real.log (n : ℝ))

/-- The squared difference of the two mirror amplitudes. -/
noncomputable def primeMirrorOffsetGap (n : ℕ) (δ : ℝ) : ℝ :=
  (primeMirrorLeftAmplitude n δ - primeMirrorRightAmplitude n δ) ^ 2

/-- Read the mirror-amplitude pair as one CF2D state. -/
noncomputable def primeMirrorOffsetState (n : ℕ) (δ : ℝ) : Vec ℝ :=
  ⟨primeMirrorLeftAmplitude n δ, primeMirrorRightAmplitude n δ⟩

/-- Specialize the mirror-offset Gap to the centered real coordinate of `s`. -/
noncomputable def primeMirrorOffsetGapAt (n : ℕ) (s : ℂ) : ℝ :=
  primeMirrorOffsetGap n (centeredSigma s.re)

/-- Specialize the mirror-amplitude state to the centered real coordinate of `s`. -/
noncomputable def primeMirrorOffsetStateAt (n : ℕ) (s : ℂ) : Vec ℝ :=
  primeMirrorOffsetState n (centeredSigma s.re)

@[simp]
theorem primeMirrorOffsetState_core (n : ℕ) (δ : ℝ) :
    (primeMirrorOffsetState n δ).core = primeMirrorLeftAmplitude n δ :=
  rfl

@[simp]
theorem primeMirrorOffsetState_beam (n : ℕ) (δ : ℝ) :
    (primeMirrorOffsetState n δ).beam = primeMirrorRightAmplitude n δ :=
  rfl

/-- Both mirror amplitudes are strictly positive. -/
theorem primeMirrorLeftAmplitude_pos (n : ℕ) (δ : ℝ) :
    0 < primeMirrorLeftAmplitude n δ := by
  exact Real.exp_pos _

/-- Both mirror amplitudes are strictly positive. -/
theorem primeMirrorRightAmplitude_pos (n : ℕ) (δ : ℝ) :
    0 < primeMirrorRightAmplitude n δ := by
  exact Real.exp_pos _

/-- The two mirror amplitudes multiply to one for every real offset. -/
theorem primeMirrorAmplitude_mul_eq_one (n : ℕ) (δ : ℝ) :
    primeMirrorLeftAmplitude n δ * primeMirrorRightAmplitude n δ = 1 := by
  calc
    primeMirrorLeftAmplitude n δ * primeMirrorRightAmplitude n δ =
        Real.exp
          ((-δ * Real.log (n : ℝ)) +
            (δ * Real.log (n : ℝ))) := by
      simp [primeMirrorLeftAmplitude, primeMirrorRightAmplitude,
        Real.exp_add]
    _ = 1 := by
      ring_nf
      simp

/-- The mirror-offset Gap is nonnegative. -/
theorem primeMirrorOffsetGap_nonneg (n : ℕ) (δ : ℝ) :
    0 ≤ primeMirrorOffsetGap n δ := by
  exact sq_nonneg _

/--
For a genuinely nonconstant positive-base mode, mirror balance is equivalent
to zero horizontal offset.
-/
theorem primeMirrorOffsetGap_eq_zero_iff_delta_eq_zero
    {n : ℕ} (hn : 1 < n) (δ : ℝ) :
    primeMirrorOffsetGap n δ = 0 ↔ δ = 0 := by
  constructor
  · intro hgap
    unfold primeMirrorOffsetGap at hgap
    have hdiff :
        primeMirrorLeftAmplitude n δ - primeMirrorRightAmplitude n δ = 0 :=
      sq_eq_zero_iff.mp hgap
    have heq :
        primeMirrorLeftAmplitude n δ = primeMirrorRightAmplitude n δ :=
      sub_eq_zero.mp hdiff
    have hlogeq :
        -δ * Real.log (n : ℝ) = δ * Real.log (n : ℝ) := by
      have h := congrArg Real.log heq
      simpa [primeMirrorLeftAmplitude, primeMirrorRightAmplitude] using h
    have hlogpos : 0 < Real.log (n : ℝ) := by
      apply Real.log_pos
      exact_mod_cast hn
    nlinarith
  · intro hδ
    subst δ
    simp [primeMirrorOffsetGap, primeMirrorLeftAmplitude,
      primeMirrorRightAmplitude]

/-- A nonzero horizontal offset gives a strictly positive mode Gap. -/
theorem primeMirrorOffsetGap_pos_of_delta_ne_zero
    {n : ℕ} (hn : 1 < n) {δ : ℝ} (hδ : δ ≠ 0) :
    0 < primeMirrorOffsetGap n δ := by
  have hne : primeMirrorOffsetGap n δ ≠ 0 := by
    intro hgap
    exact hδ
      ((primeMirrorOffsetGap_eq_zero_iff_delta_eq_zero hn δ).mp hgap)
  exact lt_of_le_of_ne
    (primeMirrorOffsetGap_nonneg n δ)
    (Ne.symm hne)

/-- The CF2D interaction Beam of the mirror pair is the fixed Big `2`. -/
theorem primeMirrorOffsetState_interaction_eq_two
    (n : ℕ) (δ : ℝ) :
    cf2dInteractionBeam (primeMirrorOffsetState n δ) = 2 := by
  change
    2 * primeMirrorLeftAmplitude n δ * primeMirrorRightAmplitude n δ = 2
  calc
    2 * primeMirrorLeftAmplitude n δ * primeMirrorRightAmplitude n δ =
        2 *
          (primeMirrorLeftAmplitude n δ *
            primeMirrorRightAmplitude n δ) := by
      ring
    _ = 2 := by
      rw [primeMirrorAmplitude_mul_eq_one]
      ring

/-- The difference whole of the mirror state is exactly the mirror-offset Gap. -/
@[simp]
theorem primeMirrorOffsetState_minusWhole_eq_gap
    (n : ℕ) (δ : ℝ) :
    cf2dMinusWhole (primeMirrorOffsetState n δ) =
      primeMirrorOffsetGap n δ :=
  rfl

/--
The mirror-state square mass is the fixed interaction Big plus the offset Gap.
-/
theorem primeMirrorOffsetState_squareMass_eq_two_add_gap
    (n : ℕ) (δ : ℝ) :
    squareMass
        (primeMirrorOffsetState n δ).core
        (primeMirrorOffsetState n δ).beam =
      2 + primeMirrorOffsetGap n δ := by
  change
    primeMirrorLeftAmplitude n δ ^ 2 +
        primeMirrorRightAmplitude n δ ^ 2 =
      2 +
        (primeMirrorLeftAmplitude n δ -
          primeMirrorRightAmplitude n δ) ^ 2
  calc
    primeMirrorLeftAmplitude n δ ^ 2 +
        primeMirrorRightAmplitude n δ ^ 2 =
      2 *
          (primeMirrorLeftAmplitude n δ *
            primeMirrorRightAmplitude n δ) +
        (primeMirrorLeftAmplitude n δ -
          primeMirrorRightAmplitude n δ) ^ 2 := by
      ring
    _ = 2 +
        (primeMirrorLeftAmplitude n δ -
          primeMirrorRightAmplitude n δ) ^ 2 := by
      rw [primeMirrorAmplitude_mul_eq_one]
      ring

/-- The centered complex-point Gap vanishes exactly on the critical line. -/
theorem primeMirrorOffsetGapAt_eq_zero_iff_re_eq_half
    {n : ℕ} (hn : 1 < n) (s : ℂ) :
    primeMirrorOffsetGapAt n s = 0 ↔
      s.re = (1 : ℝ) / 2 := by
  rw [primeMirrorOffsetGapAt,
    primeMirrorOffsetGap_eq_zero_iff_delta_eq_zero hn,
    centeredSigma_eq_zero_iff]

/-- Off the critical line, every nonconstant positive-base mode has positive Gap. -/
theorem primeMirrorOffsetGapAt_pos_of_re_ne_half
    {n : ℕ} (hn : 1 < n) {s : ℂ}
    (hre : s.re ≠ (1 : ℝ) / 2) :
    0 < primeMirrorOffsetGapAt n s := by
  apply primeMirrorOffsetGap_pos_of_delta_ne_zero hn
  intro hcenter
  exact hre ((centeredSigma_eq_zero_iff s.re).mp hcenter)

end DkMath.RH.CFBRCProjection
