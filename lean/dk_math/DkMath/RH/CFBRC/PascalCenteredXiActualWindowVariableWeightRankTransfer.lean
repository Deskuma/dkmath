/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.PascalCenteredXiVariableWeightSourceRankAudit
import Mathlib.Tactic

/-!
# Actual finite Xi-window variable-weight rank transfer

This module transfers the GWSS-001 finite orbit idea to the actual centered Xi
zero-disk finset.  The selector is an even polynomial in `w`, constructed from
the squared orbit coordinates `w ^ 2`.  It isolates the multiplicity mass of a
target squared orbit on the finite carrier.

The construction is finite and algebraic.  It does not quotient the carrier,
assume that a negative or conjugate zero is present, invoke RH, remove a
horizontal term, or identify the Mellin family with all even polynomials.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open scoped BigOperators
open DkMath.Analysis
open Filter

/-! ## Part A: finite squared-orbit selectors -/

/-- The unnormalized even selector polynomial for a finite carrier. -/
noncomputable def gwssSquaredOrbitSelectorUnnormalized
    (S : Finset ℂ) (z w : ℂ) : ℂ :=
  (S.filter (fun a => a ^ 2 ≠ z ^ 2)).prod (fun a => w ^ 2 - a ^ 2)

/-- The denominator used to normalize a squared-orbit selector. -/
noncomputable def gwssSquaredOrbitSelectorDenominator
    (S : Finset ℂ) (z : ℂ) : ℂ :=
  gwssSquaredOrbitSelectorUnnormalized S z z

/-- The normalized selector of the squared orbit of `z` on `S`. -/
noncomputable def gwssSquaredOrbitSelector
    (S : Finset ℂ) (z w : ℂ) : ℂ :=
  gwssSquaredOrbitSelectorUnnormalized S z w /
    gwssSquaredOrbitSelectorDenominator S z

private theorem differentiable_finset_product
    {α : Type} (S : Finset α) (f : α → ℂ → ℂ)
    (hf : ∀ a ∈ S, Differentiable ℂ (f a)) :
    Differentiable ℂ (fun w => S.prod (fun a => f a w)) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
      simp only [Finset.prod_insert ha]
      apply (hf a (by simp)).mul
      apply ih
      intro b hb
      exact hf b (by simp [hb])

/-- The unnormalized selector is even because every factor depends on `w ^ 2`. -/
theorem gwssSquaredOrbitSelectorUnnormalized_even
    (S : Finset ℂ) (z : ℂ) :
    PascalCenteredEvenWeight
      (gwssSquaredOrbitSelectorUnnormalized S z) := by
  intro w
  unfold gwssSquaredOrbitSelectorUnnormalized
  apply Finset.prod_congr rfl
  intro a ha
  ring

/-- The unnormalized selector is a finite product of entire quadratic factors. -/
theorem gwssSquaredOrbitSelectorUnnormalized_differentiable
    (S : Finset ℂ) (z : ℂ) :
    Differentiable ℂ (gwssSquaredOrbitSelectorUnnormalized S z) := by
  unfold gwssSquaredOrbitSelectorUnnormalized
  apply differentiable_finset_product
  intro a ha
  fun_prop

/-- Removing the target squared orbit leaves no zero factor at the target. -/
theorem gwssSquaredOrbitSelector_denominator_ne_zero
    {S : Finset ℂ} {z : ℂ} :
    gwssSquaredOrbitSelectorDenominator S z ≠ 0 := by
  unfold gwssSquaredOrbitSelectorDenominator
    gwssSquaredOrbitSelectorUnnormalized
  apply Finset.prod_ne_zero_iff.mpr
  intro a ha
  have hasq : a ^ 2 ≠ z ^ 2 := (Finset.mem_filter.mp ha).2
  exact sub_ne_zero.mpr hasq.symm

/-- The normalized selector vanishes on a carrier point outside the target
squared orbit. -/
theorem gwssSquaredOrbitSelector_eq_zero_of_sq_ne
    {S : Finset ℂ} {z w : ℂ} (hw : w ∈ S)
    (hwsq : w ^ 2 ≠ z ^ 2) :
    gwssSquaredOrbitSelector S z w = 0 := by
  have hwfilter : w ∈ S.filter (fun a => a ^ 2 ≠ z ^ 2) :=
    Finset.mem_filter.mpr ⟨hw, hwsq⟩
  unfold gwssSquaredOrbitSelector
  rw [show gwssSquaredOrbitSelectorUnnormalized S z w = 0 by
    unfold gwssSquaredOrbitSelectorUnnormalized
    exact Finset.prod_eq_zero hwfilter (by ring)]
  simp

/-- The normalized selector is constant with value one on the target squared
orbit. -/
theorem gwssSquaredOrbitSelector_eq_one_of_sq_eq
    {S : Finset ℂ} {z w : ℂ} (hwsq : w ^ 2 = z ^ 2) :
    gwssSquaredOrbitSelector S z w = 1 := by
  have hnum : gwssSquaredOrbitSelectorUnnormalized S z w =
      gwssSquaredOrbitSelectorUnnormalized S z z := by
    unfold gwssSquaredOrbitSelectorUnnormalized
    apply Finset.prod_congr rfl
    intro a ha
    rw [hwsq]
  unfold gwssSquaredOrbitSelector gwssSquaredOrbitSelectorDenominator
  rw [hnum]
  exact div_self gwssSquaredOrbitSelector_denominator_ne_zero

/-- Normalization preserves evenness of the squared-orbit selector. -/
theorem gwssSquaredOrbitSelector_even
    (S : Finset ℂ) (z : ℂ) :
    PascalCenteredEvenWeight (gwssSquaredOrbitSelector S z) := by
  intro w
  unfold gwssSquaredOrbitSelector
  congr 1
  apply Finset.prod_congr rfl
  intro a ha
  ring

/-- The normalized selector remains entire in the carrier variable. -/
theorem gwssSquaredOrbitSelector_differentiable
    (S : Finset ℂ) (z : ℂ) :
    Differentiable ℂ (gwssSquaredOrbitSelector S z) := by
  unfold gwssSquaredOrbitSelector
  exact (gwssSquaredOrbitSelectorUnnormalized_differentiable S z).div_const _

/-! ## Part A: actual Xi-window evaluation -/

/-- The actual Xi-window squared-orbit selector at radius `R` and target `z`. -/
noncomputable def pascalCenteredXiActualSquaredOrbitSelector
    (R : ℝ) (z w : ℂ) : ℂ :=
  gwssSquaredOrbitSelector (pascalCenteredXiZeroDiskFinset R) z w

/-- The actual finite Xi moment of a squared-orbit selector is its orbit mass.

The right-hand side is written as a filtered finite sum rather than assuming
that the actual carrier is already quotiented by `w ↔ -w`. -/
theorem pascalCenteredXiZeroDiskWeightedMoment_actualSquaredOrbitSelector
    {R : ℝ} {z : ℂ} (_hz : z ∈ pascalCenteredXiZeroDiskFinset R) :
    pascalCenteredXiZeroDiskWeightedMoment
        (pascalCenteredXiActualSquaredOrbitSelector R z) R =
      ∑ a ∈ (pascalCenteredXiZeroDiskFinset R).filter
          (fun a => a ^ 2 = z ^ 2),
        (pascalCenteredXiZeroMultiplicity a : ℂ) := by
  unfold pascalCenteredXiZeroDiskWeightedMoment
    pascalCenteredXiActualSquaredOrbitSelector
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a ha
  by_cases hasq : a ^ 2 = z ^ 2
  · simp only [if_pos hasq]
    rw [gwssSquaredOrbitSelector_eq_one_of_sq_eq hasq]
    simp
  · simp only [if_neg hasq]
    rw [gwssSquaredOrbitSelector_eq_zero_of_sq_ne ha hasq]
    simp

/-! ## Part B: finite Mellin-window nonvanishing audit -/

private theorem eventually_forall_finset
    {α : Type} {l : Filter ℝ} {S : Finset α} {P : α → ℝ → Prop}
    (hP : ∀ z ∈ S, ∀ᶠ ε : ℝ in l, P z ε) :
    ∀ᶠ ε : ℝ in l, ∀ z ∈ S, P z ε := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
      have ha_event : ∀ᶠ ε : ℝ in l, P a ε := hP a (by simp)
      have hS : ∀ z ∈ S, ∀ᶠ ε : ℝ in l, P z ε := by
        intro z hz
        exact hP z (by simp [hz])
      have hS_event : ∀ᶠ ε : ℝ in l, ∀ z ∈ S, P z ε := ih hS
      filter_upwards [ha_event, hS_event] with ε haε hSε
      intro z hz
      simp only [Finset.mem_insert] at hz
      rcases hz with rfl | hz
      · exact haε
      · exact hSε z hz

private theorem eventually_centeredMellinSpectralWeight_ne_zero
    (z : ℂ) :
    ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
      centeredMellinSpectralWeight
          (centeredMellinBoxApprox ε) z ≠ 0 := by
  have hball : Metric.ball (1 : ℂ) (1 / 2 : ℝ) ∈ nhds (1 : ℂ) :=
    Metric.isOpen_ball.mem_nhds (by norm_num)
  have hev :=
    (tendsto_centeredMellinSpectralWeight_centeredMellinBoxApprox_one z).eventually
      hball
  filter_upwards [hev] with ε hε hzero
  have hdist : dist (0 : ℂ) 1 < (1 / 2 : ℝ) := by
    simpa [hzero] using hε
  norm_num at hdist

/-- On every fixed finite actual Xi zero window, the Mellin box spectral
factor is simultaneously nonzero for all sufficiently small positive box
widths.  This is a finite diagonal fact from pointwise convergence to `1`; it
does not by itself prove that the `τ`-family has full squared-orbit rank. -/
theorem eventually_pascalCenteredXiMellinSpectralWeight_ne_zero_on_actual_window
    (R : ℝ) :
    ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
      ∀ z ∈ pascalCenteredXiZeroDiskFinset R,
        centeredMellinSpectralWeight
            (centeredMellinBoxApprox ε) z ≠ 0 := by
  apply eventually_forall_finset
  intro z _hz
  exact eventually_centeredMellinSpectralWeight_ne_zero z

end DkMath.RH.CFBRCProjection
