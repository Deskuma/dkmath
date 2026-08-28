/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.PascalCenteredXiMellinArithmeticSpecialization
import Mathlib.Tactic

/-!
# Finite variable-weight source-rank audit

This module records the finite algebra needed by GWSS-000/001.  The existing
Xi weighted moment is a multiplicity-weighted evaluation sum, and the
admissible even-weight API contains polynomial examples beyond the quadratic
weight.  The abstract two-orbit model below shows that the quadratic, radial,
and horizontal second-moment observables do not recover a fourth moment.

The model is deliberately not a statement about actual zeta zeros.  It is a
non-recoverability certificate for the finite-observable comparison only.  No
classical Weil positivity, infinite-height limit, RH provider, or transfer of
the model to the actual Xi zero window is asserted here.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open scoped BigOperators

/-! ## GWSS-000: admissible polynomial weights -/

private theorem pascalCenteredEvenWeight_power_two (k : ℕ) :
    PascalCenteredEvenWeight (fun z : ℂ => z ^ (2 * k)) := by
  intro z
  change (-z) ^ (2 * k) = z ^ (2 * k)
  rw [pow_mul, pow_mul]
  simp

private theorem pascalCenteredEvenWeight_power_two_differentiable (k : ℕ) :
    Differentiable ℂ (fun z : ℂ => z ^ (2 * k)) := by
  fun_prop

/-! The constant weight is an admissible even polynomial example. -/
theorem pascalCenteredEvenWeight_one :
    PascalCenteredEvenWeight (fun _ : ℂ => 1) := by
  exact pascalCenteredEvenWeight_power_two 0

/-! The quartic weight is an admissible even polynomial example. -/
theorem pascalCenteredEvenWeight_quartic :
    PascalCenteredEvenWeight (fun z : ℂ => z ^ 4) := by
  simpa [show 4 = 2 * 2 by norm_num] using
    pascalCenteredEvenWeight_power_two 2

/-! The sextic weight is an admissible even polynomial example. -/
theorem pascalCenteredEvenWeight_sextic :
    PascalCenteredEvenWeight (fun z : ℂ => z ^ 6) := by
  simpa [show 6 = 2 * 3 by norm_num] using
    pascalCenteredEvenWeight_power_two 3

/-! The constant weight satisfies the differentiability contract. -/
theorem pascalCenteredEvenWeight_one_differentiable :
    Differentiable ℂ (fun _ : ℂ => (1 : ℂ)) := by
  fun_prop

/-! The quartic weight satisfies the differentiability contract. -/
theorem pascalCenteredEvenWeight_quartic_differentiable :
    Differentiable ℂ (fun z : ℂ => z ^ 4) := by
  exact pascalCenteredEvenWeight_power_two_differentiable 2

/-! The sextic weight satisfies the differentiability contract. -/
theorem pascalCenteredEvenWeight_sextic_differentiable :
    Differentiable ℂ (fun z : ℂ => z ^ 6) := by
  exact pascalCenteredEvenWeight_power_two_differentiable 3

/-! ## GWSS-001: an abstract even-orbit model -/

/-- The moment of two weighted even orbits under an arbitrary test function. -/
def gwssEvenOrbitMoment (x : Fin 2 → ℂ) (h : ℂ → ℂ) : ℂ :=
  ∑ i : Fin 2, (h (x i) + h (-x i))

/-- The radial second moment of the same two-orbit model. -/
def gwssEvenOrbitRadialSecondMoment (x : Fin 2 → ℂ) : ℝ :=
  ∑ i : Fin 2,
    (Complex.normSq (x i) + Complex.normSq (-x i))

/-- The horizontal second moment of the same two-orbit model. -/
def gwssEvenOrbitHorizontalSecondMoment (x : Fin 2 → ℂ) : ℝ :=
  ∑ i : Fin 2, (((x i).re ^ 2) + ((-x i).re ^ 2))

/-- First model: the even orbits at `1` and `7`. -/
def gwssEvenOrbitConfigurationA : Fin 2 → ℂ := ![(1 : ℂ), 7]

/-- Second model: two copies of the even orbit at `5`. -/
def gwssEvenOrbitConfigurationB : Fin 2 → ℂ := ![(5 : ℂ), 5]

/-! The finite even-orbit source map is additive in the weight. -/
theorem gwssEvenOrbitMoment_add (x : Fin 2 → ℂ) (h₁ h₂ : ℂ → ℂ) :
    gwssEvenOrbitMoment x (fun z => h₁ z + h₂ z) =
      gwssEvenOrbitMoment x h₁ + gwssEvenOrbitMoment x h₂ := by
  simp only [gwssEvenOrbitMoment, Finset.sum_add_distrib]
  ac_rfl

/-! The two model configurations have equal holomorphic second moment. -/
theorem gwssEvenOrbitConfigurationA_second_eq_configurationB :
    gwssEvenOrbitMoment gwssEvenOrbitConfigurationA (fun z => z ^ 2) =
      gwssEvenOrbitMoment gwssEvenOrbitConfigurationB (fun z => z ^ 2) := by
  norm_num [gwssEvenOrbitMoment, gwssEvenOrbitConfigurationA,
    gwssEvenOrbitConfigurationB]

/-! The two model configurations have equal radial second moment. -/
theorem gwssEvenOrbitConfigurationA_radial_eq_configurationB :
    gwssEvenOrbitRadialSecondMoment gwssEvenOrbitConfigurationA =
      gwssEvenOrbitRadialSecondMoment gwssEvenOrbitConfigurationB := by
  norm_num [gwssEvenOrbitRadialSecondMoment, gwssEvenOrbitConfigurationA,
    gwssEvenOrbitConfigurationB, Complex.normSq_apply]

/-! The two model configurations have equal horizontal second moment. -/
theorem gwssEvenOrbitConfigurationA_horizontal_eq_configurationB :
    gwssEvenOrbitHorizontalSecondMoment gwssEvenOrbitConfigurationA =
      gwssEvenOrbitHorizontalSecondMoment gwssEvenOrbitConfigurationB := by
  norm_num [gwssEvenOrbitHorizontalSecondMoment, gwssEvenOrbitConfigurationA,
    gwssEvenOrbitConfigurationB]

/-- The fourth moment separates the two models despite equal second moments. -/
theorem gwssEvenOrbitConfigurationA_fourth_ne_configurationB :
    gwssEvenOrbitMoment gwssEvenOrbitConfigurationA (fun z => z ^ 4) ≠
      gwssEvenOrbitMoment gwssEvenOrbitConfigurationB (fun z => z ^ 4) := by
  norm_num [gwssEvenOrbitMoment, gwssEvenOrbitConfigurationA,
    gwssEvenOrbitConfigurationB]

end DkMath.RH.CFBRCProjection
