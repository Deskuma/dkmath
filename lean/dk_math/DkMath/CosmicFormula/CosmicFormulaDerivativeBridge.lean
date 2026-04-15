/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib
import DkMath.CosmicFormula.CosmicDifferenceKernel
import DkMath.CosmicFormula.CosmicDerivativePowerLimit
import DkMath.CosmicFormula.CosmicFormulaBasic

#print "file: DkMath.CosmicFormula.CosmicFormulaDerivativeBridge"

namespace DkMath.CosmicFormula

theorem delta_pow_two_eq_u_mul_powerKernel_two (x u : ℝ) :
    delta (fun y : ℝ => y ^ 2) x u = u * powerKernel 2 x u := by
  simpa [delta] using (sub_eq_u_mul_powerKernel 2 x u)

theorem cosmic_formula_unit_eq_delta_pow_two_sub_two_mul (x u : ℝ) :
    DkMath.CosmicFormula.Basic.cosmic_formula_unit x u =
      delta (fun y : ℝ => y ^ 2) x u - 2 * x * u := by
  simp [DkMath.CosmicFormula.Basic.cosmic_formula_unit, delta]
  ring

theorem cosmic_formula_unit_eq_u_mul_powerKernel_two_sub_two_mul (x u : ℝ) :
    DkMath.CosmicFormula.Basic.cosmic_formula_unit x u =
      u * powerKernel 2 x u - 2 * x * u := by
  rw [cosmic_formula_unit_eq_delta_pow_two_sub_two_mul, delta_pow_two_eq_u_mul_powerKernel_two]

theorem cosmic_formula_unit_eq_u_mul_powerKernel_two_gap (x u : ℝ) :
    DkMath.CosmicFormula.Basic.cosmic_formula_unit x u =
      u * (powerKernel 2 x u - 2 * x) := by
  rw [cosmic_formula_unit_eq_u_mul_powerKernel_two_sub_two_mul]
  ring

theorem cosmic_formula_unit_eq_u_sq_from_derivative_bridge (x u : ℝ) :
    DkMath.CosmicFormula.Basic.cosmic_formula_unit x u = u ^ 2 := by
  exact DkMath.CosmicFormula.Basic.cosmic_formula_unit_theorem x u

end DkMath.CosmicFormula
