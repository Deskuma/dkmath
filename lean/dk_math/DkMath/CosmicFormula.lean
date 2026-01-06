import Mathlib

namespace DkMath

namespace CosmicFormula

def cosmic_formula_one (x : ℝ) : ℝ :=
  (x + 1)^2 - x * (x + 2)

def cosmic_formula_u (x u : ℝ) : ℝ :=
  (x + u)^2 - x * (x + 2 * u)

end CosmicFormula

end DkMath
