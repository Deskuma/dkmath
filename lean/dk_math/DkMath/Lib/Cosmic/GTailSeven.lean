/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.Cosmic.GTailTransport
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

#print "file: DkMath.Lib.Cosmic.GTailSeven"

/-!
# Degree-seven calibration of selected binomial bodies

The interior selection removes the coefficient-one endpoints. The general
factor kernel extracts `x*u`, and its finite residual is `7*(x+u)` times the
square of `x^2+x*u+u^2`. Selection reconstructs Big; transport reinserts an
endpoint with exact accounting. The quadratic form is norm-shaped only: no
number-field norm map, cyclotomic carrier or FLT hypothesis is introduced.
-/

namespace DkMath.CosmicFormula

open scoped BigOperators

variable {R : Type*} [CommSemiring R]

/-- The degree-seven tail at depth six, derived from canonical recursion. -/
theorem GTail_seven_six (x u : R) : GTail 7 6 x u = x + 7 * u := by
  rw [GTail_rec 7 6 x u (by decide), GTail_self_eq_one]
  norm_num [Nat.choose]
  ac_rfl

/-- The degree-seven tail at depth five, with its Pascal boundary visible. -/
theorem GTail_seven_five (x u : R) :
    GTail 7 5 x u = x ^ 2 + 7 * x * u + 21 * u ^ 2 := by
  rw [GTail_rec 7 5 x u (by decide), GTail_seven_six]
  norm_num [Nat.choose]
  ring

/-- Selecting absolute powers six and seven restores the boundary power. -/
theorem selectedBody_seven_six (x u : R) :
    selectedBody 7 (Finset.Ico 6 8) x u = x ^ 6 * (x + 7 * u) := by
  rw [selectedBody_Ico 7 6 x u (by decide), GTail_seven_six]

/-- Selecting absolute powers five through seven gives the quadratic cut. -/
theorem selectedBody_seven_five (x u : R) :
    selectedBody 7 (Finset.Ico 5 8) x u =
      x ^ 5 * (x ^ 2 + 7 * x * u + 21 * u ^ 2) := by
  rw [selectedBody_Ico 7 5 x u (by decide), GTail_seven_five]

/-- Both endpoint terms remain in the Gap of the interior selection. -/
theorem selectedGap_seven_interior (x u : R) :
    selectedGap 7 (Finset.Ico 1 7) x u = u ^ 7 + x ^ 7 := by
  norm_num [selectedGap, selectedTerm, Finset.sum_filter, Finset.sum_range_succ, Nat.choose]

/-- The general active-index factor theorem extracts exactly the forced `x*u`. -/
theorem selectedBody_seven_interior_eq_mul_residual (x u : R) :
    selectedBody 7 (Finset.Ico 1 7) x u =
      x * u * selectedResidual 7 (Finset.Ico 1 7) 1 6 x u := by
  have hbounds : ∀ k ∈ activeSelectedIndices 7 (Finset.Ico 1 7), 1 ≤ k ∧ k ≤ 6 := by
    intro k hk
    rw [activeSelectedIndices_interior] at hk
    have := Finset.mem_Ico.mp hk
    omega
  simpa only [pow_one, show 7 - 6 = 1 from rfl] using
    selectedBody_eq_monomial_mul_residual 7 (Finset.Ico 1 7) 1 6 x u
      (by decide) (by decide) hbounds

/-- Degree-seven coefficient content is a specialization of the prime API. -/
theorem coeffGCD_seven_interior : coeffGCD 7 (Finset.Ico 1 7) = 7 :=
  coeffGCD_prime_interior 7 (by decide)

/-- The joint natural divisor comes from the general coefficient/monomial API. -/
theorem seven_mul_coords_dvd_selectedBody_interior (x u : ℕ) :
    7 * x * u ∣ selectedBody 7 (Finset.Ico 1 7) x u :=
  prime_mul_coords_dvd_selectedBody_interior 7 x u (by decide)

/-- The finite interior residual has a quadratic square, over every CommSemiring. -/
theorem selectedResidual_seven_interior (x u : R) :
    selectedResidual 7 (Finset.Ico 1 7) 1 6 x u =
      7 * (x + u) * (x ^ 2 + x * u + u ^ 2) ^ 2 := by
  have hexpand : selectedResidual 7 (Finset.Ico 1 7) 1 6 x u =
      7 * u ^ 5 + 21 * x * u ^ 4 + 35 * x ^ 2 * u ^ 3 +
        35 * x ^ 3 * u ^ 2 + 21 * x ^ 4 * u + 7 * x ^ 5 := by
    norm_num [selectedResidual, activeSelectedIndices, Finset.sum_filter,
      Finset.sum_range_succ, Nat.choose]
  rw [hexpand]
  ring

/-- Interior Body factorization is obtained through the general monomial extraction. -/
theorem selectedBody_seven_interior (x u : R) :
    selectedBody 7 (Finset.Ico 1 7) x u =
      7 * x * u * (x + u) * (x ^ 2 + x * u + u ^ 2) ^ 2 := by
  rw [selectedBody_seven_interior_eq_mul_residual, selectedResidual_seven_interior]
  ac_rfl

/-- Exact degree-seven Big reconstruction through selected Gap and Body. -/
theorem add_pow_seven_eq_gap_add_interior (x u : R) :
    (x + u) ^ 7 = (u ^ 7 + x ^ 7) +
      7 * x * u * (x + u) * (x ^ 2 + x * u + u ^ 2) ^ 2 := by
  rw [selectedGap_add_selectedBody 7 (Finset.Ico 1 7) x u,
    selectedGap_seven_interior, selectedBody_seven_interior]

/-- Subtraction reading of the balance, stated separately for a commutative ring. -/
theorem add_pow_seven_sub_endpoints {R : Type*} [CommRing R] (x u : R) :
    (x + u) ^ 7 - x ^ 7 - u ^ 7 =
      7 * x * u * (x + u) * (x ^ 2 + x * u + u ^ 2) ^ 2 := by
  rw [add_pow_seven_eq_gap_add_interior]
  ring

/--
Transporting endpoint zero adds `u^7` to the calibrated Body and removes it
from Gap. The generic transport lemmas provide both observation equations.
-/
theorem selectedSeven_zero_endpoint_transport (x u : R) :
    selectedBody 7 (insert 0 (Finset.Ico 1 7)) x u =
      7 * x * u * (x + u) * (x ^ 2 + x * u + u ^ 2) ^ 2 + u ^ 7 ∧
    selectedGap 7 (Finset.Ico 1 7) x u =
      selectedGap 7 (insert 0 (Finset.Ico 1 7)) x u + u ^ 7 := by
  constructor
  · simpa [selectedTerm, selectedBody_seven_interior] using
      selectedBody_insert 7 0 (Finset.Ico 1 7) x u (by decide) (by simp)
  · simpa [selectedTerm] using
      selectedGap_insert 7 0 (Finset.Ico 1 7) x u (by decide) (by simp)

/-- Endpoint insertion changes coefficient content, despite conserved Big balance. -/
theorem coeffGCD_seven_zero_endpoint :
    coeffGCD 7 (Finset.Ico 1 7) = 7 ∧ coeffGCD 7 (insert 0 (Finset.Ico 1 7)) = 1 := by
  exact ⟨coeffGCD_seven_interior,
    coeffGCD_eq_one_of_zero_mem 7 (insert 0 (Finset.Ico 1 7)) (by simp)⟩

/-- A quadratic polynomial calibration; this does not identify a number-field norm map. -/
theorem quadratic_form_four_mul (x u : R) :
    (2 * x + u) ^ 2 + 3 * u ^ 2 = 4 * (x ^ 2 + x * u + u ^ 2) := by
  ring

end DkMath.CosmicFormula
