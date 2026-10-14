/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.Cosmic.GTailSeven

#print "file: DkMathTest.CosmicFormula.GTailSeven"

/-!
# Regression tests for degree-seven selection calibration

General semiring contracts are checked together with independent numerical
and ring-normalized identities. Endpoint transport and content change reuse
the previous layers. No FLT hypothesis or actual norm-map claim occurs.
-/

namespace DkMathTest.GTailSeven

open DkMath.CosmicFormula

variable {R : Type*} [CommSemiring R]

example (x u : R) : GTail 7 6 x u = x + 7 * u := GTail_seven_six x u

example (x u : R) :
    GTail 7 5 x u = x ^ 2 + 7 * x * u + 21 * u ^ 2 := GTail_seven_five x u

example (x u : R) :
    selectedBody 7 (Finset.Ico 6 8) x u = x ^ 6 * (x + 7 * u) :=
  selectedBody_seven_six x u

example (x u : R) :
    selectedBody 7 (Finset.Ico 5 8) x u =
      x ^ 5 * (x ^ 2 + 7 * x * u + 21 * u ^ 2) :=
  selectedBody_seven_five x u

example (x u : R) : selectedGap 7 (Finset.Ico 1 7) x u = u ^ 7 + x ^ 7 :=
  selectedGap_seven_interior x u

example (x u : R) :
    selectedResidual 7 (Finset.Ico 1 7) 1 6 x u =
      7 * (x + u) * (x ^ 2 + x * u + u ^ 2) ^ 2 :=
  selectedResidual_seven_interior x u

-- A derivation through selection and the Body theorem that uses general factor extraction.
example (x u : R) :
    (x + u) ^ 7 = (u ^ 7 + x ^ 7) +
      7 * x * u * (x + u) * (x ^ 2 + x * u + u ^ 2) ^ 2 := by
  rw [selectedGap_add_selectedBody 7 (Finset.Ico 1 7) x u,
    selectedGap_seven_interior, selectedBody_seven_interior]

-- An independent ring-normalized check, with no selection/factor theorem used.
example (x u : R) :
    (x + u) ^ 7 = (u ^ 7 + x ^ 7) +
      7 * x * u * (x + u) * (x ^ 2 + x * u + u ^ 2) ^ 2 := by
  ring

example (x u : ℤ) :
    (x + u) ^ 7 - x ^ 7 - u ^ 7 =
      7 * x * u * (x + u) * (x ^ 2 + x * u + u ^ 2) ^ 2 :=
  add_pow_seven_sub_endpoints x u

-- Equal coordinates: compare Big, Gap, Body, residual and the exact factor.
example :
    selectedGap 7 (Finset.Ico 1 7) (1 : ℕ) 1 = 2 ∧
    selectedBody 7 (Finset.Ico 1 7) (1 : ℕ) 1 = 126 ∧
    selectedResidual 7 (Finset.Ico 1 7) 1 6 (1 : ℕ) 1 = 126 := by
  norm_num [selectedGap_seven_interior, selectedBody_seven_interior,
    selectedResidual_seven_interior]

example : ((1 : ℕ) + 1) ^ 7 - 1 - 1 = 126 := by norm_num

example : 7 * (1 : ℕ) * 1 * (1 + 1) * (1 ^ 2 + 1 * 1 + 1 ^ 2) ^ 2 = 126 := by
  norm_num

example : ((1 : ℤ) + 1) ^ 7 - 1 ^ 7 - 1 ^ 7 = 126 := by
  calc
    ((1 : ℤ) + 1) ^ 7 - 1 ^ 7 - 1 ^ 7 =
        7 * 1 * 1 * (1 + 1) * (1 ^ 2 + 1 * 1 + 1 ^ 2) ^ 2 :=
      add_pow_seven_sub_endpoints 1 1
    _ = 126 := by norm_num

-- Asymmetric coordinates, calibrated through the API.
example :
    GTail 7 6 (2 : ℕ) 3 = 23 ∧ GTail 7 5 (2 : ℕ) 3 = 235 ∧
    selectedBody 7 (Finset.Ico 6 8) (2 : ℕ) 3 = 1472 ∧
    selectedBody 7 (Finset.Ico 5 8) (2 : ℕ) 3 = 7520 := by
  rw [GTail_seven_six, GTail_seven_five, selectedBody_seven_six, selectedBody_seven_five]
  norm_num

example :
    selectedGap 7 (Finset.Ico 1 7) (2 : ℕ) 3 = 2315 ∧
    selectedBody 7 (Finset.Ico 1 7) (2 : ℕ) 3 = 75810 ∧
    selectedResidual 7 (Finset.Ico 1 7) 1 6 (2 : ℕ) 3 = 12635 := by
  norm_num [selectedGap_seven_interior, selectedBody_seven_interior,
    selectedResidual_seven_interior]

example :
    selectedGap 7 (Finset.Ico 1 7) (3 : ℕ) 2 = 2315 ∧
    selectedBody 7 (Finset.Ico 1 7) (3 : ℕ) 2 = 75810 := by
  norm_num [selectedGap_seven_interior, selectedBody_seven_interior]

-- Direct finite-sum computation checks the exact Body independently of the factor theorem.
example :
    selectedBody 7 (Finset.Ico 1 7) (2 : ℕ) 3 = 75810 ∧
      7 * (2 : ℕ) * 3 * (2 + 3) * (2 ^ 2 + 2 * 3 + 3 ^ 2) ^ 2 = 75810 := by
  norm_num [selectedBody, selectedTerm, Finset.sum_filter, Finset.sum_range_succ, Nat.choose]

example : coeffGCD 7 (Finset.Ico 1 7) = 7 := coeffGCD_seven_interior

example : 7 * 1 * 1 ∣ selectedBody 7 (Finset.Ico 1 7) 1 1 :=
  seven_mul_coords_dvd_selectedBody_interior 1 1

example : 7 * 2 * 3 ∣ selectedBody 7 (Finset.Ico 1 7) 2 3 :=
  seven_mul_coords_dvd_selectedBody_interior 2 3

example : 7 * 3 * 2 ∣ selectedBody 7 (Finset.Ico 1 7) 3 2 :=
  seven_mul_coords_dvd_selectedBody_interior 3 2

-- Zero-coordinate boundaries require no nonvanishing assumptions.
example (u : R) :
    selectedBody 7 (Finset.Ico 1 7) 0 u = 0 ∧
      selectedGap 7 (Finset.Ico 1 7) 0 u = u ^ 7 := by
  simp [selectedBody_seven_interior, selectedGap_seven_interior]

example (x : R) :
    selectedBody 7 (Finset.Ico 1 7) x 0 = 0 ∧
      selectedGap 7 (Finset.Ico 1 7) x 0 = x ^ 7 := by
  simp [selectedBody_seven_interior, selectedGap_seven_interior]

-- Public calibration observation uses generic transport and the new factor.
example (x u : R) :
    selectedBody 7 (insert 0 (Finset.Ico 1 7)) x u =
      7 * x * u * (x + u) * (x ^ 2 + x * u + u ^ 2) ^ 2 + u ^ 7 ∧
    selectedGap 7 (Finset.Ico 1 7) x u =
      selectedGap 7 (insert 0 (Finset.Ico 1 7)) x u + u ^ 7 :=
  selectedSeven_zero_endpoint_transport x u

example (x u : R) :
    selectedGap 7 (Finset.Ico 1 7) x u + selectedBody 7 (Finset.Ico 1 7) x u =
      selectedGap 7 (insert 0 (Finset.Ico 1 7)) x u +
        selectedBody 7 (insert 0 (Finset.Ico 1 7)) x u :=
  selected_balance_transport 7 (Finset.Ico 1 7) (insert 0 (Finset.Ico 1 7)) x u

example :
    coeffGCD 7 (Finset.Ico 1 7) = 7 ∧ coeffGCD 7 (insert 0 (Finset.Ico 1 7)) = 1 :=
  coeffGCD_seven_zero_endpoint

example :
    selectedBody 7 (insert 0 (Finset.Ico 1 7)) (1 : ℕ) 1 = 127 := by
  have h := (selectedSeven_zero_endpoint_transport (1 : ℕ) 1).1
  norm_num at h
  exact h

example (x u : R) :
    (2 * x + u) ^ 2 + 3 * u ^ 2 = 4 * (x ^ 2 + x * u + u ^ 2) :=
  quadratic_form_four_mul x u

end DkMathTest.GTailSeven

#print axioms DkMath.CosmicFormula.GTail_seven_six
#print axioms DkMath.CosmicFormula.GTail_seven_five
#print axioms DkMath.CosmicFormula.selectedBody_seven_six
#print axioms DkMath.CosmicFormula.selectedBody_seven_five
#print axioms DkMath.CosmicFormula.selectedGap_seven_interior
#print axioms DkMath.CosmicFormula.selectedBody_seven_interior_eq_mul_residual
#print axioms DkMath.CosmicFormula.coeffGCD_seven_interior
#print axioms DkMath.CosmicFormula.seven_mul_coords_dvd_selectedBody_interior
#print axioms DkMath.CosmicFormula.selectedResidual_seven_interior
#print axioms DkMath.CosmicFormula.selectedBody_seven_interior
#print axioms DkMath.CosmicFormula.add_pow_seven_eq_gap_add_interior
#print axioms DkMath.CosmicFormula.add_pow_seven_sub_endpoints
#print axioms DkMath.CosmicFormula.selectedSeven_zero_endpoint_transport
#print axioms DkMath.CosmicFormula.coeffGCD_seven_zero_endpoint
#print axioms DkMath.CosmicFormula.quadratic_form_four_mul
