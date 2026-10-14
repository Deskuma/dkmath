/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenRealCubicHighDepthFive

#print "file: DkMath.FLT.Seven.ThomasThueSixAudit"

/-!
# Fixed `n = 6` Thomas-family audit

This module records kernel-checked fixed-polynomial data for R55.  It is an
audit module, not a claim that the full nontrivial-solution classification has
already been formalized.
-/

namespace DkMath.FLT.Seven

namespace SevenRealCubic

noncomputable section

def thomasForm (n R S : ℤ) : ℤ :=
  R ^ 3 - (n - 1) * R ^ 2 * S - (n + 2) * R * S ^ 2 - S ^ 3

theorem thomasForm_six_eq_F5 (R S : ℤ) :
    thomasForm 6 R S = F5 R S := by
  simp [thomasForm, F5]

theorem thomasForm_six_eq_one_iff (R S : ℤ) :
    thomasForm 6 R S = 1 ↔ F5 R S = 1 := by
  rw [thomasForm_six_eq_F5]

def f5Poly (X : ℚ) : ℚ := X ^ 3 - 5 * X ^ 2 - 8 * X - 1

theorem f5Poly_negSixFive : f5Poly (-(6 / 5 : ℚ)) < 0 := by
  norm_num [f5Poly]

theorem f5Poly_negElevenTen : 0 < f5Poly (-(11 / 10 : ℚ)) := by
  norm_num [f5Poly]

theorem f5Poly_negOneFive : 0 < f5Poly (-(1 / 5 : ℚ)) := by
  norm_num [f5Poly]

theorem f5Poly_negOneTen : f5Poly (-(1 / 10 : ℚ)) < 0 := by
  norm_num [f5Poly]

theorem f5Poly_six : f5Poly 6 < 0 := by
  norm_num [f5Poly]

theorem f5Poly_thirteenHalf : 0 < f5Poly (13 / 2 : ℚ) := by
  norm_num [f5Poly]

theorem f5Poly_sign_ledger :
    f5Poly (-(6 / 5 : ℚ)) < 0 ∧
      0 < f5Poly (-(11 / 10 : ℚ)) ∧
      0 < f5Poly (-(1 / 5 : ℚ)) ∧
      f5Poly (-(1 / 10 : ℚ)) < 0 ∧
      f5Poly 6 < 0 ∧
      0 < f5Poly (13 / 2 : ℚ) := by
  exact ⟨f5Poly_negSixFive, f5Poly_negElevenTen, f5Poly_negOneFive,
    f5Poly_negOneTen, f5Poly_six, f5Poly_thirteenHalf⟩

def f5Real (X : ℝ) : ℝ := X ^ 3 - 5 * X ^ 2 - 8 * X - 1

private theorem f5Real_continuous : Continuous f5Real := by
  change Continuous (fun X : ℝ => X ^ 3 - 5 * X ^ 2 - 8 * X - 1)
  fun_prop

theorem f5Real_root_intervals :
    (∃ x : ℝ, x ∈ Set.Icc (-(6 / 5 : ℝ)) (-(11 / 10 : ℝ)) ∧ f5Real x = 0) ∧
      (∃ x : ℝ, x ∈ Set.Icc (-(1 / 5 : ℝ)) (-(1 / 10 : ℝ)) ∧ f5Real x = 0) ∧
      (∃ x : ℝ, x ∈ Set.Icc (6 : ℝ) (13 / 2 : ℝ) ∧ f5Real x = 0) := by
  have hleft :
      (∃ x : ℝ, x ∈ Set.Icc (-(6 / 5 : ℝ)) (-(11 / 10 : ℝ)) ∧ f5Real x = 0) := by
    have hsign : (0 : ℝ) ∈ Set.Icc (f5Real (-(6 / 5 : ℝ)))
        (f5Real (-(11 / 10 : ℝ))) := by
      norm_num [f5Real]
    rcases intermediate_value_Icc (by norm_num : (-(6 / 5 : ℝ)) ≤ -(11 / 10 : ℝ))
        f5Real_continuous.continuousOn hsign with ⟨x, hx, hzero⟩
    exact ⟨x, hx, hzero⟩
  have hmiddle :
      (∃ x : ℝ, x ∈ Set.Icc (-(1 / 5 : ℝ)) (-(1 / 10 : ℝ)) ∧ f5Real x = 0) := by
    have hsign : (0 : ℝ) ∈ Set.Icc (f5Real (-(1 / 10 : ℝ)))
        (f5Real (-(1 / 5 : ℝ))) := by
      apply Set.mem_Icc.mpr
      constructor <;> norm_num [f5Real]
    rcases intermediate_value_Icc' (by norm_num : (-(1 / 5 : ℝ)) ≤ -(1 / 10 : ℝ))
        f5Real_continuous.continuousOn hsign with ⟨x, hx, hzero⟩
    exact ⟨x, hx, hzero⟩
  have hright :
      (∃ x : ℝ, x ∈ Set.Icc (6 : ℝ) (13 / 2 : ℝ) ∧ f5Real x = 0) := by
    have hsign : (0 : ℝ) ∈ Set.Icc (f5Real 6) (f5Real (13 / 2 : ℝ)) := by
      apply Set.mem_Icc.mpr
      constructor <;> norm_num [f5Real]
    rcases intermediate_value_Icc (by norm_num : (6 : ℝ) ≤ 13 / 2)
        f5Real_continuous.continuousOn hsign with ⟨x, hx, hzero⟩
    exact ⟨x, hx, hzero⟩
  exact ⟨hleft, hmiddle, hright⟩

theorem f5Real_root_separation :
    ∃ root1 root2 root3 : ℝ,
      root1 ∈ Set.Icc (-(6 / 5 : ℝ)) (-(11 / 10 : ℝ)) ∧
      root2 ∈ Set.Icc (-(1 / 5 : ℝ)) (-(1 / 10 : ℝ)) ∧
      root3 ∈ Set.Icc (6 : ℝ) (13 / 2 : ℝ) ∧
      f5Real root1 = 0 ∧ f5Real root2 = 0 ∧ f5Real root3 = 0 ∧
      (9 / 10 : ℝ) ≤ root2 - root1 ∧
      (61 / 10 : ℝ) ≤ root3 - root2 ∧
      (71 / 10 : ℝ) ≤ root3 - root1 := by
  rcases f5Real_root_intervals with ⟨⟨root1, hroot1, hzero1⟩, ⟨root2, hroot2, hzero2⟩,
    ⟨root3, hroot3, hzero3⟩⟩
  refine ⟨root1, root2, root3, hroot1, hroot2, hroot3, hzero1, hzero2, hzero3,
    ?_, ?_, ?_⟩
  · linarith [hroot1.2, hroot2.1]
  · linarith [hroot2.2, hroot3.1]
  · linarith [hroot1.2, hroot3.1]

theorem thomasForm_six_trivial_shell_of_product_zero
    {R S : ℤ} (hThomas : thomasForm 6 R S = 1)
    (hzero : R * S * (R + S) = 0) :
    (R = 1 ∧ S = 0) ∨ (R = 0 ∧ S = -1) ∨ (R = -1 ∧ S = 1) := by
  apply eisenstein_current_highDepthFive_trivial_shell
  · exact (thomasForm_six_eq_one_iff R S).mp hThomas
  · exact hzero

end

end SevenRealCubic

end DkMath.FLT.Seven
