/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/
import DkMath.Lib.NumberTheory.EllipticFiniteKernelRootProduct
import DkMath.Lib.NumberTheory.WeierstrassDiscriminantAssembly

#print "file: DkMathTest.Lib.NumberTheory.WeierstrassDiscriminantRoots"

/-! 三つの有理2捩れ根を持つ曲線で、一般の根分解と判別式を検査する。 -/
namespace WeierstrassDiscriminantRootsTest
open WeierstrassCurve Polynomial
open DkMath.Lib.NumberTheory.WeierstrassDiscriminantRoots
open DkMath.Lib.NumberTheory.WeierstrassDiscriminantAssembly

def curve : WeierstrassCurve ℚ := ⟨0, 0, 0, -1, 0⟩

private theorem root_neg : curve.twoTorsionPolynomial.toPoly.eval (-1) = 0 := by
  norm_num [curve, twoTorsionPolynomial, Cubic.toPoly, b₂, b₄, b₆]
private theorem root_zero : curve.twoTorsionPolynomial.toPoly.eval 0 = 0 := by
  norm_num [curve, twoTorsionPolynomial, Cubic.toPoly, b₂, b₄, b₆]
private theorem root_one : curve.twoTorsionPolynomial.toPoly.eval 1 = 0 := by
  norm_num [curve, twoTorsionPolynomial, Cubic.toPoly, b₂, b₄, b₆]

example (x : ℚ) : curve.twoTorsionPolynomial.toPoly.eval x = 4 * (x + 1) * x * (x - 1) := by
  convert polynomial_eval_factor curve (by norm_num) (-1) 0 1 root_neg root_zero root_one
    (by norm_num) (by norm_num) (by norm_num) x using 1; ring

example : curve.Δ = 64 := by
  have h := discriminant_eq_root_differences curve (by norm_num) (-1) 0 1
    root_neg root_zero root_one (by norm_num) (by norm_num) (by norm_num)
  norm_num at h
  exact h

example : (64 : ℚ) * 1 ^ 4 = 64 ^ (2 * 0 + 1) := by
  apply discriminant_product_of_pair_relations 0 (-1) 0 1 (-1) 0 1 64 64 1 1 1 1 <;> norm_num

example :
    (∏ q ∈ ({0} : Finset ℕ), ((1 : ℚ) - (fun _ => (2 : ℚ) / 3) q)) *
      (∏ q ∈ ({0} : Finset ℕ), ((fun _ => (3 : ℚ)) q - 0)) =
      (1 - 0) ^ ({0} : Finset ℕ).card *
        ∏ q ∈ ({0} : Finset ℕ), ((fun _ => (3 : ℚ)) q - 2) := by
  apply product_root_difference_relation ({0} : Finset ℕ)
    (fun _ => (3 : ℚ)) (fun _ => (2 : ℚ) / 3) 0 1 2
  intro q hq
  simp at hq
  subst q
  norm_num

example :
    (fiberFactor ({0} : Finset ℕ) (1 : ℚ) (fun _ => (2 : ℚ) / 3)).eval 3 = 98 / 9 := by
  rw [fiberFactor_eval]
  norm_num

example : (fiberFactor ({0} : Finset ℕ) (1 : ℚ) (fun _ => (2 : ℚ) / 3)).Monic := by
  exact fiberFactor_monic _ _ _

example :
    (fiberFactor ({0} : Finset ℕ) (1 : ℚ) (fun _ => (2 : ℚ) / 3)).natDegree = 3 := by
  simpa using fiberFactor_natDegree ({0} : Finset ℕ) (1 : ℚ) (fun _ => (2 : ℚ) / 3)

example :
    (fiberFactor ({0} : Finset ℕ) (1 : ℚ) (fun _ => (2 : ℚ) / 3)).eval (2 / 3) = 0 := by
  rw [fiberFactor_eval_eq_zero_iff]
  right
  exact ⟨0, by simp⟩

example :
    (fiberFactor ({0} : Finset ℕ) (1 : ℚ) (fun _ => (2 : ℚ) / 3)).roots =
      ({1} : Multiset ℚ) + ({0} : Multiset ℕ).bind
        (fun _ => 2 • ({(2 : ℚ) / 3} : Multiset ℚ)) := by
  exact fiberFactor_roots _ _ _

example :
    (fiberFactor ({0} : Finset ℕ) (1 : ℚ) (fun _ => (2 : ℚ) / 3)) =
      fiberFactor ({0} : Finset ℕ) (1 : ℚ) (fun _ => (2 : ℚ) / 3) := by
  apply (eq_fiberFactor_of_monic_of_roots ({0} : Finset ℕ) (1 : ℚ)
    (fun _ => (2 : ℚ) / 3) _ (fiberFactor_monic _ _ _))
  · rfl
  · rw [fiberFactor_roots, fiberFactor_natDegree]
    simp

example :
    fiberFactor ({0} : Finset ℕ) (1 : ℚ) (fun _ => (2 : ℚ) / 3) ∣
      fiberFactor ({0} : Finset ℕ) (1 : ℚ) (fun _ => (2 : ℚ) / 3) := by
  apply fiberFactor_dvd_of_roots_le _ _ _ _ (fiberFactor_ne_zero _ _ _)
  exact le_rfl

example :
    (fiberFactor ({0} : Finset ℕ) (1 : ℚ) (fun _ => (2 : ℚ) / 3)) =
      fiberFactor ({0} : Finset ℕ) (1 : ℚ) (fun _ => (2 : ℚ) / 3) := by
  apply eq_fiberFactor_of_monic_of_roots_le _ _ _ _ (fiberFactor_monic _ _ _)
  · exact le_rfl
  · exact le_rfl

example :
    (∏ _q ∈ ({0} : Finset ℕ),
      (0 - curve.toAffine.addX (-1) 0 (curve.toAffine.slope (-1) 0 0 0))) *
        (∏ _q ∈ ({0} : Finset ℕ), ((0 : ℚ) - (-1))) =
      ((0 : ℚ) - (-1)) ^ ({0} : Finset ℕ).card *
        ∏ _q ∈ ({0} : Finset ℕ), ((0 : ℚ) - 1) := by
  have h := translated_root_product_relation curve ({0} : Finset ℕ)
    (fun _ => (0 : ℚ)) (fun _ => (0 : ℚ)) (-1) 0 1 rfl rfl
    (by norm_num [curve]) (by norm_num [curve]) (by norm_num [curve])
    (by
      intro _ _
      norm_num [curve, WeierstrassCurve.Affine.equation_iff])
    (by
      intro _ _
      norm_num)
  simpa using h

example (n : ℕ) (Δ Δ' : ℚ) (h : Δ' * (1 : ℚ) ^ 4 = Δ ^ (2 * n + 1)) :
    (1 : Valuation ℚ ℚ≥0) Δ' = ((1 : Valuation ℚ ℚ≥0) Δ) ^ (2 * n + 1) := by
  apply discriminant_value_of_unit_factor (1 : Valuation ℚ ℚ≥0) n Δ Δ' 1 h
  simp

#print axioms discriminant_eq_root_differences
#print axioms DkMath.Lib.NumberTheory.EllipticFiniteKernel.half_tangent_product_eq_root_products
#print axioms DkMath.Lib.NumberTheory.EllipticFiniteKernel.half_x_sub_root_ne_zero
#print axioms discriminant_product_of_pair_relations
end WeierstrassDiscriminantRootsTest
