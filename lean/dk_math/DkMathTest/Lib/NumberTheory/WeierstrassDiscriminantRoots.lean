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

#print axioms discriminant_eq_root_differences
#print axioms DkMath.Lib.NumberTheory.EllipticFiniteKernel.half_tangent_product_eq_root_products
#print axioms DkMath.Lib.NumberTheory.EllipticFiniteKernel.half_x_sub_root_ne_zero
#print axioms discriminant_product_of_pair_relations
end WeierstrassDiscriminantRootsTest
