/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyTateFrobenius

#print "file: DkMathTest.FLT.FreyTateFrobenius"

open Polynomial DkMath.Lib.RepresentationTheory.TriangularTwoCharacter

private instance : Fact (1 < (25 : ℕ)) := ⟨by decide⟩

-- A repeated-root characteristic polynomial does not make the actual matrix scalar.
private def U : Matrix (Fin 2) (Fin 2) (ZMod 25) := !![1, 5; 0, 1]
example : U ≠ 1 := by decide
example : U.charpoly = (X - C 1) ^ 2 := by
  rw [Matrix.charpoly_fin_two]
  norm_num [U, Matrix.trace_fin_two, Matrix.det_fin_two]
  simp only [map_ofNat]
  ring

-- General commutative-ring identity, including a nontriangular composite-modulus matrix.
private def M : Matrix (Fin 2) (Fin 2) (ZMod 25) := !![2, 5; 3, 4]
example : M * M + (18 : ZMod 25) • (1 : Matrix (Fin 2) (Fin 2) (ZMod 25)) = (6 : ZMod 25) • M := by
  have hd : M.det = 18 := by decide
  have ht : M.trace = 6 := by decide
  simpa only [hd, ht] using matrix_quadratic M

-- Kernel axiom reports for the selected production endpoints.
#print axioms DkMath.Lib.NumberTheory.CyclotomicFrobenius.torsionCyclotomicCharacter_eq_natCast
#print axioms DkMath.Lib.NumberTheory.CyclotomicFrobenius.prime_power_valuation_eq_one
#print axioms DkMath.Lib.NumberTheory.CyclotomicFrobenius.padicCyclotomicCharacter_eq_natCast
#print axioms DkMath.Lib.RepresentationTheory.TriangularTwoCharacter.trace
#print axioms DkMath.Lib.RepresentationTheory.TriangularTwoCharacter.charpoly_factor
#print axioms DkMath.Lib.RepresentationTheory.TriangularTwoCharacter.quadratic
#print axioms DkMath.Lib.RepresentationTheory.TriangularTwoCharacter.matrix_quadratic
#print axioms DkMath.Lib.RepresentationTheory.TriangularTwoCharacter.linear_quadratic
#print axioms DkMath.FLT.Frey.Source.residualTate_trace_reduction
#print axioms DkMath.FLT.Frey.Source.tateCyclotomicCharacter_frobenius
#print axioms DkMath.FLT.Frey.Source.residualTate_frobenius_det
#print axioms DkMath.FLT.Frey.Source.residualTate_frobenius_trace
#print axioms DkMath.FLT.Frey.Source.residualTate_frobenius_charpoly
#print axioms DkMath.FLT.Frey.Source.residualTate_frobenius_relation
#print axioms DkMath.FLT.Frey.Source.residualTate_finite_frobenius_relation
