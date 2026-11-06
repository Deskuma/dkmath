/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyTateCyclotomicDeterminant

#print "file: DkMathTest.FLT.FreyTateCyclotomicDeterminant"

/-! Composite modulus regression: nonzero is insufficient for scalar cancellation.
The geometric theorem accepts a genuine finite basis, without a pairing provider. -/
example : (5 : ZMod 25) ≠ 0 ∧ (5 : ZMod 25) * 5 = 0 := by decide

open DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
example (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (b : Module.Basis (Fin 2) (ZMod 25) (Torsion E 25))
    (σ : Field.absoluteGaloisGroup ℚ) :
    LinearMap.det (representation E 25 σ) =
      (torsionCyclotomicCharacter 25 (by decide) σ : ZMod 25) :=
  torsion_determinant_all E 25 (by decide) b σ

-- Kernel axiom reports for every audited production root.
#print axioms DkMath.Lib.RepresentationTheory.AlternatingDeterminantRing.coordinates
#print axioms DkMath.Lib.RepresentationTheory.AlternatingDeterminantRing.coefficient_injective
#print axioms DkMath.Lib.RepresentationTheory.AlternatingDeterminantRing.map_eq_det_smul
#print axioms DkMath.Lib.RepresentationTheory.AlternatingDeterminantRing.det_eq_of_equivariant
#print axioms DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.torsionCyclotomicCharacter_spec
#print axioms DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.torsion_determinant_all
#print axioms DkMath.FLT.Frey.Source.residualTateFiniteBasis
#print axioms DkMath.FLT.Frey.Source.residualTate_coordinate_reduction
#print axioms DkMath.FLT.Frey.Source.residualTate_basis_reduction
#print axioms DkMath.FLT.Frey.Source.residualTate_matrix_reduction
#print axioms DkMath.FLT.Frey.Source.residualTate_determinant_finite
#print axioms DkMath.FLT.Frey.Source.tateCyclotomicCharacter
#print axioms DkMath.FLT.Frey.Source.tateCyclotomicCharacter_mod
#print axioms DkMath.FLT.Frey.Source.residualTate_determinant_cyclotomic
#print axioms DkMath.FLT.Frey.Source.residualTateSecondCharacter_eq_cyclotomic
