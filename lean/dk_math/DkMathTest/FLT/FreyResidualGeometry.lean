/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyResidualGeometry
import DkMathTest.FLT.FreyResidualRepresentation

#print "file: DkMathTest.FLT.FreyResidualGeometry"

/-!
# NOTE-012: 有限性の幾何学的providerの回帰

Source 2は実在する曲線である。この同じ曲線の37-torsionにも有限性定理を適用することで、
仮想的なSource 37だけに依存しない検査を行う。非零2-torsion点の座標拘束も調べる。
37次のSourceでは位数仮定なしで有限性・開核・有限レベルが得られることを確認する。
次数0を除外する必要があることは、零番の除法多項式で検査する。
-/
namespace FreyResidualGeometryTest
open DkMath.FLT.Frey
open DkMath.Lib.NumberTheory
open EllipticTorsionRepresentation FreyResidualRepresentationTest

/-- 実在する曲線の37-torsionは、位数を仮定せず有限になる。 -/
theorem actualCurve37_finite : Finite (Torsion sample.rationalCurve 37) :=
  finite_torsion_of_ne_zero sample.rationalCurve 37 (by decide)

/-- 同じ実在する曲線で、37-torsion表現の有限レベルも得られる。 -/
theorem actualCurve37_finite_level : FactorsThroughFiniteLevel sample.rationalCurve 37 :=
  factorsThroughFiniteLevel_of_ne_zero sample.rationalCurve 37 (by decide)

/-- 既存の非零2-torsion点のx座標は実際の除法多項式の根になる。 -/
theorem twoPoint_coordinate_root :
    ((sample.rationalCurve.baseChange (AlgebraicClosure ℚ)).ΨSq 2).IsRoot 0 := by
  exact torsion_some_coordinate_root sample.rationalCurve 2
    zero_coordinates_nonsingular twoPoint.property

/-- Source 37の実際の残余空間の有限性。hcardやFiniteを引数に取らない。 -/
theorem source37_finite (S : Source 37) : Finite S.ResidualSpace :=
  S.residual_finite_of_ne_zero (by decide)

/-- Source 37の有限レベル条件も位数入力から独立になる。 -/
theorem source37_finite_level (S : Source 37) : S.ResidualFactorsThroughFiniteLevel := by
  have : Fact (Nat.Prime 37) := ⟨by decide⟩
  exact S.residual_factorsThroughFiniteLevel_of_prime

example (S : Source 37) : IsOpen (S.residualKernel : Set (Field.absoluteGaloisGroup ℚ)) := by
  have : Fact (Nat.Prime 37) := ⟨by decide⟩
  exact S.residualKernel_isOpen_of_prime

example (S : Source 37) :
    ∃ L : IntermediateField ℚ (AlgebraicClosure ℚ),
      FiniteDimensional ℚ L ∧ Normal ℚ L ∧ L.fixingSubgroup ≤ S.residualKernel := by
  have : Fact (Nat.Prime 37) := ⟨by decide⟩
  exact S.residual_normal_finite_level

example (E : WeierstrassCurve ℚ) : (E.ΨSq 0) = 0 := by simp

example (E : WeierstrassCurve ℚ) : Finite (Torsion E 1) := inferInstance

end FreyResidualGeometryTest
