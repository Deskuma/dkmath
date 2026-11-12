import DkMath

#print "file: RootSmokeNOTE031ValuationArithmetic"

/-! NOTE-031-002A: 通常入口から付値環算術・実際のtorsion座標・慣性合同へ到達する。 -/
#check DkMath.Lib.Algebra.ValuationPolynomial.valuation_root_le_one
#check DkMath.Lib.NumberTheory.ValuationPrimeSupport.valuation_intCast_eq_pow_padicValInt
#check DkMath.Lib.NumberTheory.ValuationPrimeSupport.charP_residueField
#check DkMath.Lib.NumberTheory.EllipticTorsionValuationIntegrality.torsion_coordinates_mem
#check DkMath.FLT.Frey.Source.valuation_reduction_isElliptic
#check DkMath.FLT.Frey.Source.residual_coordinates_mem
#check DkMath.FLT.Frey.Source.residual_inertia_coordinate_congruence

#print axioms DkMath.Lib.NumberTheory.EllipticTorsionValuationIntegrality.torsion_coordinates_mem
#print axioms DkMath.FLT.Frey.Source.residual_inertia_coordinate_congruence

open DkMath.Lib.NumberTheory.ValuationInertia
open WeierstrassCurve
noncomputable local instance instDecidableEqRootSmokeNOTE031ValuationArithmetic :
    DecidableEq (AlgebraicClosure ℚ) := Classical.decEq _
local instance : Fact (Nat.Prime 37) := ⟨by decide⟩

example (S : DkMath.FLT.Frey.Source 37)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 3)
    {x y : AlgebraicClosure ℚ} (h : (S.rationalCurve.baseChange (AlgebraicClosure ℚ)).toAffine.Nonsingular x y)
    (ht : 37 • (Affine.Point.some x y h) = 0) : x ∈ A ∧ y ∈ A :=
  S.residual_coordinates_mem (by decide) (by decide) A hA h ht
