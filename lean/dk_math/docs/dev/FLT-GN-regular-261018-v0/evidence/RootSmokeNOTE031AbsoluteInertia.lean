import DkMath

#print "file: RootSmokeNOTE031AbsoluteInertia"

/-! NOTE-031-001B: 通常入口から、実際の絶対慣性と同じSourceの輸送へ到達する。 -/
#check DkMath.Lib.NumberTheory.IntegralClosureInertiaLift.exists_lift_mem_inertia_integralClosure
#check DkMath.Lib.NumberTheory.ValuationInertiaLift.FractionRepresentation.exists_integral_fraction
#check DkMath.Lib.NumberTheory.AbsoluteInertiaGeneration.exists_lift_mem_valuation_inertia
#check DkMath.Lib.NumberTheory.AbsoluteInertiaGeneration.subgroup_eq_top_of_inertia_le
#check DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.isCofixedOn_of_inertia
#check DkMath.FLT.Frey.Source.residual_isFixedOn_of_inertia
#check DkMath.FLT.Frey.Source.residual_isCofixedOn_of_inertia
#check DkMath.FLT.Frey.Source.residual_fixed_or_cofixed_of_inertia_common_side

#print axioms DkMath.Lib.NumberTheory.AbsoluteInertiaGeneration.subgroup_eq_top_of_inertia_le
#print axioms DkMath.FLT.Frey.Source.residual_isCofixedOn_of_inertia

open DkMath.Lib.NumberTheory.ValuationInertia
open DkMath.Lib.RepresentationTheory LocalFixedCofixed

local instance : Fact (Nat.Prime 37) := ⟨by decide⟩

example (S : DkMath.FLT.Frey.Source 37) (N : Submodule (ZMod 37) S.ResidualSpace)
    (hlocal : ∀ q : ℕ, q.Prime → ∀ A : ValuationSubring (AlgebraicClosure ℚ),
      LiesOverPrime A q → CofixedOn S.residualRepresentation N (inertiaSubgroupIn A ℚ)) :
    IsCofixedOn S.residualRepresentation N := S.residual_isCofixedOn_of_inertia N hlocal
