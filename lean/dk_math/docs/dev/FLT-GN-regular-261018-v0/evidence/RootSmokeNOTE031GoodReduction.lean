import DkMath

#print "file: RootSmokeNOTE031GoodReduction"

/-! NOTE-031-002B: 通常入口から同じ実際の残余表現の良い素数での慣性固定へ到達する。 -/
#check DkMath.Lib.NumberTheory.EllipticGoodReductionSeparation.slope_notMem_of_sub_mem_nonunits
#check DkMath.Lib.NumberTheory.EllipticGoodReductionInertia.torsion_eq_of_coordinate_congruence
#check DkMath.Lib.NumberTheory.EllipticGoodReductionInertia.fixed_of_inertia_of_good_model
#check DkMath.FLT.Frey.Source.residual_fixed_at_good_prime
#check DkMath.FLT.Frey.Source.residual_fixed_and_cofixed_at_good_prime

#print axioms DkMath.FLT.Frey.Source.residual_fixed_at_good_prime

open DkMath.Lib.NumberTheory.ValuationInertia
local instance : Fact (Nat.Prime 37) := ⟨by decide⟩

example (S : DkMath.FLT.Frey.Source 37) (hd : ¬ (3 : ℤ) ∣ S.a * S.b * S.c)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 3)
    (σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) (hσ : σ ∈ inertiaSubgroupIn A ℚ)
    (P : S.ResidualSpace) : S.residualRepresentation σ P = P :=
  S.residual_fixed_at_good_prime (by decide) (by decide) (by decide) hd A hA σ hσ P
