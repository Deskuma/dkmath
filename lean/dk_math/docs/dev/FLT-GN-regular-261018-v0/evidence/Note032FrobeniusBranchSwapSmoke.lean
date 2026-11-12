import DkMath.FLT.FreyDyadicBranchSwap

#print "file: Note032FrobeniusBranchSwapSmoke"

/-! 指数37の同じSourceで、合同条件から幾何providerなしに枝交換・直接hnoを供給する。 -/
namespace Note032FrobeniusBranchSwapSmoke
open DkMath.FLT.Frey DkMath.Lib.NumberTheory ValuationInertia ValuationFrobenius
open EllipticCriticalCentre EllipticTangentDirections EllipticGoodReductionSeparation
open DkMath.Lib.RepresentationTheory LocalFixedCofixed
local instance : Fact (Nat.Prime 37) := ⟨by decide⟩

/-- 中心・方向も同時に構成し、同じFrobeniusによる交換を得る。 -/
theorem source37_directions (S : Source 37) (ha8 : S.a % 8 = 3)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 2) :
    ∃ C : CriticalCentre A (S.rationalCurve.baseChange (AlgebraicClosure ℚ)),
      ∃ D : TangentDirections C, ∃ σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ),
        IsFrobeniusAt A σ 2 ∧ σ D.α = D.β ∧ σ D.β = D.α :=
  S.exists_dyadic_direction_swap_of_a_mod_eight (by decide) ha8 A hA

/-- 同じE[37]の全ての外側の点についての枝交換。 -/
theorem source37_branch_swap (S : Source 37) (ha8 : S.a % 8 = 3)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 2) :
    ∃ σ ∈ A.decompositionSubgroup ℚ, ∀ P : S.ResidualSpace,
      ¬ HasSmoothReduction (S.valuationModel A) P.val →
        HasSmoothReduction (S.valuationModel A) (S.residualRepresentation σ P + P).val :=
  S.residual_exists_decomposition_branch_swap_of_a_mod_eight (by decide) ha8 A hA

/-- 直接hno。非自明慣性・外側の点・枝交換を入力に残さない。 -/
theorem source37_no_cofixed (S : Source 37) (ha8 : S.a % 8 = 3)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 2) :
    ¬ ∃ L : Submodule (ZMod 37) S.ResidualSpace, Module.finrank (ZMod 37) L = 1 ∧
      S.IsGaloisStable L ∧ IsCofixedOn S.residualRepresentation L :=
  S.residual_no_cofixed_line_of_a_mod_eight_at_two (by decide) ha8 A hA

/-- 同じSourceの既約性。b偶数も合同条件から内部供給する。 -/
theorem source37_irreducible (S : Source 37) (ha8 : S.a % 8 = 3)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 2) :
    S.ResidualIsIrreducible :=
  S.residual_isIrreducible_of_a_mod_eight_at_two (by decide) ha8 A hA

end Note032FrobeniusBranchSwapSmoke
