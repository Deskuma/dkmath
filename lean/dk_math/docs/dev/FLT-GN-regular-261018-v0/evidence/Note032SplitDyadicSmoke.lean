import DkMath.FLT.FreySplitDyadic

#print "file: Note032SplitDyadicSmoke"

/-! 032-005A: 同じSource37で7側の局所構造と一般hnoの未供給の入力を確認する。 -/
namespace Note032SplitDyadicSmoke
open DkMath.FLT.Frey DkMath.Lib.NumberTheory ValuationInertia
open EllipticGoodReductionSeparation
open DkMath.Lib.RepresentationTheory LocalFixedCofixed
local instance : Fact (Nat.Prime 37) := ⟨by decide⟩

/-- 7側の商は、実際の2上の分解群全体で固定される。 -/
theorem source37_decomposition_cofixed (S : Source 37) (ha7 : S.a % 8 = 7)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 2) :
    CofixedOn S.residualRepresentation (S.residualZeroComponent A) (A.decompositionSubgroup ℚ) :=
  S.residualZeroComponent_cofixed_decomposition_of_seven (by decide) ha7 A hA

/-- 3側で構成した種類の分解群の枝交換元は7側に存在しない。 -/
theorem source37_no_local_swap (S : Source 37) (ha7 : S.a % 8 = 7)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 2) :
    ¬ ∃ σ ∈ A.decompositionSubgroup ℚ, ∀ P : S.ResidualSpace,
      ¬ HasSmoothReduction (S.valuationModel A) P.val →
        HasSmoothReduction (S.valuationModel A) (S.residualRepresentation σ P + P).val :=
  S.residual_no_decomposition_branch_swap_of_seven (by decide) ha7 A hA

/-- Cofixed直線があるなら同じ零成分へ一致する。直線の存在は仮定として残す。 -/
theorem source37_candidate_identification (S : Source 37)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 2)
    (L : Submodule (ZMod 37) S.ResidualSpace) (hline : Module.finrank (ZMod 37) L = 1)
    (hcofixed : IsCofixedOn S.residualRepresentation L) : L = S.residualZeroComponent A :=
  S.residual_cofixed_line_eq_zeroComponent_at_two (by decide) A hA L hline hcofixed

/-- hnoを実際の変化量の脱出へ言い換える。右辺の存在を証明したとはしない。 -/
theorem source37_escape_contract (S : Source 37)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 2) :
    (¬ ∃ L : Submodule (ZMod 37) S.ResidualSpace, Module.finrank (ZMod 37) L = 1 ∧
      S.IsGaloisStable L ∧ IsCofixedOn S.residualRepresentation L) ↔
      ∃ σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ), ∃ P : S.ResidualSpace,
        S.residualRepresentation σ P - P ∉ S.residualZeroComponent A :=
  S.residual_hno_iff_exists_zeroComponent_escape (by decide) A hA

/-- 7側で脱出があれば、同じ分解群の外にあることが必要。 -/
theorem source37_escape_outside_decomposition (S : Source 37) (ha7 : S.a % 8 = 7)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 2)
    {σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)} {P : S.ResidualSpace}
    (hescape : S.residualRepresentation σ P - P ∉ S.residualZeroComponent A) :
    σ ∉ A.decompositionSubgroup ℚ :=
  S.residual_zeroComponent_escape_not_decomposition_of_seven (by decide) ha7 A hA hescape

end Note032SplitDyadicSmoke
