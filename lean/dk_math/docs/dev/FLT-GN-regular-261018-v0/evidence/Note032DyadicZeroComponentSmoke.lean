import DkMath.FLT.FreyDyadicZeroComponent

#print "file: Note032DyadicZeroComponentSmoke"

/-! 指数37の同じSourceで、零成分外の点と非自明慣性を外部providerなしで供給する。 -/
namespace Note032DyadicZeroComponentSmoke
open DkMath.FLT.Frey DkMath.Lib.NumberTheory ValuationInertia
open EllipticGoodReductionSeparation
open DkMath.Lib.RepresentationTheory LocalFixedCofixed
local instance : Fact (Nat.Prime 37) := ⟨by decide⟩

/-- 実際のE₀[37]は位数37の一次元真部分空間。 -/
theorem source37_zeroComponent_profile (S : Source 37)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 2) :
    Nat.card (S.residualZeroComponent A) = 37 ∧
      Module.finrank (ZMod 37) (S.residualZeroComponent A) = 1 ∧ S.residualZeroComponent A ≠ ⊤ :=
  ⟨S.residualZeroComponent_card_eq_at_two (by decide) A hA,
    S.residualZeroComponent_finrank_eq_one_at_two (by decide) A hA,
    S.residualZeroComponent_ne_top_at_two (by decide) A hA⟩

/-- 同じSourceの零成分外の点を、点の存在仮定なしに供給する。 -/
theorem source37_outside (S : Source 37)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 2) :
    ∃ P : S.ResidualSpace, ¬ HasSmoothReduction (S.valuationModel A) P.val :=
  S.residual_exists_not_smooth_at_two (by decide) A hA

/-- 同じ実際のE[37]上の慣性作用が非自明となる。 -/
theorem source37_inertia_nontrivial (S : Source 37)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 2) :
    ∃ τ ∈ inertiaSubgroupIn A ℚ, ∃ P, S.residualRepresentation τ P ≠ P :=
  S.residual_exists_dyadic_inertia_ne (by decide) A hA

/-- hno入口に残る幾何入力は枝交換だけである。 -/
theorem source37_no_cofixed (S : Source 37)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 2)
    (hswap : ∃ σ, ∀ P : S.ResidualSpace, ¬ HasSmoothReduction (S.valuationModel A) P.val →
      HasSmoothReduction (S.valuationModel A) (S.residualRepresentation σ P + P).val) :
    ¬ ∃ L : Submodule (ZMod 37) S.ResidualSpace, Module.finrank (ZMod 37) L = 1 ∧
      S.IsGaloisStable L ∧ IsCofixedOn S.residualRepresentation L :=
  S.residual_no_cofixed_line_of_branch_swap_at_two (by decide) A hA hswap

/-- 枝交換とb偶数の下で、同じSourceの既約性まで接続する。 -/
theorem source37_irreducible (S : Source 37) (hbe : Even S.b)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 2)
    (hswap : ∃ σ, ∀ P : S.ResidualSpace, ¬ HasSmoothReduction (S.valuationModel A) P.val →
      HasSmoothReduction (S.valuationModel A) (S.residualRepresentation σ P + P).val) :
    S.ResidualIsIrreducible :=
  S.residual_isIrreducible_of_branch_swap_at_two (by decide) hbe A hA hswap

end Note032DyadicZeroComponentSmoke
