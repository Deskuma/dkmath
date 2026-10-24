import DkMath.FLT.FreyCofixedBranchSwap

#print "file: Note032Smoke"

/-! NOTE-032の条件付き入口は同じSourceと部分空間を保持する。Sourceの存在は仮定しない。 -/
namespace Note032Smoke
open DkMath.FLT.Frey DkMath.Lib.RepresentationTheory LocalFixedCofixed
open DkMath.Lib.NumberTheory ValuationInertia
open EllipticCriticalCentre EllipticTangentDirections EllipticGoodReductionSeparation
local instance : Fact (Nat.Prime 37) := ⟨by decide⟩

/-- 指数37の同じSourceに、局所の実作用の三入力を渡してhnoへ接続する。 -/
theorem source37_no_cofixed (S : Source 37)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (M : Submodule (ZMod 37) S.ResidualSpace) (hM : M ≠ ⊤)
    (habs : CofixedOn S.residualRepresentation M (inertiaSubgroupIn A ℚ))
    (hram : ∃ τ ∈ inertiaSubgroupIn A ℚ, ∃ P, S.residualRepresentation τ P ≠ P)
    (hswap : ∃ σ, ∀ P, P ∉ M → S.residualRepresentation σ P + P ∈ M) :
    ¬ ∃ L : Submodule (ZMod 37) S.ResidualSpace, Module.finrank (ZMod 37) L = 1 ∧
      S.IsGaloisStable L ∧ IsCofixedOn S.residualRepresentation L :=
  S.residual_no_cofixed_line_of_inertia_and_branch_swap (by decide) A M hM habs hram hswap

/-- hnoを入力に戻さず、局所三入力を保持した条件付き既約性を確認する。 -/
theorem source37_irreducible (S : Source 37) (hbe : Even S.b)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (M : Submodule (ZMod 37) S.ResidualSpace) (hM : M ≠ ⊤)
    (habs : CofixedOn S.residualRepresentation M (inertiaSubgroupIn A ℚ))
    (hram : ∃ τ ∈ inertiaSubgroupIn A ℚ, ∃ P, S.residualRepresentation τ P ≠ P)
    (hswap : ∃ σ, ∀ P, P ∉ M → S.residualRepresentation σ P + P ∈ M) :
    S.ResidualIsIrreducible :=
  S.residual_isIrreducible_of_inertia_and_branch_swap (by decide) hbe A M hM habs hram hswap

/-- 実際の零成分の所属は同じモデルの滑らかな還元である。 -/
theorem source37_zeroComponent_mem (S : Source 37)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (P : S.ResidualSpace) :
    P ∈ S.residualZeroComponent A ↔ HasSmoothReduction (S.valuationModel A) P.val :=
  S.mem_residualZeroComponent_iff A P

/-- 中心固定の入力を用いて実際の点の幾何から吸収を供給する。 -/
theorem source37_zeroComponent_absorbs (S : Source 37)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (C : CriticalCentre A (S.rationalCurve.baseChange (AlgebraicClosure ℚ)))
    (D : TangentDirections C)
    (hfix : ∀ τ ∈ inertiaSubgroupIn A ℚ, τ C.x = C.x ∧ τ C.y = C.y) :
    CofixedOn S.residualRepresentation (S.residualZeroComponent A) (inertiaSubgroupIn A ℚ) :=
  S.residualZeroComponent_absorbs_of_fixed_centre A C D hfix

end Note032Smoke
