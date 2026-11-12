import DkMath.FLT.FreyDyadicGeometry

#print "file: Note032DyadicGeometrySmoke"

/-! 指数37の同じSourceへの接続。中心・方向・中心固定・非自明慣性を追加入力に要求しない。 -/
namespace Note032DyadicGeometrySmoke
open DkMath.FLT.Frey DkMath.Lib.NumberTheory ValuationInertia
open EllipticCriticalCentre EllipticTangentDirections EllipticGoodReductionSeparation
open DkMath.Lib.RepresentationTheory LocalFixedCofixed
local instance : Fact (Nat.Prime 37) := ⟨by decide⟩

/-- 同じSourceに中心・方向と慣性固定を供給する。 -/
theorem source37_geometry (S : Source 37)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 2) :
    ∃ C : CriticalCentre A (S.rationalCurve.baseChange (AlgebraicClosure ℚ)),
      ∃ D : TangentDirections C,
        (∀ σ ∈ inertiaSubgroupIn A ℚ, σ C.x = C.x ∧ σ C.y = C.y) ∧
        (∀ σ ∈ inertiaSubgroupIn A ℚ, σ D.α = D.α ∧ σ D.β = D.β) :=
  S.exists_dyadic_geometry (by decide) A hA

/-- 与えられた同じ点Pの零成分外性だけから、その点を動かす元を得る。 -/
theorem source37_point_moves (S : Source 37)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 2)
    (P : S.ResidualSpace) (hP : ¬ HasSmoothReduction (S.valuationModel A) P.val) :
    ∃ τ ∈ inertiaSubgroupIn A ℚ, S.residualRepresentation τ P ≠ P :=
  S.residual_exists_inertia_ne_of_not_smooth_at_two (by decide) A hA P hP

/-- 実際のE₀[p]の真性を次工程が供給すれば、慣性非自明性が直ちに得られる。 -/
theorem source37_inertia_of_proper (S : Source 37)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 2)
    (hproper : S.residualZeroComponent A ≠ ⊤) :
    ∃ τ ∈ inertiaSubgroupIn A ℚ, ∃ P, S.residualRepresentation τ P ≠ P :=
  S.residual_exists_dyadic_inertia_ne_of_zeroComponent_ne_top (by decide) A hA hproper

/-- hnoには実際の零成分外の点と枝交換だけを幾何入力として残す。 -/
theorem source37_no_cofixed (S : Source 37)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 2)
    (hout : ∃ P : S.ResidualSpace, ¬ HasSmoothReduction (S.valuationModel A) P.val)
    (hswap : ∃ σ, ∀ P : S.ResidualSpace, ¬ HasSmoothReduction (S.valuationModel A) P.val →
      HasSmoothReduction (S.valuationModel A) (S.residualRepresentation σ P + P).val) :
    ¬ ∃ L : Submodule (ZMod 37) S.ResidualSpace, Module.finrank (ZMod 37) L = 1 ∧
      S.IsGaloisStable L ∧ IsCofixedOn S.residualRepresentation L :=
  S.residual_no_cofixed_line_of_dyadic_branch_swap (by decide) A hA hout hswap

/-- 同じ簡約済み入力から031-005の条件付き既約性にも届く。 -/
theorem source37_irreducible (S : Source 37) (hbe : Even S.b)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 2)
    (hout : ∃ P : S.ResidualSpace, ¬ HasSmoothReduction (S.valuationModel A) P.val)
    (hswap : ∃ σ, ∀ P : S.ResidualSpace, ¬ HasSmoothReduction (S.valuationModel A) P.val →
      HasSmoothReduction (S.valuationModel A) (S.residualRepresentation σ P + P).val) :
    S.ResidualIsIrreducible :=
  S.residual_isIrreducible_of_dyadic_branch_swap (by decide) hbe A hA hout hswap

end Note032DyadicGeometrySmoke
