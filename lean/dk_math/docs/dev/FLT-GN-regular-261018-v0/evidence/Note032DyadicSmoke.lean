import DkMath.FLT.FreyDyadicNontrivial

#print "file: Note032DyadicSmoke"

/-! 指数37の同じSourceを保った接続の検証。Sourceの存在は主張しない。 -/
namespace Note032DyadicSmoke
open DkMath.FLT.Frey DkMath.Lib.NumberTheory ValuationInertia
open EllipticCriticalCentre EllipticTangentDirections EllipticGoodReductionSeparation
open DkMath.Lib.RepresentationTheory LocalFixedCofixed
local instance : Fact (Nat.Prime 37) := ⟨by decide⟩

/-- 既存の深さ障害が自然数値の整数判別式へ届く。 -/
theorem source37_depth (S : Source 37) : ¬ 37 ∣ padicValInt 2 S.curve.Δ :=
  S.not_exponent_dvd_curve_two_valuation (by decide)

/-- 供給された零成分外の点Pそのものを動かす元を得る。 -/
theorem source37_point_moves (S : Source 37)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 2)
    (C : CriticalCentre A (S.rationalCurve.baseChange (AlgebraicClosure ℚ)))
    (D : TangentDirections C)
    (hfix : ∀ τ ∈ inertiaSubgroupIn A ℚ, τ C.x = C.x)
    (P : S.ResidualSpace) (hP : ¬ HasSmoothReduction (S.valuationModel A) P.val) :
    ∃ τ ∈ inertiaSubgroupIn A ℚ, S.residualRepresentation τ P ≠ P :=
  S.residual_exists_inertia_ne_of_not_smooth (by decide) A hA C D hfix P hP

/-- 非自明慣性を仮定に要求しない、新しい条件付きhno入口。 -/
theorem source37_no_cofixed (S : Source 37)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 2)
    (C : CriticalCentre A (S.rationalCurve.baseChange (AlgebraicClosure ℚ)))
    (D : TangentDirections C)
    (hfix : ∀ τ ∈ inertiaSubgroupIn A ℚ, τ C.x = C.x ∧ τ C.y = C.y)
    (hout : ∃ P : S.ResidualSpace, ¬ HasSmoothReduction (S.valuationModel A) P.val)
    (hswap : ∃ σ, ∀ P : S.ResidualSpace, ¬ HasSmoothReduction (S.valuationModel A) P.val →
      HasSmoothReduction (S.valuationModel A) (S.residualRepresentation σ P + P).val) :
    ¬ ∃ L : Submodule (ZMod 37) S.ResidualSpace, Module.finrank (ZMod 37) L = 1 ∧
      S.IsGaloisStable L ∧ IsCofixedOn S.residualRepresentation L :=
  S.residual_no_cofixed_line_of_dyadic_geometry (by decide) A hA C D hfix hout hswap

/-- 031-005の既約性への接続も同じSourceで確認する。幾何の入力は明示したまま。 -/
theorem source37_irreducible (S : Source 37) (hbe : Even S.b)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 2)
    (C : CriticalCentre A (S.rationalCurve.baseChange (AlgebraicClosure ℚ)))
    (D : TangentDirections C)
    (hfix : ∀ τ ∈ inertiaSubgroupIn A ℚ, τ C.x = C.x ∧ τ C.y = C.y)
    (hout : ∃ P : S.ResidualSpace, ¬ HasSmoothReduction (S.valuationModel A) P.val)
    (hswap : ∃ σ, ∀ P : S.ResidualSpace, ¬ HasSmoothReduction (S.valuationModel A) P.val →
      HasSmoothReduction (S.valuationModel A) (S.residualRepresentation σ P + P).val) :
    S.ResidualIsIrreducible :=
  S.residual_isIrreducible_of_oriented_cofixed_obstruction (by decide) hbe
    (source37_no_cofixed S A hA C D hfix hout hswap)

end Note032DyadicSmoke
