import DkMath.FLT.FreyFiniteKernelZeroComponentAway

#print "file: Note032CenterAwaySmoke"

/-! 同じSource37の2・3を含む全q≠37における零成分輸送。 -/
namespace Note032CenterAwaySmoke
open WeierstrassCurve WeierstrassCurve.Affine
open DkMath.FLT.Frey DkMath.Lib.NumberTheory
open EllipticTorsionRepresentation EllipticGoodReductionSeparation
open WeierstrassRationalIntegralModel ValuationInertia DkMath.Lib.RepresentationTheory
local instance : Fact (Nat.Prime 37) := ⟨by decide⟩
noncomputable local instance {α : Type*} : DecidableEq α := Classical.decEq _

/-- 同じSource37・核・付値環標的で、37以外の全素数住所を扱う。 -/
theorem source37_away (S : Source 37) (L : Submodule (ZMod 37) S.ResidualSpace)
    (hl : Module.finrank (ZMod 37) L = 1) {q : ℕ} [Fact q.Prime] (hqp : q ≠ 37)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (P : Points S.rationalCurve) (hP : HasSmoothReduction (S.valuationModel A) P) :
    HasSmoothReduction (S.residualValuationKernelModel L hl Fact.out hqp A hA)
      (S.residualOddKernelPointHom (by decide) L hl P) :=
  S.residual_pointHom_smooth_away (by decide) L hl hqp A hA P hP

/-- 安定な同じLの既存整数標的でも、全q≠37で同じ零成分像が滑らか。 -/
theorem source37_integer_away (S : Source 37) (L : Submodule (ZMod 37) S.ResidualSpace)
    (hl : Module.finrank (ZMod 37) L = 1) (hst : IsStable S.residualRepresentation L)
    {q : ℕ} [Fact q.Prime] (hqp : q ≠ 37)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (P : Points S.rationalCurve) (hP : HasSmoothReduction (S.valuationModel A) P) :
    HasSmoothReduction (integerValuationModel A (S.residualIntegerKernelModel L hl hst))
      (S.residualIntegerKernelPointHom (by decide) L hl hst P) :=
  S.residual_integer_pointHom_smooth_away (by decide) L hl hst hqp A hA P hP

/-- 悪い2進住所では核の分岐仮定や中心一致を入力しない。 -/
theorem source37_two (S : Source 37) (L : Submodule (ZMod 37) S.ResidualSpace)
    (hl : Module.finrank (ZMod 37) L = 1)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 2)
    (P : Points S.rationalCurve) (hP : HasSmoothReduction (S.valuationModel A) P) :
    HasSmoothReduction (S.residualValuationKernelModel L hl Nat.prime_two (by decide) A hA)
      (S.residualOddKernelPointHom (by decide) L hl P) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact S.residual_pointHom_smooth_at_bad_place (by decide) L hl (by decide) (Or.inl rfl) A hA P hP

/-- 悪い3進住所も同じ核・同じ商像で扱う。 -/
theorem source37_three (S : Source 37) (L : Submodule (ZMod 37) S.ResidualSpace)
    (hl : Module.finrank (ZMod 37) L = 1) (hbad : (3 : ℤ) ∣ S.a * S.b * S.c)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 3)
    (P : Points S.rationalCurve) (hP : HasSmoothReduction (S.valuationModel A) P) :
    HasSmoothReduction (S.residualValuationKernelModel L hl (by decide) (by decide) A hA)
      (S.residualOddKernelPointHom (by decide) L hl P) := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  exact S.residual_pointHom_smooth_at_bad_place (by decide) L hl (by decide) (Or.inr hbad) A hA P hP

end Note032CenterAwaySmoke

#print axioms Note032CenterAwaySmoke.source37_away
#print axioms Note032CenterAwaySmoke.source37_integer_away
#print axioms Note032CenterAwaySmoke.source37_two
#print axioms Note032CenterAwaySmoke.source37_three
