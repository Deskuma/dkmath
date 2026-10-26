import DkMath.FLT.FreyFiniteKernelReductionSquare

#print "file: Note032ReductionSquareSmoke"

/-! Source37の同じ実点準同型・既存整数標的を固定し、2を含む一括終点を確認する。 -/
namespace Note032ReductionSquareSmoke
open WeierstrassCurve WeierstrassCurve.Affine
open DkMath.FLT.Frey DkMath.Lib.NumberTheory
open EllipticTorsionRepresentation EllipticGoodReductionSeparation ValuationInertia
open WeierstrassVariableChange WeierstrassModelReduction WeierstrassRationalIntegralModel
open DkMath.Lib.RepresentationTheory
local instance : Fact (Nat.Prime 37) := ⟨by decide⟩
noncomputable local instance {α : Type*} : DecidableEq α := Classical.decEq _

/-- 2を含む悪い住所の特異核側で、同じ実点商写像と実際の還元が可換。 -/
theorem source37_reduction_square (S : Source 37) (L : Submodule (ZMod 37) S.ResidualSpace)
    (hl : Module.finrank (ZMod 37) L = 1) {q : ℕ} [Fact q.Prime] (hqp : q ≠ 37)
    (hb : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (hd : Disjoint L (S.residualZeroComponent A)) (P : Points S.rationalCurve)
    (hP : HasSmoothReduction (S.valuationModel A) P) :
    pointEquivOfModelEq (S.residual_valuation_kernel_residue_eq_of_disjoint L hl Fact.out hqp A hA hd)
      (modelReduce A (S.residualValuationKernelModel L hl Fact.out hqp A hA) (S.residualKernelModel L hl)
        (S.residual_valuation_kernel_model_map (by decide) L hl Fact.out hqp A hA)
        (S.residualOddKernelPointHom (by decide) L hl P)) =
      modelReduce A (S.valuationModel A) (S.rationalCurve.map (algebraMap ℚ (AlgebraicClosure ℚ)))
        (S.valuationModel_map A) P :=
  S.residual_pointHom_reduction_square_at_bad_place (by decide) L hl hqp hb A hA hd P hP

/-- 同じ既存整数点準同型への輸送。安定性、Disjoint、源の滑らかさを保持する。 -/
theorem source37_integer_smooth (S : Source 37) (L : Submodule (ZMod 37) S.ResidualSpace)
    (hl : Module.finrank (ZMod 37) L = 1) (hs : IsStable S.residualRepresentation L)
    {q : ℕ} [Fact q.Prime] (hqp : q ≠ 37) (hb : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (hd : Disjoint L (S.residualZeroComponent A)) (P : Points S.rationalCurve)
    (hP : HasSmoothReduction (S.valuationModel A) P) :
    HasSmoothReduction (integerValuationModel A (S.residualIntegerKernelModel L hl hs))
      (S.residualIntegerKernelPointHom (by decide) L hl hs P) :=
  S.residual_integer_pointHom_smooth_at_bad_place_of_disjoint (by decide) L hl hs hqp hb A hA hd P hP

/-- 37以外の任意住所で、同じ整数像と同じ付値環像の条件を双方向に比較する。 -/
theorem source37_integer_smooth_iff (S : Source 37) (L : Submodule (ZMod 37) S.ResidualSpace)
    (hl : Module.finrank (ZMod 37) L = 1) (hs : IsStable S.residualRepresentation L)
    {q : ℕ} (hq : q.Prime) (hqp : q ≠ 37)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q) (P : Points S.rationalCurve) :
    HasSmoothReduction (integerValuationModel A (S.residualIntegerKernelModel L hl hs))
        (S.residualIntegerKernelPointHom (by decide) L hl hs P) ↔
      HasSmoothReduction (S.residualValuationKernelModel L hl hq hqp A hA)
        (S.residualOddKernelPointHom (by decide) L hl P) :=
  S.residual_integer_pointHom_smooth_iff (by decide) L hl hs hq hqp A hA P

end Note032ReductionSquareSmoke

#print axioms Note032ReductionSquareSmoke.source37_reduction_square
#print axioms Note032ReductionSquareSmoke.source37_integer_smooth
#print axioms Note032ReductionSquareSmoke.source37_integer_smooth_iff
