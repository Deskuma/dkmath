import DkMath.FLT.FreyFiniteKernelCollision
import DkMath.Lib.NumberTheory.WeierstrassNodalOrbit

#print "file: Note032NodalOrbitCollisionSmoke"

/-! 37の同じSource・核・商準同型・既存整数標的を保つ衝突点の終点。 -/
namespace Note032NodalOrbitCollisionSmoke
open WeierstrassCurve WeierstrassCurve.Affine
open DkMath.FLT.Frey DkMath.Lib.NumberTheory
open EllipticTorsionRepresentation EllipticGoodReductionSeparation ValuationInertia
open WeierstrassModelReduction WeierstrassRationalIntegralModel DkMath.Lib.RepresentationTheory
local instance : Fact (Nat.Prime 37) := ⟨by decide⟩
noncomputable local instance {α : Type*} : DecidableEq α := Classical.decEq _

/-- 同じ37点核と還元衝突する点の、同じ付値環商像は滑らかでOへ還元する。 -/
theorem source37_collision (S : Source 37) (L : Submodule (ZMod 37) S.ResidualSpace)
    (hl : Module.finrank (ZMod 37) L = 1) {q : ℕ} (hq : q.Prime) (hqp : q ≠ 37)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (P : Points S.rationalCurve) (Q : pointSubgroup S.rationalCurve 37 L)
    (hP : HasSmoothReduction (S.valuationModel A) P)
    (hQ : HasSmoothReduction (S.valuationModel A) Q.val)
    (hr : modelReduce A (S.valuationModel A) _ (S.valuationModel_map A) P =
      modelReduce A (S.valuationModel A) _ (S.valuationModel_map A) Q.val) :
    HasSmoothReduction (S.residualValuationKernelModel L hl hq hqp A hA)
        (S.residualOddKernelPointHom (by decide) L hl P) ∧
      modelReduce A (S.residualValuationKernelModel L hl hq hqp A hA) (S.residualKernelModel L hl)
        (S.residual_valuation_kernel_model_map (by decide) L hl hq hqp A hA)
        (S.residualOddKernelPointHom (by decide) L hl P) = 0 :=
  S.residual_pointHom_of_reduction_collision (by decide) L hl hq hqp A hA P Q hP hQ hr

/-- 安定性を保持して、衝突点の同じ像を既存整数標的へ運ぶ。 -/
theorem source37_integer_collision (S : Source 37) (L : Submodule (ZMod 37) S.ResidualSpace)
    (hl : Module.finrank (ZMod 37) L = 1) (hs : IsStable S.residualRepresentation L)
    {q : ℕ} (hq : q.Prime) (hqp : q ≠ 37)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (P : Points S.rationalCurve) (Q : pointSubgroup S.rationalCurve 37 L)
    (hP : HasSmoothReduction (S.valuationModel A) P)
    (hQ : HasSmoothReduction (S.valuationModel A) Q.val)
    (hr : modelReduce A (S.valuationModel A) _ (S.valuationModel_map A) P =
      modelReduce A (S.valuationModel A) _ (S.valuationModel_map A) Q.val) :
    HasSmoothReduction (integerValuationModel A (S.residualIntegerKernelModel L hl hs))
      (S.residualIntegerKernelPointHom (by decide) L hl hs P) :=
  S.residual_integer_pointHom_smooth_of_reduction_collision (by decide) L hl hs hq hqp A hA P Q hP hQ hr

end Note032NodalOrbitCollisionSmoke

#print axioms Note032NodalOrbitCollisionSmoke.source37_collision
#print axioms Note032NodalOrbitCollisionSmoke.source37_integer_collision
