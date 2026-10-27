import DkMath.FLT.FreyFiniteKernelDepthProduct

#print "file: Note032FreyDepthProductSmoke"

/-! Source 37 の2進特異核側では、一般積公式を保持して深さの関係へ接続する。 -/
namespace Note032FreyDepthProductSmoke
open WeierstrassCurve WeierstrassCurve.Affine
open DkMath.FLT.Frey DkMath.Lib.NumberTheory EllipticFiniteKernel EllipticTorsionRepresentation
open ValuationInertia ValuationPrimeSupport ValuationRationalPrimeSupport
local instance : Fact (Nat.Prime 37) := ⟨by decide⟩
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
noncomputable local instance instDecidableEqFreyDepthProductSmoke {α : Type*} : DecidableEq α := Classical.decEq _

/-- 源の積公式は外部仮定として明示し、同じ L・同じ商と特異核条件を保つ。 -/
theorem source37_two_singular_conditional (S : Source 37)
    (L : Submodule (ZMod 37) S.ResidualSpace) (hl : Module.finrank (ZMod 37) L = 1)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 2)
    (hd : Disjoint L (S.residualZeroComponent A))
    (hprod :
      letI := S.finite_residualPointSubgroup L hl
      letI := Fintype.ofFinite (pointSubgroup S.rationalCurve 37 L)
      (S.residualKernelModel L hl).Δ *
        (∏ Q : halfKernel S.rationalCurve (pointSubgroup S.rationalCurve 37 L),
          (2 * Q.val.val.yc + (S.rationalCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))).a₁ * Q.val.val.xc +
            (S.rationalCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))).a₃) ^ 2) ^ 4 =
        (S.rationalCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))).Δ ^ 37) :
    A.valuation (S.residualKernelModel L hl).Δ ^ 37 =
      A.valuation (S.rationalCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))).Δ :=
  S.residual_singular_discriminant_value_of_product_identity (by decide) L hl (by decide) (Or.inl rfl) A hA hd hprod
end Note032FreyDepthProductSmoke
#print axioms Note032FreyDepthProductSmoke.source37_two_singular_conditional
