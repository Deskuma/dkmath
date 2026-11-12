import DkMath.FLT.FreyFiniteKernelReducedHom

#print "file: Note032ReducedKernelSmoke"

/-! Source 37 の 2 進住所で、同じ商像の O への還元を同じ核の衝突で判定する。 -/
namespace Note032ReducedKernelSmoke
open WeierstrassCurve WeierstrassCurve.Affine IsLocalRing
open DkMath.FLT.Frey DkMath.Lib.NumberTheory
open EllipticFiniteKernel EllipticTorsionRepresentation EllipticGoodReductionSeparation EllipticSmoothReduction
open ValuationInertia ValuationPrimeSupport ValuationRationalPrimeSupport
local instance : Fact (Nat.Prime 37) := ⟨by decide⟩
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
noncomputable local instance {α : Type*} : DecidableEq α := Classical.decEq _

/-- 実際の商像が O へ還元するのは、源の還元点が同じ L の還元核にあるときだけ。 -/
theorem source37_two_zero_fiber (S : Source 37) (L : Submodule (ZMod 37) S.ResidualSpace)
    (hl : Module.finrank (ZMod 37) L = 1)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 2)
    (hle : L ≤ S.residualZeroComponent A) (P : zeroComponentSubgroup (S.valuationModel A)) :
    WeierstrassModelReduction.modelReduce A (S.residualValuationKernelModel L hl Nat.prime_two (by decide) A hA)
      (S.residualKernelModel L hl) (S.residual_valuation_kernel_model_map (by decide) L hl Nat.prime_two (by decide) A hA)
      (S.residualOddKernelPointHom (by decide) L hl (WeierstrassVariableChange.pointEquivOfModelEq
        (S.valuationModel_map A) P.val)) = 0 ↔
    ∃ Q : pointSubgroup S.rationalCurve 37 L,
      zeroComponentReduction (S.valuationModel A) P =
        smoothKernelReduction S.rationalCurve (pointSubgroup S.rationalCurve 37 L) A
          (S.valuationModel A) (S.valuationModel_map A) (S.residual_kernel_smooth_of_le L A hle) Q :=
  S.residual_modelReduce_eq_zero_iff_at_bad_place (by decide) L hl (by decide) (Or.inl rfl) A hA hle P
end Note032ReducedKernelSmoke

#print axioms DkMath.Lib.NumberTheory.EllipticFiniteKernel.nodalReducedHom_ne_zero_of_noncollision
#print axioms DkMath.Lib.NumberTheory.EllipticFiniteKernel.nodalReducedHom_ker_eq
#print axioms DkMath.Lib.NumberTheory.EllipticFiniteKernel.nodalReducedHom_eq_zero_iff
#print axioms DkMath.Lib.NumberTheory.EllipticFiniteKernel.nodalReducedQuotientHom_injective
#print axioms DkMath.FLT.Frey.Source.residualNodalReducedHom_eq_zero_iff
#print axioms DkMath.FLT.Frey.Source.residual_modelReduce_eq_zero_iff_at_bad_place
#print axioms Note032ReducedKernelSmoke.source37_two_zero_fiber
