import DkMath.FLT.FreyFiniteKernelNodalTransport

#print "file: Note032NodalTransportSmoke"

/-! Source37の同じ核・標的への条件付き全零成分輸送。 -/
namespace Note032NodalTransportSmoke
open WeierstrassCurve WeierstrassCurve.Affine IsLocalRing
open DkMath.FLT.Frey DkMath.Lib.NumberTheory
open EllipticFiniteKernel EllipticTorsionRepresentation EllipticGoodReductionSeparation
open EllipticCriticalCentre WeierstrassModelReduction ValuationInertia ValuationPrimeSupport
open ValuationRationalPrimeSupport DkMath.Lib.RepresentationTheory EllipticNodalTorsion.NodalTorsion
open scoped BigOperators
local instance : Fact (Nat.Prime 37) := ⟨by decide⟩
noncomputable local instance {α : Type*} : DecidableEq α := Classical.decEq _

/-- 候補中心一致を明示した同じSource37の全零成分輸送。 -/
theorem source37_transport (S : Source 37)
    (L : Submodule (ZMod 37) S.ResidualSpace) (hl : Module.finrank (ZMod 37) L = 1)
    {q : ℕ} (hq : q.Prime) (hqp : q ≠ 37)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (hle : L ≤ S.residualZeroComponent A) {x₀ y₀ α : ResidueField A}
    (F : Frame ((S.valuationModel A).map (residue A)) x₀ y₀ α)
    (hsep : α ≠ -((S.valuationModel A).map (residue A)).a₁ - α)
    (C : CriticalCentre A (S.residualKernelModel L hl))
    (hc : letI := S.finite_residualPointSubgroup L hl
      letI := Fintype.ofFinite (pointSubgroup S.rationalCurve 37 L)
      residue A ⟨C.x, C.x_mem⟩ = (37 : ResidueField A) * x₀ -
        ∑ Q : pointSubgroup S.rationalCurve 37 L,
          (smoothKernelReduction S.rationalCurve _ A (S.valuationModel A) (S.valuationModel_map A)
            (S.residual_kernel_smooth_of_le L A hle) Q).xc)
    (P : Points S.rationalCurve) (hP : HasSmoothReduction (S.valuationModel A) P) :
    HasSmoothReduction (S.residualValuationKernelModel L hl hq hqp A hA)
      (S.residualOddKernelPointHom hp2 L hl P) :=
  S.residual_pointHom_smooth_of_candidate (by decide) L hl hq hqp A hA hle F hsep C hc P hP

end Note032NodalTransportSmoke

#print axioms Note032NodalTransportSmoke.source37_transport
