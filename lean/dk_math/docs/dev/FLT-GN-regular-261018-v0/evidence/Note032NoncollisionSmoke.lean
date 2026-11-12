import DkMath.FLT.FreyFiniteKernelNoncollision

#print "file: Note032NoncollisionSmoke"

/-! 同じSource37の非衝突節点上で、同じ商Xの剰余公式を確認する。 -/
namespace Note032NoncollisionSmoke
open WeierstrassCurve WeierstrassCurve.Affine IsLocalRing
open DkMath.FLT.Frey DkMath.Lib.NumberTheory
open EllipticFiniteKernel EllipticTorsionRepresentation EllipticGoodReductionSeparation
open WeierstrassModelReduction ValuationInertia ValuationPrimeSupport ValuationRationalPrimeSupport
open DkMath.Lib.RepresentationTheory EllipticNodalTorsion.NodalTorsion
open scoped BigOperators
local instance : Fact (Nat.Prime 37) := ⟨by decide⟩
noncomputable local instance {α : Type*} : DecidableEq α := Classical.decEq _

/-- 実際のSource37の同じ核・源・点・商Xを保持する。 -/
theorem source37_nodal_noncollision (S : Source 37)
    (L : Submodule (ZMod 37) S.ResidualSpace) (hl : Module.finrank (ZMod 37) L = 1)
    {q : ℕ} (hq : q.Prime) (hqp : q ≠ 37)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (hle : L ≤ S.residualZeroComponent A) (P : Points S.rationalCurve)
    (hP : HasSmoothReduction (S.valuationModel A) P)
    (hout : ∀ Q : pointSubgroup S.rationalCurve 37 L,
      modelReduce A (S.valuationModel A) _ (S.valuationModel_map A) P ≠
        modelReduce A (S.valuationModel A) _ (S.valuationModel_map A) Q.val)
    {x₀ y₀ α : ResidueField A}
    (F : Frame ((S.valuationModel A).map (residue A)) x₀ y₀ α)
    (hsep : α ≠ -((S.valuationModel A).map (residue A)).a₁ - α) :
    letI := S.rationalCurve_isElliptic
    let H := pointSubgroup S.rationalCurve 37 L
    letI := S.finite_residualPointSubgroup L hl
    letI := Fintype.ofFinite H
    let hs := S.residual_kernel_smooth_of_le L A hle
    let hp := not_mem_of_reduction_noncollision S.rationalCurve H A (S.valuationModel A)
      (S.valuationModel_map A) P hout
    let hn : A.valuation (37 : AlgebraicClosure ℚ) = 1 := by
      simpa only [pow_one, Nat.cast_ofNat] using prime_power_value_one A (Fact.out : Nat.Prime 37) hq
        ((ValuationSubring.mem_nonunits_iff _).mp hA) hqp 1
    let hx := (kernelAt_coordinates_mem S.rationalCurve H 37 (S.residual_kernel_killed L) A
      (S.valuationModel A) (S.valuationModel_map A) hn hs P hP hout).1
    residue A ⟨kernelXAt S.rationalCurve H P hp, hx⟩ =
      (37 : ResidueField A) ^ 2 * (37 • modelReduce A (S.valuationModel A) _ (S.valuationModel_map A) P).xc +
        ((37 : ResidueField A) - (37 : ResidueField A) ^ 2) * x₀ -
        ∑ Q : H, (smoothKernelReduction S.rationalCurve H A (S.valuationModel A)
          (S.valuationModel_map A) hs Q).xc :=
  S.residual_kernelXAt_nodal_of_noncollision L hl hq hqp A hA hle P hP hout F hsep

end Note032NoncollisionSmoke

#print axioms Note032NoncollisionSmoke.source37_nodal_noncollision
