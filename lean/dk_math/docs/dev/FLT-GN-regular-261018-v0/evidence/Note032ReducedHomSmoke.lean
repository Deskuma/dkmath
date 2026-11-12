import DkMath.FLT.FreyFiniteKernelReducedHom

#print "file: Note032ReducedHomSmoke"

/-! 同じSource37の零成分の実際の還元像と同じ商標的の可換図式。 -/
namespace Note032ReducedHomSmoke
open WeierstrassCurve WeierstrassCurve.Affine IsLocalRing
open DkMath.FLT.Frey DkMath.Lib.NumberTheory
open EllipticFiniteKernel EllipticTorsionRepresentation EllipticGoodReductionSeparation EllipticSmoothReduction
open ValuationInertia ValuationPrimeSupport ValuationRationalPrimeSupport
open DkMath.Lib.RepresentationTheory EllipticNodalTorsion.NodalTorsion
local instance : Fact (Nat.Prime 37) := ⟨by decide⟩
noncomputable local instance {α : Type*} : DecidableEq α := Classical.decEq _

/-- 同じSource37・L・源と標的のモデルを保つ実際の可換図式。 -/
theorem source37_commutes (S : Source 37)
    (L : Submodule (ZMod 37) S.ResidualSpace) (hl : Module.finrank (ZMod 37) L = 1)
    {q : ℕ} (hq : q.Prime) (hqp : q ≠ 37)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (hle : L ≤ S.residualZeroComponent A) {x₀ y₀ α : ResidueField A}
    (F : Frame ((S.valuationModel A).map (residue A)) x₀ y₀ α)
    (hsep : α ≠ -((S.valuationModel A).map (residue A)).a₁ - α)
    (P : zeroComponentSubgroup (S.valuationModel A)) :
    S.residualNodalReducedHom (by decide) L hl hq hqp A hA hle F hsep
        ⟨zeroComponentReduction (S.valuationModel A) P, ⟨P, rfl⟩⟩ =
      letI := S.rationalCurve_isElliptic
      letI := S.finite_residualPointSubgroup L hl
      letI := Fintype.ofFinite (pointSubgroup S.rationalCurve 37 L)
      let hn : A.valuation (37 : AlgebraicClosure ℚ) = 1 := by
        simpa only [pow_one, Nat.cast_ofNat] using prime_power_value_one A (Fact.out : Nat.Prime 37) hq
          ((ValuationSubring.mem_nonunits_iff _).mp hA) hqp 1
      zeroComponentReduction (S.residualValuationKernelModel L hl hq hqp A hA)
        (nodalZeroComponentHom S.rationalCurve (pointSubgroup S.rationalCurve 37 L) 37
          (card_pointSubgroup S.rationalCurve 37 L hl) (by decide) (S.residual_kernel_killed L) A
          (S.valuationModel A) (S.valuationModel_map A) hn (S.residual_kernel_smooth_of_le L A hle) F hsep P) :=
  S.residualNodalReducedHom_commutes (by decide) L hl hq hqp A hA hle F hsep P

/-- 悪い2進住所では、源のFrameを内部供給して同じ還元像上の可換準同型を構成する。 -/
theorem source37_two_exists (S : Source 37) (L : Submodule (ZMod 37) S.ResidualSpace)
    (hl : Module.finrank (ZMod 37) L = 1)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 2)
    (hle : L ≤ S.residualZeroComponent A) :
    ∃ ψ : (zeroComponentReduction (S.valuationModel A)).range →+
        ((S.residualValuationKernelModel L hl Nat.prime_two (by decide) A hA).map (residue A)).toAffine.Point,
      ∀ P : zeroComponentSubgroup (S.valuationModel A),
        ψ ⟨zeroComponentReduction (S.valuationModel A) P, ⟨P, rfl⟩⟩ =
          WeierstrassModelReduction.modelReduce A (S.residualValuationKernelModel L hl Nat.prime_two (by decide) A hA)
            (S.residualKernelModel L hl) (S.residual_valuation_kernel_model_map (by decide) L hl Nat.prime_two (by decide) A hA)
            (S.residualOddKernelPointHom (by decide) L hl (WeierstrassVariableChange.pointEquivOfModelEq
              (S.valuationModel_map A) P.val)) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact S.exists_residualNodalReducedHom_at_bad_place (by decide) L hl (by decide) (Or.inl rfl) A hA hle

end Note032ReducedHomSmoke

#print axioms Note032ReducedHomSmoke.source37_commutes
#print axioms Note032ReducedHomSmoke.source37_two_exists
