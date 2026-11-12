/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/
import DkMath.FLT.FreyFiniteKernelZeroComponentExact
import DkMathTest.Lib.NumberTheory.EllipticFiniteKernelNodalInverse

#print "file: DkMathTest.Lib.NumberTheory.EllipticFiniteKernelZeroComponentExact"

/-! Source 37 の零成分への全射と、実3点核の特異側での厳密な群論的境界。 -/
namespace EllipticFiniteKernelZeroComponentExactTest
open WeierstrassCurve WeierstrassCurve.Affine IsLocalRing
open DkMath.FLT.Frey DkMath.Lib.NumberTheory
open EllipticFiniteKernel EllipticTorsionRepresentation EllipticGoodReductionSeparation EllipticSmoothReduction
open EllipticCriticalCentre EllipticFiniteKernelReductionTest WeierstrassRationalIntegralModel
open EllipticNodalTorsion.NodalTorsion
open ValuationInertia ValuationPrimeSupport ValuationRationalPrimeSupport
open DkMath.Lib.RepresentationTheory
noncomputable local instance {α : Type*} : DecidableEq α := Classical.decEq _
local instance : Fact (Nat.Prime 37) := ⟨by decide⟩
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- 滑らかな核側で、同じ Source 37 の既存整数標的の零成分点は源から持ち上がる。 -/
theorem source37_two_integer_lift (S : Source 37) (L : Submodule (ZMod 37) S.ResidualSpace)
    (hl : Module.finrank (ZMod 37) L = 1) (hst : IsStable S.residualRepresentation L)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 2)
    (hle : L ≤ S.residualZeroComponent A)
    (R : Points ((S.residualIntegerKernelModel L hl hst).map (Int.castRingHom ℚ)))
    (hR : HasSmoothReduction (integerValuationModel A (S.residualIntegerKernelModel L hl hst)) R) :
    ∃ P : Points S.rationalCurve, HasSmoothReduction (S.valuationModel A) P ∧
      S.residualIntegerKernelPointHom (by decide) L hl hst P = R :=
  S.residual_integer_zeroComponent_surjective_at_bad_place_of_le (by decide) L hl hst
    (by decide) (Or.inl rfl) A hA hle R hR

local instance : sample.IsElliptic := ⟨by norm_num [sample, WeierstrassCurve.Δ, b₂, b₄, b₆, b₈]⟩
noncomputable local instance : Fintype sampleKernel := Fintype.ofFinset {0, Q, -Q} (by
  intro P
  change P ∈ ({0, Q, -Q} : Finset (Points sample)) ↔ P = 0 ∨ P = Q ∨ P = -Q
  simp only [Finset.mem_insert, Finset.mem_singleton])
private theorem three_unit (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 7) :
    A.valuation (3 : AlgebraicClosure ℚ) = 1 :=
  valuation_intCast_eq_one_of_not_dvd A (by decide : Nat.Prime 7)
    ((ValuationSubring.mem_nonunits_iff _).mp hA) (z := 3) (by norm_num)

private theorem three_unit_47 (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 47) :
    A.valuation (3 : AlgebraicClosure ℚ) = 1 :=
  valuation_intCast_eq_one_of_not_dvd A (by decide : Nat.Prime 47)
    ((ValuationSubring.mem_nonunits_iff _).mp hA) (z := 3) (by norm_num)

/-- 実3点核の47上で、源零成分の同じ核による商と商標的零成分の同型を検査する。
源の中心・Frame・方向の分離は仮定として表示する。 -/
noncomputable def sample_fortySeven_zeroComponentEquiv
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 47)
    (C : CriticalCentre A (sample.map (algebraMap ℚ (AlgebraicClosure ℚ))))
    {x₀ y₀ α : ResidueField A} (F : Frame ((localSource A).map (residue A)) x₀ y₀ α)
    (hsep : α ≠ -((localSource A).map (residue A)).a₁ - α)
    (hCx : residue A ⟨C.x, C.x_mem⟩ = x₀) :
    zeroComponentSubgroup (localSource A) ⧸ zeroComponentKernel sample sampleKernel A (localSource A) (localSource_map A) ≃+
      zeroComponentSubgroup (valuationKernelModel sample sampleKernel 3 sample_killed A (localSource A)
        (localSource_map A) (three_unit_47 A hA)) := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  exact nodalZeroComponentQuotientEquiv sample sampleKernel 3 sampleKernel_card (by decide) sample_killed A
    (localSource A) (localSource_map A) (three_unit_47 A hA) (sample_kernel_smooth_at_fortySeven A hA) C F hsep hCx

/-- 実3点核の7上でも、零成分制限の全射性と E₀+H の逆像等式は同値。
この例は、全射性そのものを仮定や結論として追加しない。 -/
theorem sample_seven_surjective_iff_inverse (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : LiesOverPrime A 7) (C : CriticalCentre A (sample.map (algebraMap ℚ (AlgebraicClosure ℚ)))) :
    Function.Surjective (singularKernelZeroComponentHom sample sampleKernel A (localSource A)
      (localSource_map A) C 3 sample_killed (three_unit A hA)
      (sampleKernel_card ▸ (by decide : Odd 3)) (sample_kernel_singular_at_seven A hA)) ↔
    (zeroComponentSubgroup (valuationKernelModel sample sampleKernel 3 sample_killed A (localSource A)
      (localSource_map A) (three_unit A hA))).comap
      (modelKernelPointHom sample sampleKernel 3 sample_killed A (localSource A) (localSource_map A)
        (three_unit A hA) (sampleKernel_card ▸ (by decide : Odd 3))) =
    zeroComponentSubgroup (localSource A) ⊔ modelKernelSubgroup sample sampleKernel A (localSource A) (localSource_map A) :=
  singular_zeroComponent_surjective_iff_comap_eq sample sampleKernel 3 sample_killed A (localSource A)
    (localSource_map A) (three_unit A hA) (sampleKernel_card ▸ (by decide : Odd 3)) C
    (sample_kernel_singular_at_seven A hA)

end EllipticFiniteKernelZeroComponentExactTest
