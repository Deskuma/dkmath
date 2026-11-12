/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/
import DkMath.FLT.FreyFiniteKernelNodalInverse
import DkMathTest.Lib.NumberTheory.EllipticFiniteKernelReduction

#print "file: DkMathTest.Lib.NumberTheory.EllipticFiniteKernelNodalInverse"

/-! Source 37 の2進住所で、核の二つの局所分岐を区別する。 -/
namespace EllipticFiniteKernelNodalInverseTest
open WeierstrassCurve WeierstrassCurve.Affine
open DkMath.FLT.Frey DkMath.Lib.NumberTheory
open EllipticTorsionRepresentation EllipticGoodReductionSeparation WeierstrassRationalIntegralModel
open ValuationInertia ValuationPrimeSupport ValuationRationalPrimeSupport
open DkMath.Lib.RepresentationTheory
local instance : Fact (Nat.Prime 37) := ⟨by decide⟩
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
noncomputable local instance {α : Type*} : DecidableEq α := Classical.decEq _

/-- 滑らかな核側: 同じ既存整数標的の零成分への所属は源側と同値。 -/
theorem source37_two_smooth_kernel (S : Source 37) (L : Submodule (ZMod 37) S.ResidualSpace)
    (hl : Module.finrank (ZMod 37) L = 1) (hst : IsStable S.residualRepresentation L)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 2)
    (hle : L ≤ S.residualZeroComponent A) (P : Points S.rationalCurve) :
    HasSmoothReduction (integerValuationModel A (S.residualIntegerKernelModel L hl hst))
      (S.residualIntegerKernelPointHom (by decide) L hl hst P) ↔
      HasSmoothReduction (S.valuationModel A) P :=
  S.residual_integer_pointHom_smooth_iff_at_bad_place_of_le (by decide) L hl hst
    (by decide) (Or.inl rfl) A hA hle P

/-- 特異核側: 一次元核の非零点から、逆方向の実際の反例が存在する。 -/
theorem source37_two_singular_kernel (S : Source 37) (L : Submodule (ZMod 37) S.ResidualSpace)
    (hl : Module.finrank (ZMod 37) L = 1)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 2)
    (hd : Disjoint L (S.residualZeroComponent A)) :
    ∃ P : Points S.rationalCurve,
      HasSmoothReduction (S.residualValuationKernelModel L hl Nat.prime_two (by decide) A hA)
        (S.residualOddKernelPointHom (by decide) L hl P) ∧ ¬ HasSmoothReduction (S.valuationModel A) P :=
  S.exists_residual_disjoint_counterexample (by decide) L hl Nat.prime_two (by decide) A hA hd

end EllipticFiniteKernelNodalInverseTest

namespace EllipticFiniteKernelNodalInverseSample
open WeierstrassCurve WeierstrassCurve.Affine
open DkMath.Lib.NumberTheory EllipticFiniteKernel EllipticTorsionRepresentation
open EllipticFiniteKernelReductionTest EllipticGoodReductionSeparation
open ValuationInertia ValuationPrimeSupport ValuationRationalPrimeSupport
noncomputable local instance {α : Type*} : DecidableEq α := Classical.decEq _
local instance : sample.IsElliptic := ⟨by norm_num [sample, WeierstrassCurve.Δ, b₂, b₄, b₆, b₈]⟩
noncomputable local instance : Fintype sampleKernel := Fintype.ofFinset {0, Q, -Q} (by
  intro P
  change P ∈ ({0, Q, -Q} : Finset (Points sample)) ↔ P = 0 ∨ P = Q ∨ P = -Q
  simp only [Finset.mem_insert, Finset.mem_singleton])

/-- 実曲線 y²+xy+7y=x³ の非零3点核 Q は、7上で特異だが商像は滑らか。 -/
theorem sample_seven_counterexample (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 7) :
    HasSmoothReduction (valuationKernelModel sample sampleKernel 3 sample_killed A (localSource A)
      (localSource_map A) (valuation_intCast_eq_one_of_not_dvd A (by decide : Nat.Prime 7)
        ((ValuationSubring.mem_nonunits_iff _).mp hA) (z := 3) (by norm_num)))
      (oddKernelPointMap sample sampleKernel (sampleKernel_card ▸ (by decide : Odd 3)) Q) ∧
      ¬ HasSmoothReduction (localSource A) Q := by
  let R : sampleKernel := ⟨Q, Or.inr (Or.inl rfl)⟩
  have hR : R.val ≠ 0 := Point.some_ne_zero _
  exact nonsmooth_kernel_point_counterexample sample sampleKernel 3 sample_killed A (localSource A)
    (localSource_map A) _ (sampleKernel_card ▸ (by decide : Odd 3)) R
    (sample_kernel_singular_at_seven A hA R hR)

end EllipticFiniteKernelNodalInverseSample
