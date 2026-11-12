/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/
import DkMath.FLT.FreyFiniteKernelSingularInverse
import DkMathTest.Lib.NumberTheory.EllipticFiniteKernelReduction

#print "file: DkMathTest.Lib.NumberTheory.EllipticFiniteKernelSingularInverse"

/-! 実3点核の7上と Source 37 の任意 q≠37 で同じ零成分逆像を検査する。 -/
namespace EllipticFiniteKernelSingularInverseTest
open WeierstrassCurve WeierstrassCurve.Affine
open DkMath.FLT.Frey DkMath.Lib.NumberTheory
open EllipticFiniteKernel EllipticTorsionRepresentation EllipticGoodReductionSeparation
open EllipticCriticalCentre EllipticTangentDirections EllipticFiniteKernelReductionTest
open ValuationInertia ValuationPrimeSupport ValuationRationalPrimeSupport WeierstrassRationalIntegralModel
open DkMath.Lib.RepresentationTheory
noncomputable local instance instDecidableEqSingularInverseTest {α : Type*} : DecidableEq α := Classical.decEq _
local instance : sample.IsElliptic := ⟨by norm_num [sample, WeierstrassCurve.Δ, b₂, b₄, b₆, b₈]⟩
noncomputable local instance instFintypeSingularInverseTest : Fintype sampleKernel := Fintype.ofFinset {0, Q, -Q} (by
  intro P
  change P ∈ ({0, Q, -Q} : Finset (Points sample)) ↔ P = 0 ∨ P = Q ∨ P = -Q
  simp only [Finset.mem_insert, Finset.mem_singleton])
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩
local instance : Fact (Nat.Prime 37) := ⟨by decide⟩
private theorem three_unit (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 7) :
    A.valuation (3 : AlgebraicClosure ℚ) = 1 :=
  valuation_intCast_eq_one_of_not_dvd A (by decide : Nat.Prime 7)
    ((ValuationSubring.mem_nonunits_iff _).mp hA) (z := 3) (by norm_num)

/-- 実3点核の7上で、同じ商の零成分逆像を同じ核による移動で判定する。
源の臨界中心と分離した二方向を明示し、標的中心や水準の深さは要求しない。 -/
theorem sample_seven_inverse (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 7)
    (C : CriticalCentre A (sample.map (algebraMap ℚ (AlgebraicClosure ℚ)))) (D : TangentDirections C)
    (P : Points sample) :
    HasSmoothReduction (valuationKernelModel sample sampleKernel 3 sample_killed A (localSource A)
      (localSource_map A) (three_unit A hA))
      (oddKernelPointMap sample sampleKernel (sampleKernel_card ▸ (by decide : Odd 3)) P) ↔
      ∃ R : sampleKernel, HasSmoothReduction (localSource A) (P - R.val) :=
  singular_kernel_smooth_iff_translate sample sampleKernel 3 sampleKernel_card (by decide) sample_killed
    A (localSource A) (localSource_map A) (three_unit A hA) C D (sample_kernel_singular_at_seven A hA) P

/-- 実3点核の7上では、中心と二方向を具体的な Δ・c₄ の計算から内部供給する。 -/
theorem sample_seven_inverse_internal_geometry (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : LiesOverPrime A 7) (P : Points sample) :
    HasSmoothReduction (valuationKernelModel sample sampleKernel 3 sample_killed A (localSource A)
      (localSource_map A) (three_unit A hA))
      (oddKernelPointMap sample sampleKernel (sampleKernel_card ▸ (by decide : Odd 3)) P) ↔
      ∃ R : sampleKernel, HasSmoothReduction (localSource A) (P - R.val) := by
  let W := sample.map (algebraMap ℚ (AlgebraicClosure ℚ))
  have hd : W.Δ = (-64484 : AlgebraicClosure ℚ) := by
    norm_num [W, sample, WeierstrassCurve.map, WeierstrassCurve.Δ, b₂, b₄, b₆, b₈]
  have hc : W.c₄ = (-167 : AlgebraicClosure ℚ) := by
    norm_num [W, sample, WeierstrassCurve.map, c₄, b₂, b₄]
  have hv := (ValuationSubring.mem_nonunits_iff _).mp hA
  have hex : Nonempty (CriticalCentre A W) := by
    apply exists_criticalCentre A W
    · rw [show W = (localSource A).map A.subtype from (localSource_map A).symm, map_a₁]
      exact (localSource A).a₁.property
    · rw [show W = (localSource A).map A.subtype from (localSource_map A).symm, map_a₂]
      exact (localSource A).a₂.property
    · rw [show W = (localSource A).map A.subtype from (localSource_map A).symm, map_a₃]
      exact (localSource A).a₃.property
    · rw [show W = (localSource A).map A.subtype from (localSource_map A).symm, map_a₄]
      exact (localSource A).a₄.property
    · rw [show W = (localSource A).map A.subtype from (localSource_map A).symm, map_a₆]
      exact (localSource A).a₆.property
    · rw [hd]; norm_num
    · rw [hd]
      simpa only [Int.cast_neg, Int.cast_ofNat] using
        valuation_intCast_lt_one_of_dvd A hv (z := -64484) (by norm_num)
    · rw [hc]
      simpa only [Int.cast_neg, Int.cast_ofNat] using
        valuation_intCast_eq_one_of_not_dvd A (by decide : Nat.Prime 7) hv (z := -167) (by norm_num)
  obtain ⟨C⟩ := hex
  have ha : W.a₁ ∈ A := by
    rw [show W = (localSource A).map A.subtype from (localSource_map A).symm, map_a₁]
    exact (localSource A).a₁.property
  have h2 : A.valuation (2 : AlgebraicClosure ℚ) = 1 :=
    valuation_intCast_eq_one_of_not_dvd A (by decide : Nat.Prime 7) hv (z := 2) (by norm_num)
  obtain ⟨D⟩ := exists_tangentDirections A W C ha h2
  exact sample_seven_inverse A hA C D P

/-- Source 37 の p 以外の全住所で、同じ既存整数標的の零成分逆像を判定する。 -/
theorem source37_integer_inverse_away (S : Source 37) (L : Submodule (ZMod 37) S.ResidualSpace)
    (hl : Module.finrank (ZMod 37) L = 1) (hst : IsStable S.residualRepresentation L)
    {q : ℕ} [Fact q.Prime] (hqp : q ≠ 37)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q) (P : Points S.rationalCurve) :
    HasSmoothReduction (integerValuationModel A (S.residualIntegerKernelModel L hl hst))
      (S.residualIntegerKernelPointHom (by decide) L hl hst P) ↔
      ∃ R : pointSubgroup S.rationalCurve 37 L, HasSmoothReduction (S.valuationModel A) (P - R.val) :=
  S.residual_integer_pointHom_smooth_iff_translate_away (by decide) L hl hst hqp A hA P

end EllipticFiniteKernelSingularInverseTest
