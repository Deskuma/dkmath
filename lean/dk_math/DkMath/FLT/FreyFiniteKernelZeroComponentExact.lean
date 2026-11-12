/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/
import DkMath.FLT.FreyFiniteKernelNodalInverse
import DkMath.Lib.NumberTheory.EllipticFiniteKernelZeroComponentExact

#print "file: DkMath.FLT.FreyFiniteKernelZeroComponentExact"

/-!
# Frey の滑らかな核側の零成分への全射

同じ一次元核と商準同型の全点全射性を、零成分の逆像判定に結合する。
これは代数閉包上の点の持上げであり、剰余点の持上げを意味しない。
-/
namespace DkMath.FLT.Frey.Source
open WeierstrassCurve WeierstrassCurve.Affine
open DkMath.Lib.NumberTheory EllipticFiniteKernel EllipticTorsionRepresentation
open EllipticGoodReductionSeparation WeierstrassRationalIntegralModel
open ValuationInertia ValuationPrimeSupport ValuationRationalPrimeSupport
open DkMath.Lib.RepresentationTheory
noncomputable local instance {α : Type*} : DecidableEq α := Classical.decEq _
variable {p : ℕ} [Fact p.Prime] (S : Source p)
local instance : S.rationalCurve.IsElliptic := S.rationalCurve_isElliptic

/-- 滑らかな核側の悪い住所では、標的の任意の幾何学的零成分点は
同じ商準同型による源の零成分点の像である。 -/
theorem residual_zeroComponent_surjective_at_bad_place_of_le (hp5 : 5 ≤ p)
    (L : Submodule (ZMod p) S.ResidualSpace) (hl : Module.finrank (ZMod p) L = 1)
    {q : ℕ} [Fact q.Prime] (hqp : q ≠ p) (hbad : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (hle : L ≤ S.residualZeroComponent A) (R : (S.residualKernelModel L hl).toAffine.Point)
    (hR : HasSmoothReduction (S.residualValuationKernelModel L hl Fact.out hqp A hA) R) :
    ∃ P : Points S.rationalCurve, HasSmoothReduction (S.valuationModel A) P ∧
      S.residualOddKernelPointHom (by omega) L hl P = R := by
  obtain ⟨P, hP⟩ := S.residual_odd_kernel_pointHom_surjective (by omega) L hl R
  refine ⟨P, ?_, hP⟩
  apply (S.residual_pointHom_smooth_iff_at_bad_place_of_le hp5 L hl hqp hbad A hA hle P).mp
  exact hP.symm ▸ hR

/-- 安定な同じ核の既存整数標的でも、幾何学的零成分の各点は源零成分から持ち上がる。
整数標的の全点全射性と同じ整数化点準同型を使う。 -/
theorem residual_integer_zeroComponent_surjective_at_bad_place_of_le (hp5 : 5 ≤ p)
    (L : Submodule (ZMod p) S.ResidualSpace) (hl : Module.finrank (ZMod p) L = 1)
    (hst : IsStable S.residualRepresentation L) {q : ℕ} [Fact q.Prime]
    (hqp : q ≠ p) (hbad : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (hle : L ≤ S.residualZeroComponent A)
    (R : Points ((S.residualIntegerKernelModel L hl hst).map (Int.castRingHom ℚ)))
    (hR : HasSmoothReduction (integerValuationModel A (S.residualIntegerKernelModel L hl hst)) R) :
    ∃ P : Points S.rationalCurve, HasSmoothReduction (S.valuationModel A) P ∧
      S.residualIntegerKernelPointHom (by omega) L hl hst P = R := by
  obtain ⟨P, hP⟩ := S.residual_integer_kernel_pointHom_surjective (by omega) L hl hst R
  refine ⟨P, ?_, hP⟩
  apply (S.residual_integer_pointHom_smooth_iff_at_bad_place_of_le hp5 L hl hst hqp hbad A hA hle P).mp
  exact hP.symm ▸ hR

end DkMath.FLT.Frey.Source
