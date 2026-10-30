/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.Lib.NumberTheory.EllipticFiniteKernelDiscriminantDepth

#print "file: DkMathTest.Lib.NumberTheory.EllipticFiniteKernelDiscriminantDepth"

namespace DkMathTest.EllipticFiniteKernelDiscriminantDepth

open DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
open DkMath.Lib.NumberTheory.EllipticFiniteKernel
open DkMath.Lib.NumberTheory.EllipticGoodReductionSeparation
open DkMath.Lib.NumberTheory.EllipticSmoothReduction
open DkMath.Lib.NumberTheory.EllipticCriticalCentre
open DkMath.Lib.NumberTheory.EllipticCriticalCentreAlgebra
open DkMath.Lib.NumberTheory.EllipticTangentDirections
open WeierstrassCurve
open scoped BigOperators

variable {K : Type*} [Field K] [CharZero K]

/-- 教科書回帰例：特異枝の付値定理へ、判別式積を自動供給する。 -/
example (E : WeierstrassCurve K) [E.IsElliptic]
    (H : AddSubgroup (Points E)) [Fintype H]
    (p : ℕ) [Fact p.Prime]
    (hcard : Nat.card H = p) (hp2 : p ≠ 2)
    (hkill : ∀ Q : H, p • Q.val = 0)
    (A : ValuationSubring (AlgebraicClosure K)) (M : WeierstrassCurve A)
    (hM : M.map A.subtype = E.map (algebraMap K (AlgebraicClosure K)))
    (hp : A.valuation (p : AlgebraicClosure K) = 1)
    (C : CriticalCentre A (E.map (algebraMap K (AlgebraicClosure K))))
    (D : TangentDirections C)
    (hbad : ∀ Q : H, Q.val ≠ 0 → ¬ HasSmoothReduction M Q.val) :
    A.valuation (kernelModel E H).Δ ^ p =
      A.valuation (E.map (algebraMap K (AlgebraicClosure K))).Δ :=
  singular_discriminant_value_of_odd_card E H p hcard hp2 hkill A M hM hp C D hbad

/-- 教科書回帰例：滑らか枝でも同じ内部判別式積を利用する。 -/
example (E : WeierstrassCurve K) [E.IsElliptic]
    (H : AddSubgroup (Points E)) [Fintype H]
    (p : ℕ) [Fact p.Prime]
    (hkill : ∀ Q : H, p • Q.val = 0)
    (A : ValuationSubring (AlgebraicClosure K)) (M : WeierstrassCurve A)
    (hM : M.map A.subtype = E.map (algebraMap K (AlgebraicClosure K)))
    (hp : A.valuation (p : AlgebraicClosure K) = 1)
    (ho : Odd (Nat.card H))
    (hs : ∀ Q : H, HasSmoothReduction M Q.val) :
    A.valuation (kernelModel E H).Δ =
      A.valuation (E.map (algebraMap K (AlgebraicClosure K))).Δ ^ Nat.card H :=
  smooth_discriminant_value_of_odd_card E H p hkill A M hM hp ho hs

#print axioms
  DkMath.Lib.NumberTheory.EllipticFiniteKernel.singular_discriminant_value_of_odd_card
#print axioms
  DkMath.Lib.NumberTheory.EllipticFiniteKernel.smooth_discriminant_value_of_odd_card

end DkMathTest.EllipticFiniteKernelDiscriminantDepth
