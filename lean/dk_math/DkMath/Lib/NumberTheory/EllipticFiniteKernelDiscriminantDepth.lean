/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.Lib.NumberTheory.EllipticFiniteKernelDiscriminantProduct
import DkMath.Lib.NumberTheory.EllipticFiniteKernelDepthProduct

#print "file: DkMath.Lib.NumberTheory.EllipticFiniteKernelDiscriminantDepth"

/-!
# 判別式積から局所深さへの教材入口

`EllipticFiniteKernelDepthProduct` の二つの評価定理は、商判別式と半核接線積の
積公式を `hprod` として受け取る。このファイルでは、奇数有限核について既に証明した
`kernelModel_discriminant_product_of_odd_card` をその入力へ差し込み、積公式を利用側の
仮定から DkMath 内部の定理へ置き換える。

ここで閉じるのは判別式積の局所付値への輸送であり、特異・滑らかの還元仮定、素数核の
`p`-torsion 条件、また `hno` 全体の大域算術は引き続き呼び出し側の責務として残る。
-/

namespace DkMath.Lib.NumberTheory.EllipticFiniteKernel

open WeierstrassCurve WeierstrassCurve.Affine
open EllipticTorsionRepresentation
open EllipticGoodReductionSeparation EllipticSmoothReduction
open EllipticCriticalCentre EllipticCriticalCentreAlgebra EllipticTangentDirections
open scoped BigOperators

variable {K : Type*} [Field K] [CharZero K]

/-- [DkMath.Lib] 奇素数核の特異枝で、判別式積を内部供給して源判別式の付値を得る。 -/
theorem singular_discriminant_value_of_odd_card
    (E : WeierstrassCurve K) [E.IsElliptic]
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
      A.valuation (E.map (algebraMap K (AlgebraicClosure K))).Δ := by
  have ho : Odd (Nat.card H) := hcard ▸ (Fact.out : p.Prime).odd_of_ne_two hp2
  have hprod := kernelModel_discriminant_product_of_odd_card E H ho
  rw [hcard] at hprod
  exact singular_discriminant_value_of_product_identity E H p hcard hp2 hkill A M hM hp C D hbad hprod

/-- [DkMath.Lib] 滑らかな奇数核で、判別式積を内部供給して商判別式の付値を得る。 -/
theorem smooth_discriminant_value_of_odd_card
    (E : WeierstrassCurve K) [E.IsElliptic]
    (H : AddSubgroup (Points E)) [Fintype H]
    (p : ℕ) [Fact p.Prime]
    (hkill : ∀ Q : H, p • Q.val = 0)
    (A : ValuationSubring (AlgebraicClosure K)) (M : WeierstrassCurve A)
    (hM : M.map A.subtype = E.map (algebraMap K (AlgebraicClosure K)))
    (hp : A.valuation (p : AlgebraicClosure K) = 1)
    (ho : Odd (Nat.card H))
    (hs : ∀ Q : H, HasSmoothReduction M Q.val) :
    A.valuation (kernelModel E H).Δ =
      A.valuation (E.map (algebraMap K (AlgebraicClosure K))).Δ ^ Nat.card H := by
  have hprod := kernelModel_discriminant_product_of_odd_card E H ho
  exact smooth_discriminant_value_of_product_identity E H p hkill A M hM hp ho hs hprod

end DkMath.Lib.NumberTheory.EllipticFiniteKernel
