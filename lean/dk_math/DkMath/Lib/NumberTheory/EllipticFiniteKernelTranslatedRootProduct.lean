/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.Lib.NumberTheory.EllipticFiniteKernelRootProduct
import DkMath.Lib.NumberTheory.WeierstrassTwoTorsionTranslateGeneral

#print "file: DkMath.Lib.NumberTheory.EllipticFiniteKernelTranslatedRootProduct"

/-!
# 半核の実点への一般 Weierstrass 根差積特殊化

一般定理 `translated_root_product_relation_general` は、有限集合上の各点が
同じ Weierstrass 方程式を満たし、かつ第一の2捩れ根と衝突しないことを入力に取る。
ここでは、その入力を実際の `halfKernel E H` に合わせる。

教材としての役割は二つある。第一に、半核点の曲線方程式は
`Point.nonsingular_xc_yc` から供給できることを示す。第二に、奇数核では
`half_x_sub_root_ne_zero` が三根すべてとの非衝突を一度に供給するので、
有限積の幾何学的非零性を個々の積因子ごとに再証明する必要がないことを示す。
二捩れ点の y 座標条件と三根の対称式は、後続の商判別式組立てで実際の二捩れ点を
選ぶ段階に残し、ここでは数学的な境界を明示的に保持する。
-/

namespace DkMath.Lib.NumberTheory.EllipticFiniteKernel

open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open EllipticFunctionField EllipticTorsionRepresentation
open DkMath.Lib.NumberTheory.WeierstrassTwoTorsionTranslateGeneral
open scoped BigOperators

noncomputable local instance instDecidableEqEllipticFiniteKernelTranslatedRootProduct
    {α : Type*} : DecidableEq α := Classical.decEq _

variable {K : Type*} [Field K] [CharZero K]
  (E : WeierstrassCurve K)
  (H : AddSubgroup (Points E)) [Fintype H]

/-- [DkMath.Lib] 一般 Weierstrass 形の根差積を実際の半核へ特殊化する。

`r₁,r₂,r₃` は源曲線を代数閉包へ写した2捩れ三根、`(e₁,t₁)` は第一根上の
2捩れ点の affine 座標である。証明は一般有限積定理を半核へ適用するだけで、
各半核点の方程式は点 API、分母の非零性は `half_x_sub_root_ne_zero` から得る。
したがって、残る `hσ₁` と `hTtwo` は「三根の一次対称式」と「選んだ2捩れ点の
y 座標条件」という、後段で明示的に消費すべき幾何学的入力として可視化される。
-/
theorem halfKernel_translated_root_product_relation
    (ho : Odd (Nat.card H))
    (r₁ r₂ r₃ t₁ : AlgebraicClosure K)
    (h₁ : (E.map (algebraMap K (AlgebraicClosure K))).twoTorsionPolynomial.toPoly.eval r₁ = 0)
    (h₂ : (E.map (algebraMap K (AlgebraicClosure K))).twoTorsionPolynomial.toPoly.eval r₂ = 0)
    (h₃ : (E.map (algebraMap K (AlgebraicClosure K))).twoTorsionPolynomial.toPoly.eval r₃ = 0)
    (h₁₂ : r₁ ≠ r₂) (h₁₃ : r₁ ≠ r₃) (h₂₃ : r₂ ≠ r₃)
    (hσ₁ : 4 * (r₁ + r₂ + r₃) = -((E.map (algebraMap K (AlgebraicClosure K))).a₁ ^ 2 +
      4 * (E.map (algebraMap K (AlgebraicClosure K))).a₂))
    (hTtwo : 2 * t₁ +
      (E.map (algebraMap K (AlgebraicClosure K))).a₁ * r₁ +
        (E.map (algebraMap K (AlgebraicClosure K))).a₃ = 0) :
    (∏ Q : halfKernel E H,
      (r₂ - (E.map (algebraMap K (AlgebraicClosure K))).toAffine.addX r₁
        Q.val.val.xc
        ((E.map (algebraMap K (AlgebraicClosure K))).toAffine.slope r₁
          Q.val.val.xc t₁ Q.val.val.yc))) *
        (∏ Q : halfKernel E H, (Q.val.val.xc - r₁)) =
      (r₂ - r₁) ^ (halfKernel E H).card *
        ∏ Q : halfKernel E H, (Q.val.val.xc - r₃) := by
  let W : WeierstrassCurve (AlgebraicClosure K) :=
    E.map (algebraMap K (AlgebraicClosure K))
  have hEq : ∀ Q : halfKernel E H,
      W.toAffine.Equation Q.val.val.xc Q.val.val.yc := by
    intro Q
    have hQ0 : Q.val.val ≠ 0 := fun hz =>
      ((mem_halfKernel E H Q.val).mp Q.property).1 (Subtype.ext hz)
    exact (Point.nonsingular_xc_yc hQ0).1
  have hxe : ∀ Q : halfKernel E H, Q.val.val.xc ≠ r₁ := by
    intro Q
    exact sub_ne_zero.mp
      (half_x_sub_root_ne_zero E H ho r₁ r₂ r₃ h₁ h₂ h₃ h₁₂ h₁₃ h₂₃ Q).1
  simpa [W] using
    (translated_root_product_relation_general W (Finset.univ : Finset (halfKernel E H))
      (fun Q : halfKernel E H => Q.val.val.xc)
      (fun Q : halfKernel E H => Q.val.val.yc)
      t₁ r₁ r₂ r₃ h₁ h₂ h₃ h₁₂ h₁₃ h₂₃ hσ₁ hTtwo
      (fun Q _ => hEq Q) (fun Q _ => hxe Q))

/-- [DkMath.Lib] 三根の分離から一次対称式も自動供給する半核版。

前定理の `hσ₁` は、呼び出し側が係数比較を再実装しないよう、
`two_torsion_root_sum` で根の評価・分離から構成できる。ここでは二捩れ点の
y 条件 `hTtwo` だけを残し、根差積の幾何学的有限積をさらに短く呼び出せる形にする。
-/
theorem halfKernel_translated_root_product_relation_of_roots
    (ho : Odd (Nat.card H))
    (r₁ r₂ r₃ t₁ : AlgebraicClosure K)
    (h₁ : (E.map (algebraMap K (AlgebraicClosure K))).twoTorsionPolynomial.toPoly.eval r₁ = 0)
    (h₂ : (E.map (algebraMap K (AlgebraicClosure K))).twoTorsionPolynomial.toPoly.eval r₂ = 0)
    (h₃ : (E.map (algebraMap K (AlgebraicClosure K))).twoTorsionPolynomial.toPoly.eval r₃ = 0)
    (h₁₂ : r₁ ≠ r₂) (h₁₃ : r₁ ≠ r₃) (h₂₃ : r₂ ≠ r₃)
    (hTtwo : 2 * t₁ +
      (E.map (algebraMap K (AlgebraicClosure K))).a₁ * r₁ +
        (E.map (algebraMap K (AlgebraicClosure K))).a₃ = 0) :
    (∏ Q : halfKernel E H,
      (r₂ - (E.map (algebraMap K (AlgebraicClosure K))).toAffine.addX r₁
        Q.val.val.xc
        ((E.map (algebraMap K (AlgebraicClosure K))).toAffine.slope r₁
          Q.val.val.xc t₁ Q.val.val.yc))) *
        (∏ Q : halfKernel E H, (Q.val.val.xc - r₁)) =
      (r₂ - r₁) ^ (halfKernel E H).card *
        ∏ Q : halfKernel E H, (Q.val.val.xc - r₃) := by
  apply halfKernel_translated_root_product_relation E H ho r₁ r₂ r₃ t₁
    h₁ h₂ h₃ h₁₂ h₁₃ h₂₃
    (two_torsion_root_sum (E.map (algebraMap K (AlgebraicClosure K)))
      h₁ h₂ h₃ h₁₂ h₁₃ h₂₃) hTtwo

/-- [DkMath.Lib] affine 2捩れ点から y 条件まで自動化した半核根差積。

`hTtwo` すら手書きせず、実際の点 `Affine.Point.some e₁ t₁ hT` と
`2T=0` から `two_torsion_y_condition` を呼び出す。これで、半核の有限積に
残る幾何学的入力は三根の分離と、選択した affine 2捩れ点そのものになる。
-/
theorem halfKernel_translated_root_product_relation_of_two_torsion
    (ho : Odd (Nat.card H))
    (r₁ r₂ r₃ t₁ : AlgebraicClosure K)
    (h₁ : (E.map (algebraMap K (AlgebraicClosure K))).twoTorsionPolynomial.toPoly.eval r₁ = 0)
    (h₂ : (E.map (algebraMap K (AlgebraicClosure K))).twoTorsionPolynomial.toPoly.eval r₂ = 0)
    (h₃ : (E.map (algebraMap K (AlgebraicClosure K))).twoTorsionPolynomial.toPoly.eval r₃ = 0)
    (h₁₂ : r₁ ≠ r₂) (h₁₃ : r₁ ≠ r₃) (h₂₃ : r₂ ≠ r₃)
    (hT : (E.map (algebraMap K (AlgebraicClosure K))).toAffine.Nonsingular r₁ t₁)
    (htor : 2 • (Affine.Point.some r₁ t₁ hT) = 0) :
    (∏ Q : halfKernel E H,
      (r₂ - (E.map (algebraMap K (AlgebraicClosure K))).toAffine.addX r₁
        Q.val.val.xc
        ((E.map (algebraMap K (AlgebraicClosure K))).toAffine.slope r₁
          Q.val.val.xc t₁ Q.val.val.yc))) *
        (∏ Q : halfKernel E H, (Q.val.val.xc - r₁)) =
      (r₂ - r₁) ^ (halfKernel E H).card *
        ∏ Q : halfKernel E H, (Q.val.val.xc - r₃) := by
  apply halfKernel_translated_root_product_relation_of_roots E H ho r₁ r₂ r₃ t₁
    h₁ h₂ h₃ h₁₂ h₁₃ h₂₃
    (two_torsion_y_condition (E.map (algebraMap K (AlgebraicClosure K))) hT htor)

end DkMath.Lib.NumberTheory.EllipticFiniteKernel
