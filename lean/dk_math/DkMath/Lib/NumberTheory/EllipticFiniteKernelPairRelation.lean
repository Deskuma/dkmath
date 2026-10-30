/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.Lib.NumberTheory.EllipticFiniteKernelDiscriminantNormalization
import DkMath.Lib.NumberTheory.EllipticFiniteKernelTranslatedRootProduct

#print "file: DkMath.Lib.NumberTheory.EllipticFiniteKernelPairRelation"

/-!
# Vélu 半核の一組の判別式組立て

ここでは、特殊ファイバー交差評価を既存の pair_relation へ接続する。
交差評価は、第一の差積を実際の kernelXAt と半核距離積から供給する。
もう一つの根差積は、一般 Weierstrass 形の有限積定理から供給できるため、
本補題ではその恒等式を明示的な入力として保持する。

この分離により、商判別式の代数組立てと、三つの2捩れ点を実際に選ぶ
幾何学的責務が混ざらない。後続の補題では
halfKernel_translated_root_product_relation_of_two_torsion と、
点加法の x 座標公式を用いて htranslated を閉じる。
-/

namespace DkMath.Lib.NumberTheory.EllipticFiniteKernel

open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open EllipticFunctionField EllipticTorsionRepresentation
open DkMath.Lib.NumberTheory.WeierstrassDiscriminantAssembly
open scoped BigOperators

noncomputable local instance instDecidableEqEllipticFiniteKernelPairRelation
    {α : Type*} : DecidableEq α := Classical.decEq _

variable {K : Type*} [Field K] [CharZero K]
  (E : WeierstrassCurve K) [E.IsElliptic]
  (H : AddSubgroup (Points E)) [Fintype H]

/-- [DkMath.Lib] 実際の半核交差評価から pair_relation の一組を作る。

Htranslated は G * Hj = (ek - ej)^n * Hl という二捩れ平行移動の根差積である。
第一の関係式は既存の veluHalf_base_special_fiber_intersection_eval から自動的に
得られる。従って、この定理が証明する新しい内容は、交差評価を hF として
pair_relation に組み込み、明示的な半核の判別式因子へ変換することである。
-/
theorem veluHalf_base_pair_relation_of_translated_root_product
    (ho : Odd (Nat.card H))
    (Pj Pk Pl : Points E)
    (hPj : Pj ∉ H) (hPk : Pk ∉ H)
    (hnegj : -Pj = Pj)
    (htranslated :
      (∏ Q : halfKernel E H, (Pk.xc - (Pj + Q.val.val).xc)) *
          (∏ Q ∈ halfKernel E H, (Q.val.xc - Pj.xc)) =
        (Pk.xc - Pj.xc) ^ (halfKernel E H).card *
          ∏ Q ∈ halfKernel E H, (Q.val.xc - Pl.xc)) :
    (kernelXAt E H Pj hPj - kernelXAt E H Pk hPk) ^ 2 *
        (∏ Q ∈ halfKernel E H, (Q.val.xc - Pj.xc)) ^ 4 *
        (∏ Q ∈ halfKernel E H, (Q.val.xc - Pk.xc)) ^ 4 =
      (Pk.xc - Pj.xc) ^ (2 * (2 * (halfKernel E H).card + 1)) *
        (∏ Q ∈ halfKernel E H, (Q.val.xc - Pl.xc)) ^ 4 := by
  let Hj : AlgebraicClosure K :=
    ∏ Q ∈ halfKernel E H, (Q.val.xc - Pj.xc)
  let Hk : AlgebraicClosure K :=
    ∏ Q ∈ halfKernel E H, (Q.val.xc - Pk.xc)
  let G : AlgebraicClosure K :=
    ∏ Q : halfKernel E H, (Pk.xc - (Pj + Q.val.val).xc)
  let Hl : AlgebraicClosure K :=
    ∏ Q ∈ halfKernel E H, (Q.val.xc - Pl.xc)
  let Xj : AlgebraicClosure K := kernelXAt E H Pj hPj
  let Xk : AlgebraicClosure K := kernelXAt E H Pk hPk
  let A : AlgebraicClosure K := Xk * Hk ^ 2
  have hF0 := veluHalf_base_special_fiber_intersection_eval E H ho Pj hPj hnegj
    (kernelXAt E H Pj hPj) rfl Pk hPk
  have hFraw :
      (Xk - Xj) * Hk ^ 2 = (Pk.xc - Pj.xc) * G ^ 2 := by
    simpa [Xj, Xk, Hk, G] using hF0
  have hF : A - Xj * Hk ^ 2 = (Pk.xc - Pj.xc) * G ^ 2 := by
    calc
      A - Xj * Hk ^ 2 = (Xk - Xj) * Hk ^ 2 := by simp only [A]; ring
      _ = (Pk.xc - Pj.xc) * G ^ 2 := hFraw
  have hA : A = Hk ^ 2 * Xk := by
    simp only [A]
    ring
  have hG : G * Hj = (Pk.xc - Pj.xc) ^ (halfKernel E H).card * Hl := by
    simpa [G, Hj, Hl] using htranslated
  simpa [A, G, Hj, Hk, Hl, Xj, Xk] using
    (pair_relation (k := AlgebraicClosure K) (halfKernel E H).card G Hj Hk Hl Xj Xk
      Pj.xc Pk.xc A hA hF hG)

/-- [DkMath.Lib] 実際の2捩れ点座標から一組の pair relation を組み立てる。

`halfKernel_translated_root_product_relation_of_points` が、第一の2捩れ点
`Pj` と任意の核外点 `Pk` に対する移動根積を自動的に供給する。ここでは
その定理を既存の交差評価へ渡し、抽象的な `htranslated` を呼び出し側から
取り除く。三つの `xc` が二捩れ三根であることと、その分離だけは、商曲線の
三枝を選ぶ幾何学的境界として明示的に残している。
-/
theorem veluHalf_base_pair_relation_of_two_torsion_points
    (ho : Odd (Nat.card H))
    (Pj Pk Pl : Points E)
    (hPj : Pj ∉ H) (hPk : Pk ∉ H)
    (hnegj : -Pj = Pj)
    (hT : (E.map (algebraMap K (AlgebraicClosure K))).toAffine.Nonsingular Pj.xc Pj.yc)
    (htor : 2 • (Affine.Point.some Pj.xc Pj.yc hT) = 0)
    (h₁ : (E.map (algebraMap K (AlgebraicClosure K))).twoTorsionPolynomial.toPoly.eval Pj.xc = 0)
    (h₂ : (E.map (algebraMap K (AlgebraicClosure K))).twoTorsionPolynomial.toPoly.eval Pk.xc = 0)
    (h₃ : (E.map (algebraMap K (AlgebraicClosure K))).twoTorsionPolynomial.toPoly.eval Pl.xc = 0)
    (h₁₂ : Pj.xc ≠ Pk.xc) (h₁₃ : Pj.xc ≠ Pl.xc)
    (h₂₃ : Pk.xc ≠ Pl.xc) :
    (kernelXAt E H Pj hPj - kernelXAt E H Pk hPk) ^ 2 *
        (∏ Q ∈ halfKernel E H, (Q.val.xc - Pj.xc)) ^ 4 *
        (∏ Q ∈ halfKernel E H, (Q.val.xc - Pk.xc)) ^ 4 =
      (Pk.xc - Pj.xc) ^ (2 * (2 * (halfKernel E H).card + 1)) *
        (∏ Q ∈ halfKernel E H, (Q.val.xc - Pl.xc)) ^ 4 := by
  have htranslated :
      (∏ Q : halfKernel E H, (Pk.xc - (Pj + Q.val.val).xc)) *
          (∏ Q ∈ halfKernel E H, (Q.val.xc - Pj.xc)) =
        (Pk.xc - Pj.xc) ^ (halfKernel E H).card *
          ∏ Q ∈ halfKernel E H, (Q.val.xc - Pl.xc) := by
    have hauto := halfKernel_translated_root_product_relation_of_points E H ho
      Pj.xc Pk.xc Pl.xc Pj.yc h₁ h₂ h₃ h₁₂ h₁₃ h₂₃ hT htor Pj hPj
      (by rfl) (by rfl)
    have hbridge_j :
        (∏ Q : halfKernel E H, (Q.val.val.xc - Pj.xc)) =
          ∏ Q ∈ halfKernel E H, (Q.val.xc - Pj.xc) := by
      exact Finset.prod_coe_sort (halfKernel E H)
        (fun Q : H => Q.val.xc - Pj.xc)
    have hbridge_l :
        (∏ Q : halfKernel E H, (Q.val.val.xc - Pl.xc)) =
          ∏ Q ∈ halfKernel E H, (Q.val.xc - Pl.xc) := by
      exact Finset.prod_coe_sort (halfKernel E H)
        (fun Q : H => Q.val.xc - Pl.xc)
    rw [← hbridge_j, ← hbridge_l]
    exact hauto
  exact veluHalf_base_pair_relation_of_translated_root_product E H ho Pj Pk Pl
    hPj hPk hnegj htranslated

omit [E.IsElliptic] in
/-- [DkMath.Lib] 奇数半核の三つの二捩れ根距離積は同時に非零である。

各積因子の非零性は `half_x_sub_root_ne_zero` が三根を一度に供給する。
`Finset.prod_ne_zero_iff` で三つの有限積へ持ち上げ、判別式組立てに必要な
共通因子の非零性を根差分の再証明なしに得る。
-/
theorem halfKernel_three_root_distance_products_ne_zero
    (ho : Odd (Nat.card H))
    (r₁ r₂ r₃ : AlgebraicClosure K)
    (h₁ : (E.map (algebraMap K (AlgebraicClosure K))).twoTorsionPolynomial.toPoly.eval r₁ = 0)
    (h₂ : (E.map (algebraMap K (AlgebraicClosure K))).twoTorsionPolynomial.toPoly.eval r₂ = 0)
    (h₃ : (E.map (algebraMap K (AlgebraicClosure K))).twoTorsionPolynomial.toPoly.eval r₃ = 0)
    (h₁₂ : r₁ ≠ r₂) (h₁₃ : r₁ ≠ r₃) (h₂₃ : r₂ ≠ r₃) :
    (∏ Q ∈ halfKernel E H, (Q.val.xc - r₁)) *
        (∏ Q ∈ halfKernel E H, (Q.val.xc - r₂)) *
        (∏ Q ∈ halfKernel E H, (Q.val.xc - r₃)) ≠ 0 := by
  have hroot (e : AlgebraicClosure K) (he : ∀ Q : halfKernel E H,
      Q.val.val.xc - e ≠ 0) :
      (∏ Q ∈ halfKernel E H, (Q.val.xc - e)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro Q hQ
    exact he ⟨Q, hQ⟩
  have h₁' := hroot r₁ (fun Q =>
    (half_x_sub_root_ne_zero E H ho r₁ r₂ r₃ h₁ h₂ h₃ h₁₂ h₁₃ h₂₃ Q).1)
  have h₂' := hroot r₂ (fun Q =>
    (half_x_sub_root_ne_zero E H ho r₁ r₂ r₃ h₁ h₂ h₃ h₁₂ h₁₃ h₂₃ Q).2.1)
  have h₃' := hroot r₃ (fun Q =>
    (half_x_sub_root_ne_zero E H ho r₁ r₂ r₃ h₁ h₂ h₃ h₁₂ h₁₃ h₂₃ Q).2.2)
  exact mul_ne_zero (mul_ne_zero h₁' h₂') h₃'

/-- [DkMath.Lib] 三つの実二捩れ枝から判別式積の代数組立てへ渡す入口。

三つの順序付き一組を `P₁₂`, `P₁₃`, `P₂₃` として生成し、既存の
`discriminant_product_of_pair_relations` に渡す。ここで `hH`、`hU`、二つの
判別式表示は、商モデルの係数計算・接線積・非衝突性を供給する境界である。
`hH` は半核の根非衝突から内部で自動生成され、`hU` と二つの判別式表示は
商モデルの係数計算・接線積を供給する境界として残る。従って本定理は、三組の
幾何学的根差積を一度に消費するが、商判別式そのものの
係数計算を隠れた仮定として導入しない。
-/
theorem veluHalf_base_discriminant_product_of_three_two_torsion_points
    (ho : Odd (Nat.card H))
    (P₁ P₂ P₃ : Points E)
    (hP₁ : P₁ ∉ H) (hP₂ : P₂ ∉ H) (hP₃ : P₃ ∉ H)
    (hneg₁ : -P₁ = P₁) (hneg₂ : -P₂ = P₂)
    (hT₁ : (E.map (algebraMap K (AlgebraicClosure K))).toAffine.Nonsingular P₁.xc P₁.yc)
    (htor₁ : 2 • (Affine.Point.some P₁.xc P₁.yc hT₁) = 0)
    (hT₂ : (E.map (algebraMap K (AlgebraicClosure K))).toAffine.Nonsingular P₂.xc P₂.yc)
    (htor₂ : 2 • (Affine.Point.some P₂.xc P₂.yc hT₂) = 0)
    (h₁ : (E.map (algebraMap K (AlgebraicClosure K))).twoTorsionPolynomial.toPoly.eval P₁.xc = 0)
    (h₂ : (E.map (algebraMap K (AlgebraicClosure K))).twoTorsionPolynomial.toPoly.eval P₂.xc = 0)
    (h₃ : (E.map (algebraMap K (AlgebraicClosure K))).twoTorsionPolynomial.toPoly.eval P₃.xc = 0)
    (h₁₂ : P₁.xc ≠ P₂.xc) (h₁₃ : P₁.xc ≠ P₃.xc)
    (h₂₃ : P₂.xc ≠ P₃.xc)
    (Δ Δ' U : AlgebraicClosure K)
    (hU : U = 4 ^ (halfKernel E H).card *
      ((∏ Q ∈ halfKernel E H, (Q.val.xc - P₁.xc)) *
        (∏ Q ∈ halfKernel E H, (Q.val.xc - P₂.xc)) *
        (∏ Q ∈ halfKernel E H, (Q.val.xc - P₃.xc))))
    (hΔ : Δ = 16 * ((P₂.xc - P₁.xc) * (P₃.xc - P₁.xc) *
      (P₃.xc - P₂.xc)) ^ 2)
    (hΔ' : Δ' = 16 *
      ((kernelXAt E H P₁ hP₁ - kernelXAt E H P₂ hP₂) *
        (kernelXAt E H P₁ hP₁ - kernelXAt E H P₃ hP₃) *
        (kernelXAt E H P₂ hP₂ - kernelXAt E H P₃ hP₃)) ^ 2) :
    Δ' * U ^ 4 = Δ ^ (2 * (halfKernel E H).card + 1) := by
  let H₁ : AlgebraicClosure K := ∏ Q ∈ halfKernel E H, (Q.val.xc - P₁.xc)
  let H₂ : AlgebraicClosure K := ∏ Q ∈ halfKernel E H, (Q.val.xc - P₂.xc)
  let H₃ : AlgebraicClosure K := ∏ Q ∈ halfKernel E H, (Q.val.xc - P₃.xc)
  let X₁ : AlgebraicClosure K := kernelXAt E H P₁ hP₁
  let X₂ : AlgebraicClosure K := kernelXAt E H P₂ hP₂
  let X₃ : AlgebraicClosure K := kernelXAt E H P₃ hP₃
  have hH := halfKernel_three_root_distance_products_ne_zero E H ho
    P₁.xc P₂.xc P₃.xc h₁ h₂ h₃ h₁₂ h₁₃ h₂₃
  have h₂₁ : P₂.xc ≠ P₁.xc := h₁₂.symm
  have P₁₂ := veluHalf_base_pair_relation_of_two_torsion_points E H ho P₁ P₂ P₃
    hP₁ hP₂ hneg₁ hT₁ htor₁ h₁ h₂ h₃ h₁₂ h₁₃ h₂₃
  have P₁₃ := veluHalf_base_pair_relation_of_two_torsion_points E H ho P₁ P₃ P₂
    hP₁ hP₃ hneg₁ hT₁ htor₁ h₁ h₃ h₂ h₁₃ h₁₂ h₂₃.symm
  have P₂₃ := veluHalf_base_pair_relation_of_two_torsion_points E H ho P₂ P₃ P₁
    hP₂ hP₃ hneg₂ hT₂ htor₂ h₂ h₃ h₁ h₂₃ h₂₁ h₁₃.symm
  exact discriminant_product_of_pair_relations (k := AlgebraicClosure K)
    (halfKernel E H).card P₁.xc P₂.xc P₃.xc X₁ X₂ X₃ Δ Δ' H₁ H₂ H₃ U hH hU hΔ hΔ'
    (by simpa [H₁, H₂, H₃, X₁, X₂, X₃] using P₁₂)
    (by simpa [H₁, H₂, H₃, X₁, X₂, X₃] using P₁₃)
    (by simpa [H₁, H₂, H₃, X₁, X₂, X₃] using P₂₃)

end DkMath.Lib.NumberTheory.EllipticFiniteKernel
