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

end DkMath.Lib.NumberTheory.EllipticFiniteKernel
