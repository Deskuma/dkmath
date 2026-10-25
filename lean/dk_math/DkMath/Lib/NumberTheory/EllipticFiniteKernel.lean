/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Translation-group and fixed-field proofs adapted from
DkMath.Lib.NumberTheory.EllipticMultiplicationFixedField, originally adapted from
P2M/Sol/S_WeierstrassCurve_Affine_eq_zero_of_forall_transEquiv_eq.lean.
Upstream blob: e82e468ec9dc155bbe1c531016cbd83735a3b037
Modified: generalize from full n-torsion to the same arbitrary actual subgroup H;
construct normalized coordinate sums and prove their translation invariance.
-/

import DkMath.Lib.NumberTheory.EllipticFunctionFieldTranslation
import DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
import Mathlib.FieldTheory.Fixed

#print "file: DkMath.Lib.NumberTheory.EllipticFiniteKernel"

/-!
# NOTE-032-005C₂a: 有限核の平行移動固定体と正規化座標和

[DkMath.Lib] 同じ曲線の実際の有限部分群Hを関数体の平行移動へ送る。
作用の忠実性から、固定体に対する関数体の次数は|H|となる。
さらにX_H=Σ_Q x(γ+Q)−Σ_Q x(Q)、Y_H=Σ_Q y(γ+Q)−Σ_Q y(Q)を構成する。
Oでの便宜的座標は0なので、定数和はHからOを除く通常の正規化と一致する。
一般点γ+Qは常に有限点であり、ここでは極での有理関数評価を行わない。

平行移動による添字の置換から、この二関数は同じHの固定体に入る。
固定体の存在・次数や不変関数の存在だけでは、商楕円曲線の方程式、非特異性、
点群準同型、isogenyの存在・次数はまだ証明されない。
-/
namespace DkMath.Lib.NumberTheory.EllipticFiniteKernel
open WeierstrassCurve WeierstrassCurve.Affine
open EllipticFunctionField EllipticTorsionRepresentation
open scoped BigOperators
variable {K : Type*} [Field K] (E : WeierstrassCurve K) [E.IsElliptic]
noncomputable local instance : DecidableEq (AlgebraicClosure K) := Classical.decEq _

/-- [DkMath.Lib] 実点の同じ部分群を関数体の平行移動自己同型へ送る。
Multiplicativeは加法と自己同型の乗法の型を合わせるためだけに使う。 -/
noncomputable def kernelTranslation (H : AddSubgroup (Points E)) :
    Multiplicative H →* ((E.toAffine⁄(AlgebraicClosure K)).FunctionField ≃ₐ[AlgebraicClosure K] (E.toAffine⁄(AlgebraicClosure K)).FunctionField) where
  toFun Q := transEquiv E (AlgebraicClosure K) Q.toAdd.val
  map_one' := by
    change transEquiv E (AlgebraicClosure K) 0 = 1
    rw [transEquiv_zero]
    rfl
  map_mul' Q R := transEquiv_add E (AlgebraicClosure K) Q.toAdd.val R.toAdd.val

/-- [DkMath.Lib] 関数体上の平行移動は同じ実点の移動量を識別する。 -/
theorem kernelTranslation_injective (H : AddSubgroup (Points E)) :
    Function.Injective (kernelTranslation E H) := by
  intro Q R he
  exact Multiplicative.toAdd.injective
    (Subtype.ext (transEquiv_injective E (AlgebraicClosure K) he))

/-- [DkMath.Lib] 同じ核の平行移動から成る実際の自己同型部分群。 -/
noncomputable def kernelTranslationGroup (H : AddSubgroup (Points E)) :
    Subgroup ((E.toAffine⁄(AlgebraicClosure K)).FunctionField ≃ₐ[AlgebraicClosure K] (E.toAffine⁄(AlgebraicClosure K)).FunctionField) := (kernelTranslation E H).range

/-- [DkMath.Lib] 忠実性により、平行移動群の位数は同じ核Hの位数である。 -/
theorem card_kernelTranslationGroup (H : AddSubgroup (Points E)) :
    Nat.card (kernelTranslationGroup E H) = Nat.card H := by
  exact (Nat.card_congr (Equiv.ofInjective (kernelTranslation E H)
    (kernelTranslation_injective E H))).symm

/-- [DkMath.Lib] 有限核の平行移動群も有限である。 -/
theorem finite_kernelTranslationGroup (H : AddSubgroup (Points E)) [Finite H] :
    Finite (kernelTranslationGroup E H) :=
  Nat.finite_of_card_ne_zero (by rw [card_kernelTranslationGroup]; exact Nat.card_ne_zero.mpr ⟨inferInstance, inferInstance⟩)

/-- [DkMath.Lib] 同じ有限核に対応する関数体の中間固定体。
楕円曲線としてのモデルを、この定義に仮定や隠れたデータとして含めない。 -/
noncomputable def kernelFixedField (H : AddSubgroup (Points E)) :
    IntermediateField (AlgebraicClosure K) (E.toAffine⁄(AlgebraicClosure K)).FunctionField :=
  IntermediateField.fixedField (kernelTranslationGroup E H)

/-- [DkMath.Lib] 有限自己同型群の固定体定理を、同じHの忠実な平行移動へ適用する。
商曲線の次数ではなく、ここで構成した関数体拡大の次数である。 -/
theorem finrank_kernelFixedField (H : AddSubgroup (Points E)) [Finite H] :
    Module.finrank (kernelFixedField E H) (E.toAffine⁄(AlgebraicClosure K)).FunctionField = Nat.card H := by
  let := finite_kernelTranslationGroup E H
  let := Fintype.ofFinite (kernelTranslationGroup E H)
  change Module.finrank (FixedPoints.subfield (kernelTranslationGroup E H) (E.toAffine⁄(AlgebraicClosure K)).FunctionField) (E.toAffine⁄(AlgebraicClosure K)).FunctionField = _
  rw [FixedPoints.finrank_eq_card, Fintype.card_eq_nat_card, card_kernelTranslationGroup]

/-- [DkMath.Lib] 同じHの固定体への所属は、Hの全ての平行移動による不変性である。 -/
theorem mem_kernelFixedField_iff (H : AddSubgroup (Points E)) (f : (E.toAffine⁄(AlgebraicClosure K)).FunctionField) :
    f ∈ kernelFixedField E H ↔ ∀ Q : H, transEquiv E (AlgebraicClosure K) Q.val f = f := by
  change f ∈ IntermediateField.fixedField (kernelTranslationGroup E H) ↔ _
  rw [IntermediateField.mem_fixedField_iff]
  constructor
  · intro h Q
    exact h (kernelTranslation E H (Multiplicative.ofAdd Q)) ⟨Multiplicative.ofAdd Q, rfl⟩
  · intro h σ hσ
    obtain ⟨Q, rfl⟩ := hσ
    exact h Q.toAdd

/-- [DkMath.Lib] 有限核の同じ平行移動の総和。係数|H|で割った平均ではない。 -/
noncomputable def kernelTrace (H : AddSubgroup (Points E)) [Fintype H] (f : (E.toAffine⁄(AlgebraicClosure K)).FunctionField) : (E.toAffine⁄(AlgebraicClosure K)).FunctionField :=
  ∑ Q : H, transEquiv E (AlgebraicClosure K) Q.val f

/-- [DkMath.Lib] 平行移動は有限核の和の添字を置換するため、同じ総和を保存する。 -/
theorem kernelTrace_translation (H : AddSubgroup (Points E)) [Fintype H] (Q : H) (f : (E.toAffine⁄(AlgebraicClosure K)).FunctionField) :
    transEquiv E (AlgebraicClosure K) Q.val (kernelTrace E H f) = kernelTrace E H f := by
  unfold kernelTrace
  rw [map_sum]
  apply Fintype.sum_equiv (Equiv.addLeft Q)
  intro R
  change transEquiv E (AlgebraicClosure K) Q.val (transEquiv E (AlgebraicClosure K) R.val f) =
    transEquiv E (AlgebraicClosure K) (Q.val + R.val) f
  exact (congrArg (fun e => e f)
    (transEquiv_add E (AlgebraicClosure K) Q.val R.val)).symm

/-- [DkMath.Lib] x座標の正規化された有限和。Oの定数座標0は補正和に寄与しない。 -/
noncomputable def veluX (H : AddSubgroup (Points E)) [Fintype H] : (E.toAffine⁄(AlgebraicClosure K)).FunctionField :=
  kernelTrace E H (genericX E (AlgebraicClosure K)) -
    algebraMap (AlgebraicClosure K) (E.toAffine⁄(AlgebraicClosure K)).FunctionField (∑ Q : H, Q.val.xc)

/-- [DkMath.Lib] y座標の正規化された有限和。曲線方程式の成立は別に証明する。 -/
noncomputable def veluY (H : AddSubgroup (Points E)) [Fintype H] : (E.toAffine⁄(AlgebraicClosure K)).FunctionField :=
  kernelTrace E H (genericY E (AlgebraicClosure K)) -
    algebraMap (AlgebraicClosure K) (E.toAffine⁄(AlgebraicClosure K)).FunctionField (∑ Q : H, Q.val.yc)

/-- [DkMath.Lib] 正規化x座標は同じ核の全ての平行移動で不変である。 -/
theorem veluX_translation (H : AddSubgroup (Points E)) [Fintype H] (Q : H) :
    transEquiv E (AlgebraicClosure K) Q.val (veluX E H) = veluX E H := by
  rw [veluX, map_sub, kernelTrace_translation, AlgEquiv.commutes]

/-- [DkMath.Lib] 正規化y座標も同じ核の平行移動で不変である。 -/
theorem veluY_translation (H : AddSubgroup (Points E)) [Fintype H] (Q : H) :
    transEquiv E (AlgebraicClosure K) Q.val (veluY E H) = veluY E H := by
  rw [veluY, map_sub, kernelTrace_translation, AlgEquiv.commutes]

/-- [DkMath.Lib] 二つの正規化関数は、同じ核で構成した中間固定体の元である。
固定体を生成するという主張や、そのモデルの楕円曲線性とは区別する。 -/
theorem velu_coordinates_mem (H : AddSubgroup (Points E)) [Fintype H] :
    veluX E H ∈ kernelFixedField E H ∧ veluY E H ∈ kernelFixedField E H :=
  ⟨(mem_kernelFixedField_iff E H _).mpr (veluX_translation E H),
    (mem_kernelFixedField_iff E H _).mpr (veluY_translation E H)⟩

end DkMath.Lib.NumberTheory.EllipticFiniteKernel
