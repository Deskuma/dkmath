/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Translation reindexing adapted from DkMath.Lib.NumberTheory.EllipticFiniteKernel,
originally adapted from anthropics/fermats-last-theorem,
P2M/Sol/S_WeierstrassCurve_Affine_eq_zero_of_forall_transEquiv_eq.lean.
Upstream blob: e82e468ec9dc155bbe1c531016cbd83735a3b037
Modified: use products and descend them through the existing kernelModelPull.
-/

import DkMath.Lib.NumberTheory.EllipticFiniteKernelModelMap
import DkMath.Lib.NumberTheory.EllipticPointOrderAlgebra

#print "file: DkMath.Lib.NumberTheory.EllipticFiniteKernelNorm"

/-!
# 同じ有限核の軌道積と、標的関数体への降下

[DkMath.Lib] 加法性の次の橋は、主因子を標的へ押し出しても主因子になること。
その生成関数の候補を、N_H(f)=∏_{Q∈H}t_Q(f)という実際の軌道積で構成する。
和による座標構成と同じ添字置換により、この積は同じ固定体F_Hに入る。
既存の引き戻しの像=F_Hから、同じ標的関数体の一意な元へ降下させる。

ここで証明する位数公式は、引き戻した関数の源の点Pでの位数である。
標的の像点での位数との比較、ファイバーの重複度、主因子の押し出しはまだ別の仕事。
従って軌道積の構成だけを、点写像の加法性の証明とは呼ばない。
-/
namespace DkMath.Lib.NumberTheory.EllipticFiniteKernel
open WeierstrassCurve WeierstrassCurve.Affine
open EllipticFunctionField EllipticTorsionRepresentation
open scoped BigOperators
variable {K : Type*} [Field K] (E : WeierstrassCurve K) [E.IsElliptic]
noncomputable local instance instDecidableEqEllipticFiniteKernelNorm : DecidableEq (AlgebraicClosure K) := Classical.decEq _

/-- [DkMath.Lib] 同じHの平行移動に沿う軌道積。係数による平均は行わない。 -/
noncomputable def kernelNorm (H : AddSubgroup (Points E)) [Fintype H]
    (f : (E.toAffine⁄(AlgebraicClosure K)).FunctionField) :
    (E.toAffine⁄(AlgebraicClosure K)).FunctionField :=
  ∏ Q : H, transEquiv E (AlgebraicClosure K) Q.val f

/-- [DkMath.Lib] 添字の置換から軌道積のH不変性を得る。 -/
theorem kernelNorm_translation (H : AddSubgroup (Points E)) [Fintype H] (Q : H)
    (f : (E.toAffine⁄(AlgebraicClosure K)).FunctionField) :
    transEquiv E (AlgebraicClosure K) Q.val (kernelNorm E H f) = kernelNorm E H f := by
  unfold kernelNorm
  rw [map_prod]
  apply Fintype.prod_equiv (Equiv.addLeft Q)
  intro R
  exact (congrArg (fun e => e f)
    (transEquiv_add E (AlgebraicClosure K) Q.val R.val)).symm

/-- [DkMath.Lib] 軌道積は既存の同じ固定体に入る。 -/
theorem kernelNorm_mem (H : AddSubgroup (Points E)) [Fintype H]
    (f : (E.toAffine⁄(AlgebraicClosure K)).FunctionField) :
    kernelNorm E H f ∈ kernelFixedField E H :=
  (mem_kernelFixedField_iff E H _).mpr (fun Q => kernelNorm_translation E H Q f)

/-- [DkMath.Lib] 同じ軌道積の乗法性。加法性は主張しない。 -/
theorem kernelNorm_mul (H : AddSubgroup (Points E)) [Fintype H]
    (f g : (E.toAffine⁄(AlgebraicClosure K)).FunctionField) :
    kernelNorm E H (f * g) = kernelNorm E H f * kernelNorm E H g := by
  simp only [kernelNorm, map_mul, Finset.prod_mul_distrib]

/-- [DkMath.Lib] 非零関数の軌道積は非零。各平行移動が自己同型であることを使う。 -/
theorem kernelNorm_ne_zero (H : AddSubgroup (Points E)) [Fintype H]
    (f : (E.toAffine⁄(AlgebraicClosure K)).FunctionField) (hf : f ≠ 0) : kernelNorm E H f ≠ 0 := by
  exact Finset.prod_ne_zero_iff.mpr (fun Q _ => (transEquiv E _ Q.val).map_ne_zero_iff.mpr hf)

/-- [DkMath.Lib] 固定関数の軌道積は|H|乗である。 -/
theorem kernelNorm_of_mem (H : AddSubgroup (Points E)) [Fintype H]
    (f : (E.toAffine⁄(AlgebraicClosure K)).FunctionField) (hf : f ∈ kernelFixedField E H) :
    kernelNorm E H f = f ^ Fintype.card H := by
  simp only [kernelNorm, (mem_kernelFixedField_iff E H f).mp hf, Finset.prod_const,
    Finset.card_univ]

/-- [DkMath.Lib] 軌道積の全点付値は、同じH剰余類上の付値の積である。
無限遠点を含む既存の平行移動付値公式を使う。 -/
theorem pointValuation_kernelNorm (H : AddSubgroup (Points E)) [Fintype H]
    (P : Points E) (f : (E.toAffine⁄(AlgebraicClosure K)).FunctionField) :
    pointValuation E P (kernelNorm E H f) = ∏ Q : H, pointValuation E (P + Q.val) f := by
  rw [kernelNorm, map_prod]
  exact Finset.prod_congr rfl (fun Q _ => pointValuation_transEquiv E P Q.val f)

/-- [DkMath.Lib] 同じ軌道積の源での整数位数は、剰余類上の整数位数の和。
これは標的の像点での位数の公式ではない。 -/
theorem pointOrder_kernelNorm (H : AddSubgroup (Points E)) [Fintype H]
    (P : Points E) (f : (E.toAffine⁄(AlgebraicClosure K)).FunctionField) (hf : f ≠ 0) :
    pointOrder E P (kernelNorm E H f) (kernelNorm_ne_zero E H f hf) =
      ∑ Q : H, pointOrder E (P + Q.val) f hf := by
  have hp := pointOrder_prod E P Finset.univ
    (fun Q : H => transEquiv E (AlgebraicClosure K) Q.val f)
    (fun Q => (transEquiv E _ Q.val).map_ne_zero_iff.mpr hf)
  exact hp.trans (Finset.sum_congr rfl (fun Q _ => pointOrder_transEquiv E P Q.val f hf))

variable [CharZero K]

/-- [DkMath.Lib] 軌道積を、同じ標的関数体の一意な関数として実現する。
同じkernelModelPullの像定理を使うため、別の商体や別の商曲線を選ばない。 -/
theorem existsUnique_kernelModelNorm (H : AddSubgroup (Points E)) [Fintype H]
    (f : (E.toAffine⁄(AlgebraicClosure K)).FunctionField) :
    ∃! g : (kernelModel E H).toAffine.FunctionField, kernelModelPull E H g = kernelNorm E H f := by
  have hm : kernelNorm E H f ∈ (kernelModelPull E H).fieldRange := by
    rw [kernelModelPull_fieldRange]
    exact kernelNorm_mem E H f
  obtain ⟨g, hg⟩ := AlgHom.mem_fieldRange.mp hm
  exact ⟨g, hg, fun g' hg' => (kernelModelPull E H).injective (hg'.trans hg.symm)⟩

/-- [DkMath.Lib] 同じ標的関数体へ降ろした軌道積。主因子輸送の生成関数候補。 -/
noncomputable def kernelModelNorm (H : AddSubgroup (Points E)) [Fintype H]
    (f : (E.toAffine⁄(AlgebraicClosure K)).FunctionField) :
    (kernelModel E H).toAffine.FunctionField := (existsUnique_kernelModelNorm E H f).exists.choose

/-- [DkMath.Lib] 標的の関数を引き戻すと、実際のH軌道積に一致する。 -/
theorem kernelModelPull_norm (H : AddSubgroup (Points E)) [Fintype H]
    (f : (E.toAffine⁄(AlgebraicClosure K)).FunctionField) :
    kernelModelPull E H (kernelModelNorm E H f) = kernelNorm E H f :=
  (existsUnique_kernelModelNorm E H f).exists.choose_spec

/-- [DkMath.Lib] 降下した軌道積も乗法的。同じ引き戻しの単射性で証明する。 -/
theorem kernelModelNorm_mul (H : AddSubgroup (Points E)) [Fintype H]
    (f g : (E.toAffine⁄(AlgebraicClosure K)).FunctionField) :
    kernelModelNorm E H (f * g) = kernelModelNorm E H f * kernelModelNorm E H g := by
  apply (kernelModelPull E H).injective
  change kernelModelPull E H (kernelModelNorm E H (f * g)) =
    kernelModelPull E H (kernelModelNorm E H f * kernelModelNorm E H g)
  rw [map_mul]
  rw [kernelModelPull_norm, kernelModelPull_norm, kernelModelPull_norm, kernelNorm_mul]

/-- [DkMath.Lib] 標的へ降りた同じ生成関数も非零。 -/
theorem kernelModelNorm_ne_zero (H : AddSubgroup (Points E)) [Fintype H]
    (f : (E.toAffine⁄(AlgebraicClosure K)).FunctionField) (hf : f ≠ 0) :
    kernelModelNorm E H f ≠ 0 := by
  intro h
  have he := kernelModelPull_norm E H f
  rw [h, map_zero] at he
  exact kernelNorm_ne_zero E H f hf he.symm

/-- [DkMath.Lib] 標的関数を引き戻してから軌道積を降ろすと|H|乗となる。
関数体の次数|H|と整合するが、点写像の加法性は使用しない。 -/
theorem kernelModelNorm_pull (H : AddSubgroup (Points E)) [Fintype H]
    (g : (kernelModel E H).toAffine.FunctionField) :
    kernelModelNorm E H (kernelModelPull E H g) = g ^ Fintype.card H := by
  apply (kernelModelPull E H).injective
  change kernelModelPull E H (kernelModelNorm E H (kernelModelPull E H g)) =
    kernelModelPull E H (g ^ Fintype.card H)
  rw [kernelModelPull_norm, map_pow]
  apply kernelNorm_of_mem
  rw [← kernelModelPull_fieldRange]
  exact AlgHom.mem_fieldRange.mpr ⟨g, rfl⟩

end DkMath.Lib.NumberTheory.EllipticFiniteKernel
