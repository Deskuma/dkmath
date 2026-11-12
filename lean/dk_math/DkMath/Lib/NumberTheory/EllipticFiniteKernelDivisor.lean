/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.EllipticFiniteKernelSurjective
import DkMath.Lib.NumberTheory.ValuationDivisor
import Mathlib.GroupTheory.QuotientGroup.Basic

#print "file: DkMath.Lib.NumberTheory.EllipticFiniteKernelDivisor"

/-!
# 同じ全点関数に沿う、有限支持因子と主因子の大域輸送

[DkMath.Lib] 既存の全点関数φに沿って点の整数重みを足し合わせる。
全ファイバー=H軌道と全射性により、この押し出しの全ての標的係数を軌道和で計算できる。
主因子D=div(f)の押し出しは、同じkernelModelNorm(f)の主因子になる。
主因子で割った因子群の間にも加法準同型を構成する。

この加法準同型は因子類の間のもの。点群の加法性を同じ型で代用しない。
-/
namespace DkMath.Lib.NumberTheory.EllipticFiniteKernel
open WeierstrassCurve WeierstrassCurve.Affine WithZero
open EllipticTorsionRepresentation
open scoped BigOperators
variable {K : Type*} [Field K] [CharZero K] (E : WeierstrassCurve K) [E.IsElliptic]
noncomputable local instance instDecidableEqEllipticFiniteKernelDivisor {α : Type*} :
    DecidableEq α := Classical.decEq _

/-- [DkMath.Lib] 同じ全点関数に沿う有限支持因子の押し出し。点の重みを加算する。 -/
noncomputable def kernelDivisorPush (H : AddSubgroup (Points E)) [Fintype H]
    (hodd : Odd (Nat.card H)) :
    (Points E →₀ ℤ) →+ ((kernelModel E H).toAffine.Point →₀ ℤ) :=
  Finsupp.mapDomain.addMonoidHom (oddKernelPointMap E H hodd)

/-- [DkMath.Lib] 同じ押し出しの像点での係数は、正確に同じH軌道の重みの和。 -/
theorem kernelDivisorPush_apply_image (H : AddSubgroup (Points E)) [Fintype H]
    (hodd : Odd (Nat.card H)) (D : Points E →₀ ℤ) (P : Points E) :
    kernelDivisorPush E H hodd D (oddKernelPointMap E H hodd P) = ∑ Q : H, D (P + Q.val) := by
  induction D using Finsupp.induction_linear with
  | zero => simp
  | add D C hd hc => simp only [map_add, Finsupp.add_apply, hd, hc, Finset.sum_add_distrib]
  | single R n =>
    change Finsupp.mapDomain (oddKernelPointMap E H hodd) (Finsupp.single R n) _ = _
    rw [Finsupp.mapDomain_single, Finsupp.single_apply]
    by_cases he : oddKernelPointMap E H hodd R = oddKernelPointMap E H hodd P
    · rw [ite_eq_left he]
      have hm := (oddKernelPointMap_eq_iff_sub_mem E H hodd P R).mp he.symm
      let q : H := ⟨R - P, hm⟩
      have hr : R = P + q.val := by change R = P + (R - P); abel
      symm
      rw [Fintype.sum_eq_single q (fun Q hQ => ?_)]
      · rw [← hr]
        exact Finsupp.single_eq_same
      · rw [Finsupp.single_apply, ite_eq_right]
        intro hh
        apply hQ
        exact Subtype.ext (add_left_cancel (hh.symm.trans hr))
    · rw [ite_eq_right he]
      symm
      apply Finset.sum_eq_zero
      intro Q _
      rw [Finsupp.single_apply, ite_eq_right]
      intro hh
      exact he ((congrArg (oddKernelPointMap E H hodd) hh).trans
        (oddKernelPointMap_translation E H hodd P Q))

/-- [DkMath.Lib] 押し出しは因子の整数次数を保存する。点群の加法性は不要。 -/
theorem kernelDivisorPush_degree (H : AddSubgroup (Points E)) [Fintype H]
    (hodd : Odd (Nat.card H)) (D : Points E →₀ ℤ) :
    (kernelDivisorPush E H hodd D).sum (fun _ n => n) = D.sum (fun _ n => n) :=
  Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)

/-- [DkMath.Lib] 点差の因子[P]−[O]を、同じ像点の因子[φ(P)]−[O]へ送る。
これは因子としての等式であり、点群の加法性は使用しない。 -/
theorem kernelDivisorPush_pointDivisor (H : AddSubgroup (Points E)) [Fintype H]
    (hodd : Odd (Nat.card H)) (P : Points E) :
    kernelDivisorPush E H hodd (Finsupp.single P 1 - Finsupp.single 0 1) =
      Finsupp.single (oddKernelPointMap E H hodd P) 1 - Finsupp.single 0 1 := by
  rw [map_sub]
  change Finsupp.mapDomain (oddKernelPointMap E H hodd) (Finsupp.single P 1) -
    Finsupp.mapDomain (oddKernelPointMap E H hodd) (Finsupp.single 0 1) = _
  rw [Finsupp.mapDomain_single, Finsupp.mapDomain_single,
    (oddKernelPointMap_eq_zero_iff E H hodd 0).mpr H.zero_mem]

/-- [DkMath.Lib] 同じ全点関数の因子押し出しは主因子を主因子へ送る。
標的の生成関数は、既存の同じ軌道積を降ろしたkernelModelNormである。 -/
theorem kernelDivisorPush_isPrincipal (H : AddSubgroup (Points E)) [Fintype H]
    (hodd : Odd (Nat.card H)) (D : Points E →₀ ℤ)
    (hD : ValuationDivisor.IsPrincipal (pointValuation E) D) :
    ValuationDivisor.IsPrincipal (kernelTargetValuation E H hodd) (kernelDivisorPush E H hodd D) := by
  obtain ⟨f, hf, hD⟩ := hD
  refine ⟨kernelModelNorm E H f, kernelModelNorm_ne_zero E H f hf, ?_⟩
  intro T
  obtain ⟨P, rfl⟩ := oddKernelPointMap_surjective E H hodd T
  rw [kernelDivisorPush_apply_image]
  calc
    (∑ Q : H, D (P + Q.val)) = ∑ Q : H, pointOrder E (P + Q.val) f hf := by
      apply Finset.sum_congr rfl
      intro Q _
      exact (hD (P + Q.val)).trans (pointOrder_eq_neg_log E (P + Q.val) f hf).symm
    _ = _ := (kernelModelNorm_order_all E H hodd P f hf).symm

/-- [DkMath.Lib] 主因子で割った因子群の間の、同じ押し出しが誘導する加法準同型。
点群とのAbel対応はまだ使用せず、因子類の準同型として公開する。 -/
noncomputable def kernelDivisorClassPush (H : AddSubgroup (Points E)) [Fintype H]
    (hodd : Odd (Nat.card H)) :
    ((Points E →₀ ℤ) ⧸ ValuationDivisor.principalSubgroup (pointValuation E)) →+
      (((kernelModel E H).toAffine.Point →₀ ℤ) ⧸
        ValuationDivisor.principalSubgroup (kernelTargetValuation E H hodd)) :=
  QuotientAddGroup.map (ValuationDivisor.principalSubgroup (pointValuation E))
    (ValuationDivisor.principalSubgroup (kernelTargetValuation E H hodd)) (kernelDivisorPush E H hodd)
    (fun D hD => kernelDivisorPush_isPrincipal E H hodd D hD)

/-- [DkMath.Lib] 因子類の準同型は、同じ代表因子の実際の押し出しによって計算する。 -/
theorem kernelDivisorClassPush_mk (H : AddSubgroup (Points E)) [Fintype H]
    (hodd : Odd (Nat.card H)) (D : Points E →₀ ℤ) :
    kernelDivisorClassPush E H hodd (QuotientAddGroup.mk D) =
      QuotientAddGroup.mk (kernelDivisorPush E H hodd D) := rfl

/-- [DkMath.Lib] 因子類の押し出しも、点差の類を同じ像点の点差の類へ送る。
残るAbel対応は、この点差の類と実際の点群を結ぶ部分である。 -/
theorem kernelDivisorClassPush_pointClass (H : AddSubgroup (Points E)) [Fintype H]
    (hodd : Odd (Nat.card H)) (P : Points E) :
    kernelDivisorClassPush E H hodd
        (QuotientAddGroup.mk (Finsupp.single P 1 - Finsupp.single 0 1)) =
      QuotientAddGroup.mk (Finsupp.single (oddKernelPointMap E H hodd P) 1 - Finsupp.single 0 1) := by
  rw [kernelDivisorClassPush_mk, kernelDivisorPush_pointDivisor]

end DkMath.Lib.NumberTheory.EllipticFiniteKernel
