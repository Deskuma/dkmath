/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.EllipticFiniteKernelUnramified
import DkMath.Lib.NumberTheory.WeierstrassPolePullback

#print "file: DkMath.Lib.NumberTheory.EllipticFiniteKernelValuation"

/-!
# 全点関数と引き戻しの全局所付値を一致させる

[DkMath.Lib] 核外では中国剰余定理による一様化元、核上では極位数2,3を使う。
これにより既存の同じ全点関数φと同じ関数体引き戻しιについて、全てのP,gで
v_P(ιg)=v_{φ(P)}(g)を証明する。OとH上の点も含み、局所倍率は内部で1と証明済み。
同じ軌道積の標的位数公式も全点へ延びる。

これは場所の整合と正規化の一致である。主因子の押し出し・点群の加法性を
仮定に隠さず、それらの大域的な接続は次の仕事として保持する。
-/
namespace DkMath.Lib.NumberTheory.EllipticFiniteKernel
open WeierstrassCurve WeierstrassCurve.Affine WithZero
open EllipticFunctionField EllipticTorsionRepresentation WeierstrassCoordinateEvaluation
open WeierstrassFinitePlace WeierstrassPolePullback
open scoped BigOperators
variable {K : Type*} [Field K] [CharZero K] (E : WeierstrassCurve K) [E.IsElliptic]
noncomputable local instance instDecidableEqEllipticFiniteKernelValuation :
    DecidableEq (AlgebraicClosure K) := Classical.decEq _

/-- [DkMath.Lib] H上の全ての点で、同じ引き戻しは標的の無限遠付値を正確に保存する。
三次モデルの二元基底の偶奇と、既存のX_H,Y_Hの極位数2,3から従う。 -/
theorem kernelModelPull_valuation_of_mem (H : AddSubgroup (Points E)) [Fintype H]
    (P : Points E) (hP : P ∈ H) (g : (kernelModel E H).toAffine.FunctionField) :
    pointValuation E P (kernelModelPull E H g) =
      EllipticInfinityValuation.valuationInfty (kernelModel E H).toAffine g :=
  functionPull_valuation_infty _ _ _ _ (pointValuation E P)
    (veluX_transcendental E H) (veluY_not_mem_simpleX E H)
    (fun _ hc => pointValuation_const_eq_one E P hc)
    (veluX_valuation_of_mem E H P hP) (veluY_valuation_of_mem E H P hP) g

/-- [DkMath.Lib] 同じ奇数核の標的の全点付値。標的楕円性は内部供給する。 -/
noncomputable def kernelTargetValuation (H : AddSubgroup (Points E)) [Fintype H]
    (hodd : Odd (Nat.card H)) (T : (kernelModel E H).toAffine.Point) :
    Valuation (kernelModel E H).toAffine.FunctionField ℤᵐ⁰ := by
  let := kernelModel_isElliptic_of_odd_card E H hodd
  exact modelPointValuation (kernelModel E H) T

/-- [DkMath.Lib] 標的のOでは、同じ無限遠付値へ戻る。 -/
theorem kernelTargetValuation_zero (H : AddSubgroup (Points E)) [Fintype H]
    (hodd : Odd (Nat.card H)) : kernelTargetValuation E H hodd 0 =
      EllipticInfinityValuation.valuationInfty (kernelModel E H).toAffine := by
  let := kernelModel_isElliptic_of_odd_card E H hodd
  exact modelPointValuation_zero _

/-- [DkMath.Lib] 核外の点の像では、前段で構成した同じ有限素点の付値へ戻る。 -/
theorem kernelTargetValuation_image_of_not_mem (H : AddSubgroup (Points E)) [Fintype H]
    (hodd : Odd (Nat.card H)) (P : Points E) (hP : P ∉ H) :
    kernelTargetValuation E H hodd (oddKernelPointMap E H hodd P) =
      kernelImageValuation E H hodd P hP := by
  let := kernelModel_isElliptic_of_odd_card E H hodd
  let : IsDedekindDomain (kernelModel E H).toAffine.CoordinateRing :=
    EllipticCoordinateRing.isDedekindDomain
  exact modelPointValuation_of_ne_zero _ _
    (fun h => hP ((oddKernelPointMap_eq_zero_iff E H hodd P).mp h))

/-- [DkMath.Lib] 同じ全点関数と関数体引き戻しは、全点で正規化付値を正確に保存する。
H上の無限遠像も核外の有限像も含む。外部の局所比較providerは不要。 -/
theorem kernelModelPull_valuation_all (H : AddSubgroup (Points E)) [Fintype H]
    (hodd : Odd (Nat.card H)) (P : Points E) (g : (kernelModel E H).toAffine.FunctionField) :
    pointValuation E P (kernelModelPull E H g) =
      kernelTargetValuation E H hodd (oddKernelPointMap E H hodd P) g := by
  by_cases hP : P ∈ H
  · let := kernelModel_isElliptic_of_odd_card E H hodd
    have he : oddKernelPointMap E H hodd P = 0 := kernelPointMap_of_mem E H P hP
    rw [he, kernelTargetValuation_zero]
    exact kernelModelPull_valuation_of_mem E H P hP g
  · rw [kernelTargetValuation_image_of_not_mem E H hodd P hP]
    exact kernelModelPull_valuation_eq E H hodd P hP g

/-- [DkMath.Lib] 同じ全点関数の像点での軌道積位数は、同じH軌道の源の位数の和。
P∈Hも許し、標的のOの位数も同じ式で扱う。 -/
theorem kernelModelNorm_order_all (H : AddSubgroup (Points E)) [Fintype H]
    (hodd : Odd (Nat.card H)) (P : Points E)
    (f : (E.toAffine⁄(AlgebraicClosure K)).FunctionField) (hf : f ≠ 0) :
    -log (kernelTargetValuation E H hodd (oddKernelPointMap E H hodd P) (kernelModelNorm E H f)) =
      ∑ Q : H, pointOrder E (P + Q.val) f hf := by
  have he := kernelModelPull_valuation_all E H hodd P (kernelModelNorm E H f)
  rw [kernelModelPull_norm] at he
  exact (congrArg (fun z => -log z) he).symm.trans
    ((pointOrder_eq_neg_log E P _ (kernelNorm_ne_zero E H f hf)).symm.trans (pointOrder_kernelNorm E H P f hf))

end DkMath.Lib.NumberTheory.EllipticFiniteKernel
