/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.EllipticFiniteKernelLocalTransport
import DkMath.Lib.NumberTheory.DedekindLocalParameter

#print "file: DkMath.Lib.NumberTheory.EllipticFiniteKernelUnramified"

/-!
# 有限像点の局所倍率を1と証明する

[DkMath.Lib] Hの平行移動軌道は|H|個の相異なる点。P∉Hなら全て有限点である。
中国剰余定理で、Pに一次の零点、他の軌道点に位数0を持つ源の関数fを作る。
その軌道積のPでの位数は1で、既存のkernelModelNormにより標的関数の引き戻し。
局所倍率eはこの1を割る正整数なので1である。従って標的の有限像点での
位数公式から倍率を除ける。核上の無限遠像と主因子の大域輸送は別に扱う。
-/
namespace DkMath.Lib.NumberTheory.EllipticFiniteKernel
open WeierstrassCurve WeierstrassCurve.Affine WithZero
open EllipticFunctionField EllipticTorsionRepresentation
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped BigOperators
attribute [local instance] geometricCoordinateRing_isDedekindDomain
variable {K : Type*} [Field K] [CharZero K] (E : WeierstrassCurve K) [E.IsElliptic]
noncomputable local instance instDecidableEqEllipticFiniteKernelUnramified {α : Type*} :
    DecidableEq α := Classical.decEq _

omit [CharZero K] in
/-- [DkMath.Lib] 核外のPの同じH軌道で、Pのみを一次で消す源の関数を構成する。
点の相異性・有限性・局所パラメータを内部供給する。 -/
theorem exists_orbit_parameter (H : AddSubgroup (Points E)) [Finite H]
    (P : Points E) (hP : P ∉ H) :
    ∃ f : (E.toAffine⁄(AlgebraicClosure K)).FunctionField, f ≠ 0 ∧
      ∀ Q : H, pointValuation E (P + Q.val) f = if Q = 0 then exp (-1 : ℤ) else 1 := by
  classical
  have hn (Q : H) : P + Q.val ≠ 0 := fun hz =>
    add_not_mem_kernel E H P hP Q (hz ▸ H.zero_mem)
  let w (Q : H) := placeOf E (AlgebraicClosure K) (P + Q.val) (hn Q)
  have hinj : Function.Injective w := by
    intro Q R he
    have hpt : P + Q.val = P + R.val := placeOf_injective E (AlgebraicClosure K) (hn Q) (hn R) he
    exact Subtype.ext (add_left_cancel hpt)
  obtain ⟨a, ha₀, ha⟩ := DedekindLocalParameter.exists_parameter w hinj (0 : H)
  let f := algebraMap (E.toAffine⁄(AlgebraicClosure K)).CoordinateRing
    (E.toAffine⁄(AlgebraicClosure K)).FunctionField a
  have hf : f ≠ 0 := by
    intro hz
    apply ha₀
    apply IsFractionRing.injective (E.toAffine⁄(AlgebraicClosure K)).CoordinateRing
      (E.toAffine⁄(AlgebraicClosure K)).FunctionField
    simpa only [map_zero] using hz
  refine ⟨f, hf, fun Q => ?_⟩
  have heval : pointValuation E (P + Q.val) f = (w Q).valuation _ f := by
    unfold pointValuation
    split_ifs with hz
    · exact (hn Q hz).elim
    · rfl
  exact heval.trans ((valuation_of_algebraMap (w Q) a).trans (ha Q))

/-- [DkMath.Lib] 同じ標的関数体の元の引き戻しで、Pの一様化元を実現する。
存在だけでなく、同じ源の軌道積を使ってこの元を構成する。 -/
theorem exists_kernel_pull_uniformizer (H : AddSubgroup (Points E)) [Fintype H]
    (P : Points E) (hP : P ∉ H) :
    ∃ g : (kernelModel E H).toAffine.FunctionField, g ≠ 0 ∧
      pointValuation E P (kernelModelPull E H g) = exp (-1 : ℤ) := by
  classical
  obtain ⟨f, hf, hv⟩ := exists_orbit_parameter E H P hP
  refine ⟨kernelModelNorm E H f, kernelModelNorm_ne_zero E H f hf, ?_⟩
  rw [kernelModelPull_norm, pointValuation_kernelNorm]
  rw [Fintype.prod_eq_single (0 : H) (fun Q hQ => by rw [hv, ite_eq_right hQ])]
  exact (hv 0).trans (ite_eq_left rfl)

/-- [DkMath.Lib] 同じ有限像点では局所位数が正確に一致する。
局所倍率は引き戻し一様化元の位数1を割るため1である。 -/
theorem kernelModelPull_order_eq (H : AddSubgroup (Points E)) [Fintype H]
    (hodd : Odd (Nat.card H)) (P : Points E) (hP : P ∉ H)
    (g : (kernelModel E H).toAffine.FunctionField) (hg : g ≠ 0) :
    -log (pointValuation E P (kernelModelPull E H g)) =
      -log (kernelImageValuation E H hodd P hP g) := by
  obtain ⟨e, he, hs⟩ := exists_pos_kernel_order_scaling E H hodd P hP
  obtain ⟨u, hu, hvu⟩ := exists_kernel_pull_uniformizer E H P hP
  have hunit := hs u hu
  rw [hvu, log_exp] at hunit
  have he₁ : e = 1 := Int.eq_one_of_mul_eq_one_right he.le
    (show e * (-log (kernelImageValuation E H hodd P hP u)) = 1 by omega)
  simpa only [he₁, one_mul] using hs g hg

/-- [DkMath.Lib] 付値そのものも同じ有限像点で一致する。零関数も含む。 -/
theorem kernelModelPull_valuation_eq (H : AddSubgroup (Points E)) [Fintype H]
    (hodd : Odd (Nat.card H)) (P : Points E) (hP : P ∉ H)
    (g : (kernelModel E H).toAffine.FunctionField) :
    pointValuation E P (kernelModelPull E H g) = kernelImageValuation E H hodd P hP g := by
  by_cases hg : g = 0
  · subst g; simp only [map_zero]
  · have hs := neg_injective (kernelModelPull_order_eq E H hodd P hP g hg)
    exact (exp_log ((pointValuation E P).ne_zero_iff.mpr
      ((map_ne_zero (kernelModelPull E H).toRingHom).mpr hg))).symm.trans
        ((congrArg WithZero.exp hs).trans (exp_log ((kernelImageValuation E H hodd P hP).ne_zero_iff.mpr hg)))

/-- [DkMath.Lib] 同じ有限像点における、倍率のない軌道積の標的位数公式。
剰余類上の全ての源の位数の和に一致し、不分岐性の外部providerを要求しない。 -/
theorem kernelModelNorm_order_eq (H : AddSubgroup (Points E)) [Fintype H]
    (hodd : Odd (Nat.card H)) (P : Points E) (hP : P ∉ H)
    (f : (E.toAffine⁄(AlgebraicClosure K)).FunctionField) (hf : f ≠ 0) :
    -log (kernelImageValuation E H hodd P hP (kernelModelNorm E H f)) =
      ∑ Q : H, pointOrder E (P + Q.val) f hf := by
  have hs := kernelModelPull_order_eq E H hodd P hP (kernelModelNorm E H f)
    (kernelModelNorm_ne_zero E H f hf)
  rw [kernelModelPull_norm] at hs
  exact hs.symm.trans ((pointOrder_eq_neg_log E P _ (kernelNorm_ne_zero E H f hf)).symm.trans
    (pointOrder_kernelNorm E H P f hf))

end DkMath.Lib.NumberTheory.EllipticFiniteKernel
