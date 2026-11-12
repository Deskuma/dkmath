/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.EllipticFinitePointApproximation
import DkMath.Lib.NumberTheory.EllipticFiniteKernelValuation

#print "file: DkMath.Lib.NumberTheory.EllipticFiniteKernelFibers"

/-!
# 同じ全点関数のファイバーは、正確に同じHの剰余類

[DkMath.Lib] 二つの相異なる核外軌道をCRTで分離し、軌道積を同じ標的関数へ降ろす。
像が同じなら、その標的関数の付値も同じでなければならないが、一方は一次に消え、
他方は単元なので矛盾する。逆向きは既存のH平行移動不変性。
全点関数の加法性を使わずに、全てのファイバーを同定する。
-/
namespace DkMath.Lib.NumberTheory.EllipticFiniteKernel
open WeierstrassCurve WeierstrassCurve.Affine WithZero
open EllipticFunctionField EllipticTorsionRepresentation EllipticFinitePointApproximation
open scoped BigOperators
variable {K : Type*} [Field K] [CharZero K] (E : WeierstrassCurve K) [E.IsElliptic]
noncomputable local instance instDecidableEqEllipticFiniteKernelFibers {α : Type*} :
    DecidableEq α := Classical.decEq _

/-- [DkMath.Lib] 相異なる二つの核外H軌道を、同じ標的関数の引き戻しで分離する。
Pでは一次に消え、Rでは単元となる。標的全体の全射性や加法性は使用しない。 -/
theorem exists_pull_separating_orbits (H : AddSubgroup (Points E)) [Fintype H]
    (P R : Points E) (hP : P ∉ H) (hR : R ∉ H) (hRP : R - P ∉ H) :
    ∃ g : (kernelModel E H).toAffine.FunctionField,
      pointValuation E P (kernelModelPull E H g) = exp (-1 : ℤ) ∧
      pointValuation E R (kernelModelPull E H g) = 1 := by
  let A : Finset (Points E) := Finset.univ.image (fun Q : H => P + Q.val)
  let B : Finset (Points E) := Finset.univ.image (fun Q : H => R + Q.val)
  have ha (Q : H) : P + Q.val ∈ A := Finset.mem_image.mpr ⟨Q, Finset.mem_univ _, rfl⟩
  have hb (Q : H) : R + Q.val ∈ B := Finset.mem_image.mpr ⟨Q, Finset.mem_univ _, rfl⟩
  have hS : ∀ T ∈ A ∪ B, T ≠ 0 := by
    intro T hT
    rcases Finset.mem_union.mp hT with ht | ht
    · obtain ⟨Q, _, rfl⟩ := Finset.mem_image.mp ht
      exact fun hz => add_not_mem_kernel E H P hP Q (hz ▸ H.zero_mem)
    · obtain ⟨Q, _, rfl⟩ := Finset.mem_image.mp ht
      exact fun hz => add_not_mem_kernel E H R hR Q (hz ▸ H.zero_mem)
  have hPmem : P ∈ A ∪ B := Finset.mem_union_left _ (by simpa only [ZeroMemClass.coe_zero, add_zero] using ha 0)
  obtain ⟨f, _, hfp, hfun⟩ := exists_parameter_on_finset E (A ∪ B) hS P hPmem
  have hfa (Q : H) (hQ : Q ≠ 0) : pointValuation E (P + Q.val) f = 1 := by
    apply hfun _ (Finset.mem_union_left _ (ha Q))
    intro he
    have hqv : Q.val = 0 := by exact add_left_cancel (he.trans (add_zero P).symm)
    exact hQ (Subtype.ext hqv)
  have hfb (Q : H) : pointValuation E (R + Q.val) f = 1 := by
    apply hfun _ (Finset.mem_union_right _ (hb Q))
    intro he
    apply hRP
    have hd : R - P = -Q.val := by rw [← he]; abel
    exact hd ▸ H.neg_mem Q.property
  refine ⟨kernelModelNorm E H f, ?_, ?_⟩
  · rw [kernelModelPull_norm, pointValuation_kernelNorm,
      Fintype.prod_eq_single (0 : H) hfa]
    simpa only [ZeroMemClass.coe_zero, add_zero] using hfp
  · rw [kernelModelPull_norm, pointValuation_kernelNorm]
    simp only [hfb, Finset.prod_const_one]

/-- [DkMath.Lib] 同じ像を持つことと、差が同じHに属することは同値。
核上の零ファイバーも核外の全ての有限ファイバーも、この一つの式で扱う。 -/
theorem oddKernelPointMap_eq_iff_sub_mem (H : AddSubgroup (Points E)) [Fintype H]
    (hodd : Odd (Nat.card H)) (P R : Points E) :
    oddKernelPointMap E H hodd P = oddKernelPointMap E H hodd R ↔ R - P ∈ H := by
  constructor
  · intro he
    by_cases hP : P ∈ H
    · have hR : R ∈ H := (oddKernelPointMap_eq_zero_iff E H hodd R).mp
        (he.symm.trans ((oddKernelPointMap_eq_zero_iff E H hodd P).mpr hP))
      exact H.sub_mem hR hP
    · have hR : R ∉ H := fun hm => hP ((oddKernelPointMap_eq_zero_iff E H hodd P).mp
        (he.trans ((oddKernelPointMap_eq_zero_iff E H hodd R).mpr hm)))
      by_contra hRP
      obtain ⟨g, hgp, hgr⟩ := exists_pull_separating_orbits E H P R hP hR hRP
      have hv : pointValuation E P (kernelModelPull E H g) =
          pointValuation E R (kernelModelPull E H g) := by
        rw [kernelModelPull_valuation_all E H hodd P, kernelModelPull_valuation_all E H hodd R, he]
      rw [hgp, hgr, ← exp_zero, exp_inj] at hv
      omega
  · intro hm
    have ht := oddKernelPointMap_translation E H hodd P (⟨R - P, hm⟩ : H)
    have ha : P + (R - P) = R := by abel
    exact ((congrArg (oddKernelPointMap E H hodd) ha).symm.trans ht).symm

/-- [DkMath.Lib] 同じ全点関数のファイバーは、実点のH軌道そのもの。
存在するQも同じ部分群Hの点であり、別の抽象核へ置き換えない。 -/
theorem oddKernelPointMap_eq_iff_exists_translate (H : AddSubgroup (Points E)) [Fintype H]
    (hodd : Odd (Nat.card H)) (P R : Points E) :
    oddKernelPointMap E H hodd P = oddKernelPointMap E H hodd R ↔ ∃ Q : H, R = P + Q.val := by
  rw [oddKernelPointMap_eq_iff_sub_mem]
  constructor
  · intro hm
    refine ⟨⟨R - P, hm⟩, ?_⟩
    change R = P + (R - P)
    abel
  · rintro ⟨Q, rfl⟩
    have he : P + Q.val - P = Q.val := by abel
    exact he.symm ▸ Q.property

/-- [DkMath.Lib] 同じ像点のファイバーとHの間の実際の全単射。
QをP+Qへ送り、逆写像は差R−P。群準同型性はこの構成には使わない。 -/
noncomputable def kernelFiberEquiv (H : AddSubgroup (Points E)) [Fintype H]
    (hodd : Odd (Nat.card H)) (P : Points E) :
    H ≃ {R : Points E // oddKernelPointMap E H hodd R = oddKernelPointMap E H hodd P} where
  toFun Q := ⟨P + Q.val, oddKernelPointMap_translation E H hodd P Q⟩
  invFun R := ⟨R.val - P, (oddKernelPointMap_eq_iff_sub_mem E H hodd P R.val).mp R.property.symm⟩
  left_inv Q := Subtype.ext (by change P + Q.val - P = Q.val; abel)
  right_inv R := Subtype.ext (by change P + (R.val - P) = R.val; abel)

/-- [DkMath.Lib] 同じ像点のファイバーの位数は|H|。相異なるx座標の個数とは区別する。 -/
theorem card_kernel_image_fiber (H : AddSubgroup (Points E)) [Fintype H]
    (hodd : Odd (Nat.card H)) (P : Points E) :
    Nat.card {R : Points E // oddKernelPointMap E H hodd R = oddKernelPointMap E H hodd P} =
      Nat.card H := (Nat.card_congr (kernelFiberEquiv E H hodd P)).symm

end DkMath.Lib.NumberTheory.EllipticFiniteKernel
