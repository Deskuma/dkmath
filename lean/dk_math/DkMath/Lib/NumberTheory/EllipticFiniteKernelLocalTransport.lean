/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.EllipticFiniteKernelNorm
import DkMath.Lib.NumberTheory.EllipticFiniteKernelNonsingular
import DkMath.Lib.NumberTheory.WeierstrassFinitePlace

#print "file: DkMath.Lib.NumberTheory.EllipticFiniteKernelLocalTransport"

/-!
# 同じ全点関数の有限像点と、関数体の引き戻しの局所中心

[DkMath.Lib] P∉Hなら既存の全点関数の像は有限点。この点の素イデアルと評価を、
同じkernelModelの座標環上に構成する。座標の有限評価から、引き戻しはこの場所を
源のPの場所へ送ることを証明する。局所位数には同じ正整数倍率e_Pが存在する。
前回の軌道積をこの比較に入力し、倍率を保持した標的でのノルム位数公式を得る。

e_P=1、H上の無限遠像、任意の二点の加法性は本ファイルの結論に含めない。
-/
namespace DkMath.Lib.NumberTheory.EllipticFiniteKernel
open WeierstrassCurve WeierstrassCurve.Affine WithZero
open EllipticFunctionField EllipticTorsionRepresentation EllipticPointEvaluation
open WeierstrassCoordinateEvaluation WeierstrassFinitePlace
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped BigOperators
variable {K : Type*} [Field K] [CharZero K] (E : WeierstrassCurve K) [E.IsElliptic]
noncomputable local instance instDecidableEqEllipticFiniteKernelLocalTransport :
    DecidableEq (AlgebraicClosure K) := Classical.decEq _

/-- [DkMath.Lib] 同じkernelModelPullは、座標環上で既存の同じ座標代入に一致する。 -/
theorem kernelModelPull_algebraMap (H : AddSubgroup (Points E)) [Fintype H]
    (b : (kernelModel E H).toAffine.CoordinateRing) :
    kernelModelPull E H (algebraMap (kernelModel E H).toAffine.CoordinateRing
      (kernelModel E H).toAffine.FunctionField b) = kernelModelCoordinateHom E H b :=
  functionPull_algebraMap _ _ _ _ _ _ b

/-- [DkMath.Lib] 既存の全点関数の有限像点に対応する、同じ標的座標環の素点。 -/
noncomputable def kernelImagePlace (H : AddSubgroup (Points E)) [Fintype H]
    (hodd : Odd (Nat.card H)) (P : Points E) (hP : P ∉ H) :
    HeightOneSpectrum (kernelModel E H).toAffine.CoordinateRing :=
  finitePlace (kernelModel E H) (oddKernelPointMap E H hodd P)
    (fun h => hP ((oddKernelPointMap_eq_zero_iff E H hodd P).mp h))

/-- [DkMath.Lib] 同じ有限像点の正規化された離散付値。
標的のDedekind性と楕円性は奇数核の既存の定理から内部供給する。 -/
noncomputable def kernelImageValuation (H : AddSubgroup (Points E)) [Fintype H]
    (hodd : Odd (Nat.card H)) (P : Points E) (hP : P ∉ H) :
    Valuation (kernelModel E H).toAffine.FunctionField ℤᵐ⁰ := by
  let := kernelModel_isElliptic_of_odd_card E H hodd
  let : IsDedekindDomain (kernelModel E H).toAffine.CoordinateRing :=
    EllipticCoordinateRing.isDedekindDomain
  exact (kernelImagePlace E H hodd P hP).valuation _

/-- [DkMath.Lib] 源の有限評価は、標的の同じ有限像点での全座標環評価と可換。
一般点だけの主張ではなく、任意の座標環元bに対する剰余合同である。 -/
theorem kernelModelCoordinateHom_congr (H : AddSubgroup (Points E)) [Fintype H]
    (hodd : Odd (Nat.card H)) (P : Points E) (hP : P ∉ H)
    (b : (kernelModel E H).toAffine.CoordinateRing) :
    (pointValuation E P).Cong (kernelModelCoordinateHom E H b)
      (algebraMap (AlgebraicClosure K) _
        (finiteEval (kernelModel E H) (oddKernelPointMap E H hodd P)
          (fun h => hP ((oddKernelPointMap_eq_zero_iff E H hodd P).mp h)) b)) := by
  let := kernelModel_isElliptic_of_odd_card E H hodd
  have he : oddKernelPointMap E H hodd P =
      Point.some _ _ (kernelAt_nonsingular E H P hP) := kernelPointMap_of_not_mem E H P hP
  have hx : (pointValuation E P).Cong (veluX E H)
      (algebraMap _ _ (oddKernelPointMap E H hodd P).xc) := by
    rw [he]
    exact value_spec E P (veluX E H) (veluX_regular_outside E H P hP)
  have hy : (pointValuation E P).Cong (veluY E H)
      (algebraMap _ _ (oddKernelPointMap E H hodd P).yc) := by
    rw [he]
    exact value_spec E P (veluY E H) (veluY_regular_outside E H P hP)
  exact coordinateEval_congr (kernelModel E H) (pointValuation E P) _ _
    (kernelModel_equation E H) _ _ (pointValuation_const_le_one E P) hx hy b

/-- [DkMath.Lib] 同じ引き戻しの局所中心は、同じ全点関数の有限像点である。
像点のイデアルの元は消え、その外の座標環元は単元になる。 -/
theorem kernelModelPull_center (H : AddSubgroup (Points E)) [Fintype H]
    (hodd : Odd (Nat.card H)) (P : Points E) (hP : P ∉ H) :
    (∀ b ∈ (kernelImagePlace E H hodd P hP).asIdeal,
      pointValuation E P (kernelModelPull E H (algebraMap _ _ b)) ≤ exp (-1 : ℤ)) ∧
    (∀ b ∉ (kernelImagePlace E H hodd P hP).asIdeal,
      pointValuation E P (kernelModelPull E H (algebraMap _ _ b)) = 1) := by
  have hc := kernelModelCoordinateHom_congr E H hodd P hP
  constructor
  · intro b hb
    rw [kernelModelPull_algebraMap]
    have h := hc b
    rw [finiteEval_of_mem _ _ _ b hb, map_zero, Valuation.cong_zero_iff] at h
    exact WithZero.lt_one_iff_le_exp_neg_one.mp h
  · intro b hb
    rw [kernelModelPull_algebraMap]
    exact (hc b).eq_of_eq_one (pointValuation_const_eq_one E P
      (fun hz => hb ((mem_finitePlace_iff _ _ _ b).mpr hz)))

/-- [DkMath.Lib] 同じ有限像点での局所位数を、源の位数へ正整数倍率で輸送する。
倍率は全ての標的関数に共通し、関数ごとに選び直すものではない。 -/
theorem exists_pos_kernel_order_scaling (H : AddSubgroup (Points E)) [Fintype H]
    (hodd : Odd (Nat.card H)) (P : Points E) (hP : P ∉ H) :
    ∃ e : ℤ, 0 < e ∧ ∀ g : (kernelModel E H).toAffine.FunctionField, g ≠ 0 →
      -log (pointValuation E P (kernelModelPull E H g)) =
        e * (-log (kernelImageValuation E H hodd P hP g)) := by
  let := kernelModel_isElliptic_of_odd_card E H hodd
  let : IsDedekindDomain (kernelModel E H).toAffine.CoordinateRing :=
    EllipticCoordinateRing.isDedekindDomain
  obtain ⟨h₁, h₂⟩ := kernelModelPull_center E H hodd P hP
  exact DiscreteValuationPullback.exists_pos_order_scaling
    (kernelImagePlace E H hodd P hP) (pointValuation E P) (kernelModelPull E H).toRingHom h₁ h₂

/-- [DkMath.Lib] 倍率を保持した、同じ標的関数の軌道積位数公式。
右辺は同じH剰余類の源の位数の総和、左辺は同じ有限像点での位数のe倍である。
e=1や任意ファイバーと剰余類の一致は、この定理から結論しない。 -/
theorem exists_pos_kernel_norm_order_formula (H : AddSubgroup (Points E)) [Fintype H]
    (hodd : Odd (Nat.card H)) (P : Points E) (hP : P ∉ H) :
    ∃ e : ℤ, 0 < e ∧ ∀ f : (E.toAffine⁄(AlgebraicClosure K)).FunctionField, ∀ hf : f ≠ 0,
      e * (-log (kernelImageValuation E H hodd P hP (kernelModelNorm E H f))) =
        ∑ Q : H, pointOrder E (P + Q.val) f hf := by
  obtain ⟨e, he, hscale⟩ := exists_pos_kernel_order_scaling E H hodd P hP
  refine ⟨e, he, fun f hf => ?_⟩
  have hs := hscale (kernelModelNorm E H f) (kernelModelNorm_ne_zero E H f hf)
  rw [kernelModelPull_norm] at hs
  exact hs.symm.trans ((pointOrder_eq_neg_log E P _ (kernelNorm_ne_zero E H f hf)).symm.trans
    (pointOrder_kernelNorm E H P f hf))

end DkMath.Lib.NumberTheory.EllipticFiniteKernel
