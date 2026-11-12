/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.EllipticFiniteKernelFormal
import DkMath.Lib.NumberTheory.EllipticNodalReduction

#print "file: DkMath.Lib.NumberTheory.EllipticFiniteKernelZeroComponent"

/-!
# 特異核側の全零成分を、同じ商写像で輸送する

[DkMath.Lib] 非零核点が全て特異に還元するとき、滑らかなPと特異なQの和も特異である。
これは零成分部分群の閉性から従う。同じ臨界中心への合同を座標和で打ち消すと、
X_H(P),Y_H(P)は元のPの座標に合同となる。整点では剰余の非特異性を保ち、
非整点では前章の無限遠近傍保存を使う。核内の点もOへの像として含める。
滑らかな核の側や逆像の判定を、この側の結論へ混ぜない。
-/
namespace DkMath.Lib.NumberTheory.EllipticFiniteKernel
open WeierstrassCurve WeierstrassCurve.Affine IsLocalRing
open EllipticTorsionRepresentation EllipticGoodReductionSeparation EllipticSmoothReduction
open EllipticCriticalCentre EllipticNodalReduction WeierstrassResidueModel ValuationResidue
open scoped BigOperators
noncomputable local instance instDecidableEqEllipticFiniteKernelZeroComponent {α : Type*} : DecidableEq α :=
  Classical.decEq _

/-- [DkMath.Lib] 同じ一般ファイバー上の零成分は引き算で閉じる。モデルの等式を保持する。 -/
theorem smooth_sub_of_model {L : Type*} [Field L] (A : ValuationSubring L)
    (M : WeierstrassCurve A) (V : WeierstrassCurve L) (hM : M.map A.subtype = V)
    {P Q : V.toAffine.Point} (hP : HasSmoothReduction M P) (hQ : HasSmoothReduction M Q) :
    HasSmoothReduction M (P - Q) := by
  subst V
  exact (zeroComponentSubgroup M).sub_mem hP hQ

private theorem modelEquiv_symm {L : Type*} [Field L] {W V : WeierstrassCurve L} (h : W = V) :
    WeierstrassVariableChange.pointEquivOfModelEq h.symm =
      (WeierstrassVariableChange.pointEquivOfModelEq h).symm := by
  subst V
  rfl

private theorem sum_normalized_small {L G : Type*} [Field L] [AddCommGroup G] [Fintype G]
    (A : ValuationSubring L) (f g : G → L) (hg : g 0 = 0)
    (h : ∀ i : G, i ≠ 0 → A.valuation (f i - g i) < 1) :
    A.valuation (((∑ i, f i) - ∑ i, g i) - f 0) < 1 := by
  have he := Finset.sum_erase_add (Finset.univ : Finset G) (fun i => f i - g i) (Finset.mem_univ 0)
  rw [← Finset.sum_sub_distrib, ← he, hg, sub_zero, add_sub_cancel_right]
  exact A.valuation.map_sum_lt one_ne_zero (fun i hi => h i (Finset.mem_erase.mp hi).1)

variable {K : Type*} [Field K] [CharZero K] (E : WeierstrassCurve K) [E.IsElliptic]
  (H : AddSubgroup (Points E)) [Fintype H]
  (A : ValuationSubring (AlgebraicClosure K)) (M : WeierstrassCurve A)
  (hM : M.map A.subtype = E.map (algebraMap K (AlgebraicClosure K)))
  (C : CriticalCentre A (E.map (algebraMap K (AlgebraicClosure K))))

include hM in
omit [CharZero K] [E.IsElliptic] [Fintype H] in
/-- [DkMath.Lib] 滑らかでない実点の両座標は、同じ中心に合同。便宜座標のOを特異点に数えない。 -/
theorem nonsmooth_coordinates_congr (P : Points E) (hP : ¬ HasSmoothReduction M P) :
    A.valuation (P.xc - C.x) < 1 ∧ A.valuation (P.yc - C.y) < 1 := by
  cases P with
  | zero => exact (hP (hasSmoothReduction_zero M _)).elim
  | some x y h =>
    have hx := (not_hasSmoothReduction_some_iff_of_model M _ hM C h).mp hP
    exact ⟨hx, y_small_of_x_small_of_model M _ hM C h hx⟩

include C hM in
omit [CharZero K] in
/-- [DkMath.Lib] 特異核側の同じ座標和は、零成分の元の両座標と合同。
これは標的の滑らかさを入力する条件付き定理ではなく、源の部分群閉性からの結論である。 -/
theorem kernelAt_congr_of_not_smooth_kernel
    (hbad : ∀ Q : H, Q.val ≠ 0 → ¬ HasSmoothReduction M Q.val)
    (P : Points E) (hP : P ∉ H) (hsm : HasSmoothReduction M P) :
    A.valuation (kernelXAt E H P hP - P.xc) < 1 ∧
      A.valuation (kernelYAt E H P hP - P.yc) < 1 := by
  have hshift (Q : H) (hQ : Q ≠ 0) : ¬ HasSmoothReduction M (P + Q.val) := by
    intro hh
    have hh' := smooth_sub_of_model A M _ hM hh hsm
    have hQ0 : Q.val ≠ 0 := fun hz => hQ (Subtype.ext hz)
    apply hbad Q hQ0
    have he : P + Q.val - P = Q.val := by abel
    exact he ▸ hh'
  have hc (Q : H) (hQ : Q ≠ 0) :=
    nonsmooth_coordinates_congr E A M hM C (P + Q.val) (hshift Q hQ)
  have hd (Q : H) (hQ : Q ≠ 0) :=
    nonsmooth_coordinates_congr E A M hM C Q.val (hbad Q (fun hz => hQ (Subtype.ext hz)))
  have hx (Q : H) (hQ : Q ≠ 0) : A.valuation ((P + Q.val).xc - Q.val.xc) < 1 :=
    (show A.valuation.Cong (P + Q.val).xc C.x from (hc Q hQ).1).trans
      (show A.valuation.Cong Q.val.xc C.x from (hd Q hQ).1).symm
  have hy (Q : H) (hQ : Q ≠ 0) : A.valuation ((P + Q.val).yc - Q.val.yc) < 1 :=
    (show A.valuation.Cong (P + Q.val).yc C.y from (hc Q hQ).2).trans
      (show A.valuation.Cong Q.val.yc C.y from (hd Q hQ).2).symm
  rw [kernelXAt_eq_sum, kernelYAt_eq_sum]
  constructor
  · simpa only [AddSubgroup.coe_zero, add_zero] using
      sum_normalized_small A (fun Q : H => (P + Q.val).xc) (fun Q => Q.val.xc) rfl hx
  · simpa only [AddSubgroup.coe_zero, add_zero] using
      sum_normalized_small A (fun Q : H => (P + Q.val).yc) (fun Q => Q.val.yc) rfl hy

variable (n : ℕ) (hkill : ∀ Q : H, n • Q.val = 0) (hn : A.valuation (n : AlgebraicClosure K) = 1)

include C hM in
/-- [DkMath.Lib] 特異核側では、同じ零成分の全点の像が同じ付値環標的で滑らか。
整な点だけへ零成分を縮めず、O・非整点・核内点を全て処理する。 -/
theorem oddKernelPointMap_smooth_of_not_smooth_kernel (ho : Odd (Nat.card H))
    (hbad : ∀ Q : H, Q.val ≠ 0 → ¬ HasSmoothReduction M Q.val)
    (P : Points E) (hsm : HasSmoothReduction M P) :
    HasSmoothReduction (valuationKernelModel E H n hkill A M hM hn) (oddKernelPointMap E H ho P) := by
  let := kernelModel_isElliptic_of_odd_card E H ho
  by_cases hP : P ∈ H
  · rw [show oddKernelPointMap E H ho P = 0 from kernelPointMap_of_mem E H P hP]
    exact hasSmoothReduction_zero _ _
  by_cases hx : P.xc ∈ A
  · have hP0 : P ≠ 0 := fun hz => hP (hz ▸ H.zero_mem)
    have hns := Point.nonsingular_xc_yc hP0
    have hy := EllipticTorsionValuationIntegrality.y_mem_of_x_mem A M _ hM hns.1 hx
    have hc := kernelAt_congr_of_not_smooth_kernel E H A M hM C hbad P hP hsm
    have hxi : kernelXAt E H P hP ∈ A := by
      have hi := A.add_mem _ _ ((A.valuation_le_one_iff _).mp hc.1.le) hx
      simpa only [sub_add_cancel] using hi
    have hyi : kernelYAt E H P hP ∈ A := by
      have hi := A.add_mem _ _ ((A.valuation_le_one_iff _).mp hc.2.le) hy
      simpa only [sub_add_cancel] using hi
    have hrx := (residue_eq_residue_iff_sub_mem_nonunits A hxi hx).mpr
      ((ValuationSubring.mem_nonunits_iff _).mpr hc.1)
    have hry := (residue_eq_residue_iff_sub_mem_nonunits A hyi hy).mpr
      ((ValuationSubring.mem_nonunits_iff _).mpr hc.2)
    have hpns := (hasSmoothReduction_some_iff M hns).mp
      (by rwa [← Point.eq_some_xc_yc hP0]) hx hy
    have hres := valuationKernelModel_residue_eq_of_not_smooth E H n hkill A M hM hn hbad
    rw [show oddKernelPointMap E H ho P = Point.some _ _ (kernelAt_nonsingular E H P hP) from
      kernelPointMap_of_not_mem E H P hP, hasSmoothReduction_some_iff]
    intro _ _
    rw [hres, hrx, hry]
    exact hpns
  · exact oddKernelPointMap_smooth_of_x_not_mem E H n hkill A M hM hn ho P hx

/-- [DkMath.Lib] 同じ実点商準同型を、源と同じ付値環標的の全零成分の間へ制限する。
保存性を仮定として受け取らず、特異核の条件から内部で供給する。 -/
noncomputable def singularKernelZeroComponentHom (ho : Odd (Nat.card H))
    (hbad : ∀ Q : H, Q.val ≠ 0 → ¬ HasSmoothReduction M Q.val) :
    zeroComponentSubgroup M →+
      zeroComponentSubgroup (valuationKernelModel E H n hkill A M hM hn) := by
  let U := valuationKernelModel E H n hkill A M hM hn
  let hU := valuationKernelModel_map E H n hkill A M hM hn ho
  let f := (WeierstrassVariableChange.pointEquivOfModelEq hU.symm).toAddMonoidHom.comp
    ((oddKernelPointHom E H ho).comp
      (WeierstrassVariableChange.pointEquivOfModelEq hM).toAddMonoidHom)
  refine { toFun := fun P => ⟨f P.val, ?_⟩
           map_zero' := Subtype.ext (map_zero f)
           map_add' := fun P Q => Subtype.ext (map_add f P.val Q.val) }
  change HasSmoothReduction U _
  apply (smooth_pointEquiv_of_model A U _ hU _).mpr
  apply oddKernelPointMap_smooth_of_not_smooth_kernel E H A M hM C n hkill hn ho hbad
  apply (smooth_pointEquiv_of_model A M _ hM _).mp
  change HasSmoothReduction M ((WeierstrassVariableChange.pointEquivOfModelEq hM.symm)
    ((WeierstrassVariableChange.pointEquivOfModelEq hM) P.val))
  rw [modelEquiv_symm hM, AddEquiv.symm_apply_apply]
  exact P.property

/-- [DkMath.Lib] 零成分への制限を一般ファイバーへ戻すと、既存の同じ商準同型そのものになる。 -/
theorem singularKernelZeroComponentHom_geometric (ho : Odd (Nat.card H))
    (hbad : ∀ Q : H, Q.val ≠ 0 → ¬ HasSmoothReduction M Q.val) (P : zeroComponentSubgroup M) :
    WeierstrassVariableChange.pointEquivOfModelEq
      (valuationKernelModel_map E H n hkill A M hM hn ho)
      (singularKernelZeroComponentHom E H A M hM C n hkill hn ho hbad P).val =
        oddKernelPointHom E H ho (WeierstrassVariableChange.pointEquivOfModelEq hM P.val) := by
  change WeierstrassVariableChange.pointEquivOfModelEq _
    (WeierstrassVariableChange.pointEquivOfModelEq _ _) = _
  rw [modelEquiv_symm (valuationKernelModel_map E H n hkill A M hM hn ho), AddEquiv.apply_symm_apply]
  rfl

/-- [DkMath.Lib] 特異核側では零成分への制限は単射。核内で滑らかな点はOだけだからである。
剰余点群上の単射性や、零成分全体への全射性は結論しない。 -/
theorem singularKernelZeroComponentHom_injective (ho : Odd (Nat.card H))
    (hbad : ∀ Q : H, Q.val ≠ 0 → ¬ HasSmoothReduction M Q.val) :
    Function.Injective (singularKernelZeroComponentHom E H A M hM C n hkill hn ho hbad) := by
  rw [injective_iff_map_eq_zero]
  intro P hP
  have hv := congrArg (fun T : zeroComponentSubgroup (valuationKernelModel E H n hkill A M hM hn) =>
    WeierstrassVariableChange.pointEquivOfModelEq (valuationKernelModel_map E H n hkill A M hM hn ho) T.val) hP
  rw [singularKernelZeroComponentHom_geometric, AddSubgroup.coe_zero, map_zero] at hv
  have hm : WeierstrassVariableChange.pointEquivOfModelEq hM P.val ∈ H :=
    (oddKernelPointMap_eq_zero_iff E H ho _).mp hv
  have hs : HasSmoothReduction M (WeierstrassVariableChange.pointEquivOfModelEq hM P.val) := by
    apply (smooth_pointEquiv_of_model A M _ hM _).mp
    rw [modelEquiv_symm hM, AddEquiv.symm_apply_apply]
    exact P.property
  have hz : WeierstrassVariableChange.pointEquivOfModelEq hM P.val = 0 := by
    by_contra hnz
    exact hbad ⟨_,hm⟩ hnz hs
  apply Subtype.ext
  exact (WeierstrassVariableChange.pointEquivOfModelEq hM).injective (hz.trans (map_zero _).symm)

end DkMath.Lib.NumberTheory.EllipticFiniteKernel
