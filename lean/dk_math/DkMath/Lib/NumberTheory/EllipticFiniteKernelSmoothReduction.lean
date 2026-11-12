/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.EllipticFiniteKernelReduction
import DkMath.Lib.NumberTheory.EllipticSmoothTorsionReduction
import DkMath.Lib.NumberTheory.WeierstrassVariableChangeGalois

#print "file: DkMath.Lib.NumberTheory.EllipticFiniteKernelSmoothReduction"

/-!
# 同じ滑らかな有限核の単射な還元と、同じ半核の剰余座標

[DkMath.Lib] 核が零成分に入る側では、既存の還元準同型を同じHへ制限する。
単元位数捩れ上の単射性から、核の点数と半核の点数を剰余へ保つ。
付値環モデルの剰余を、この同じ還元核の座標で構成する多項式モデルへ同定する。
剰余の商のΔ,c₄を節点上で計算する工程は別であり、ここに仮定として隠さない。
-/
namespace DkMath.Lib.NumberTheory.EllipticFiniteKernel
open WeierstrassCurve WeierstrassCurve.Affine IsLocalRing
open EllipticTorsionRepresentation EllipticGoodReductionSeparation EllipticSmoothReduction
open EllipticSmoothTorsionReduction WeierstrassVariableChange WeierstrassVeluPolynomial
noncomputable local instance instDecidableEqEllipticFiniteKernelSmoothReduction {α : Type*} :
    DecidableEq α := Classical.decEq _

/-- [DkMath.Lib] モデルの等式による点の輸送は滑らかな還元条件を変えない。 -/
theorem smooth_pointEquiv_of_model {L : Type*} [Field L] (A : ValuationSubring L)
    (M : WeierstrassCurve A) (V : WeierstrassCurve L) (hm : M.map A.subtype = V)
    (P : V.toAffine.Point) :
    HasSmoothReduction M (pointEquivOfModelEq hm.symm P) ↔ HasSmoothReduction M P := by
  subst V
  rfl

variable {K : Type*} [Field K] [CharZero K] (E : WeierstrassCurve K)
  (H : AddSubgroup (Points E)) (A : ValuationSubring (AlgebraicClosure K))
  (M : WeierstrassCurve A) (hM : M.map A.subtype = E.map (algebraMap K (AlgebraicClosure K)))

/-- [DkMath.Lib] 同じHを同じ付値環モデルの一般ファイバーへ入れる加法準同型。座標値を保つ。 -/
noncomputable def kernelIntegralPointHom : H →+ (M.map A.subtype).toAffine.Point :=
  (pointEquivOfModelEq hM.symm).toAddMonoidHom.comp H.subtype

/-- [DkMath.Lib] 同じ滑らかなHの剰余点群への実際の加法準同型。 -/
noncomputable def smoothKernelReduction (hs : ∀ Q : H, HasSmoothReduction M Q.val) :
    H →+ (M.map (residue A)).toAffine.Point :=
  (zeroComponentReduction M).comp {
    toFun Q := ⟨kernelIntegralPointHom E H A M hM Q,
      (smooth_pointEquiv_of_model A M _ hM Q.val).mpr (hs Q)⟩
    map_zero' := Subtype.ext (map_zero _)
    map_add' P Q := Subtype.ext (map_add _ P Q) }

include hM in
/-- [DkMath.Lib] 単元位数捩れの同じ滑らかな核は、還元で点を失わない。 -/
theorem smoothKernelReduction_injective (hs : ∀ Q : H, HasSmoothReduction M Q.val)
    (n : ℕ) (hkill : ∀ Q : H, n • Q.val = 0) (hn : A.valuation (n : AlgebraicClosure K) = 1) :
    Function.Injective (smoothKernelReduction E H A M hM hs) := by
  intro P Q he
  let i := kernelIntegralPointHom E H A M hM
  have hsm (R : H) : HasSmoothReduction M (i R) := (smooth_pointEquiv_of_model A M _ hM R.val).mpr (hs R)
  have hk (R : H) : n • i R = 0 := by
    have hR : n • R = 0 := Subtype.ext (hkill R)
    simpa only [map_nsmul, map_zero] using congrArg i hR
  have hp : i P = i Q := reduce_injOn_torsion M hn ⟨hsm P, hk P⟩ ⟨hsm Q, hk Q⟩ he
  exact Subtype.ext ((pointEquivOfModelEq hM.symm).injective hp)

/-- [DkMath.Lib] 同じ還元準同型の像は、元のHと正確に同じ点数を持つ。 -/
theorem card_smoothKernelReduction_range
    (hs : ∀ Q : H, HasSmoothReduction M Q.val) (n : ℕ) (hkill : ∀ Q : H, n • Q.val = 0)
    (hn : A.valuation (n : AlgebraicClosure K) = 1) :
    Nat.card (smoothKernelReduction E H A M hM hs).range = Nat.card H :=
  (Nat.card_congr (Equiv.ofInjective _ (smoothKernelReduction_injective E H A M hM hs n hkill hn))).symm

/-- [DkMath.Lib] 同じ還元像は有限である。ncardの無限集合での既定値を使わない。 -/
theorem finite_smoothKernelReduction_range [Finite H]
    (hs : ∀ Q : H, HasSmoothReduction M Q.val) (n : ℕ) (hkill : ∀ Q : H, n • Q.val = 0)
    (hn : A.valuation (n : AlgebraicClosure K) = 1) : Finite (smoothKernelReduction E H A M hM hs).range :=
  Nat.finite_of_card_ne_zero (by
    rw [card_smoothKernelReduction_range E H A M hM hs n hkill hn]
    exact Nat.card_ne_zero.mpr ⟨inferInstance, inferInstance⟩)

/-- [DkMath.Lib] 同じ半核の還元像も点数を保つ。異なる代表を同じ剰余座標へ潰さない。 -/
theorem card_reduced_halfKernel [Fintype H]
    (hs : ∀ Q : H, HasSmoothReduction M Q.val) (n : ℕ) (hkill : ∀ Q : H, n • Q.val = 0)
    (hn : A.valuation (n : AlgebraicClosure K) = 1) (ho : Odd (Nat.card H)) :
    2 * ((halfKernel E H).image (smoothKernelReduction E H A M hM hs)).card + 1 = Nat.card H := by
  rw [Finset.card_image_of_injective _ (smoothKernelReduction_injective E H A M hM hs n hkill hn)]
  exact card_halfKernel E H ho

/-- [DkMath.Lib] 同じ核点の還元の両座標は、同じ整な元の剰余である。Oも便宜座標0で一致。 -/
theorem smoothKernelReduction_coordinates (hs : ∀ Q : H, HasSmoothReduction M Q.val)
    (n : ℕ) (hkill : ∀ Q : H, n • Q.val = 0) (hn : A.valuation (n : AlgebraicClosure K) = 1) (Q : H) :
    (smoothKernelReduction E H A M hM hs Q).xc =
        residue A ⟨Q.val.xc, (kernel_coordinates_mem E H n hkill A M hM hn Q).1⟩ ∧
      (smoothKernelReduction E H A M hM hs Q).yc =
        residue A ⟨Q.val.yc, (kernel_coordinates_mem E H n hkill A M hM hn Q).2⟩ := by
  by_cases hQ : Q.val = 0
  · have hq : Q = 0 := Subtype.ext hQ
    subst Q
    rw [map_zero]
    exact ⟨(map_zero _).symm, (map_zero _).symm⟩
  · have hxy := Point.nonsingular_xc_yc hQ
    have hmxy : (M.map A.subtype).toAffine.Nonsingular Q.val.xc Q.val.yc := hM.symm ▸ hxy
    have hi : kernelIntegralPointHom E H A M hM Q = Point.some Q.val.xc Q.val.yc hmxy := by
      change pointEquivOfModelEq hM.symm Q.val = _
      have heq : (Q.val : (E.map (algebraMap K (AlgebraicClosure K))).toAffine.Point) =
          Point.some Q.val.xc Q.val.yc hxy := Point.eq_some_xc_yc hQ
      exact (congrArg (pointEquivOfModelEq hM.symm) heq).trans (pointEquivOfModelEq_some hM.symm hxy)
    have hsm : HasSmoothReduction M (Point.some Q.val.xc Q.val.yc hmxy) := by
      rw [← hi]
      exact (smooth_pointEquiv_of_model A M _ hM Q.val).mpr (hs Q)
    have hx := (kernel_coordinates_mem E H n hkill A M hM hn Q).1
    have hy := (kernel_coordinates_mem E H n hkill A M hM hn Q).2
    have hns := (hasSmoothReduction_some_iff M hmxy).mp hsm hx hy
    have hr : smoothKernelReduction E H A M hM hs Q =
        Point.some (residue A ⟨Q.val.xc, hx⟩) (residue A ⟨Q.val.yc, hy⟩) hns := by
      change reducePointSmooth M (kernelIntegralPointHom E H A M hM Q) = _
      rw [hi, reducePointSmooth_some_of_mem M hmxy hx hns]
    rw [hr]
    exact ⟨rfl, rfl⟩

/-- [DkMath.Lib] 付値環標的の剰余を、同じ単射な還元核の半核座標で実現する。
剰余核の節点商不変量を証明する次の工程へ、具体的な同じモデルを渡す。 -/
theorem valuationKernelModel_residue_of_smooth [Fintype H]
    (hs : ∀ Q : H, HasSmoothReduction M Q.val) (n : ℕ) (hkill : ∀ Q : H, n • Q.val = 0)
    (hn : A.valuation (n : AlgebraicClosure K) = 1) :
    (valuationKernelModel E H n hkill A M hM hn).map (residue A) =
      polynomialModel (M.map (residue A)) (halfKernel E H)
        (fun Q => (smoothKernelReduction E H A M hM hs Q).xc)
        (fun Q => (smoothKernelReduction E H A M hM hs Q).yc) := by
  rw [valuationKernelModel_residue]
  have hx : (fun Q : H => residue A ⟨Q.val.xc, (kernel_coordinates_mem E H n hkill A M hM hn Q).1⟩) =
      (fun Q => (smoothKernelReduction E H A M hM hs Q).xc) :=
    funext (fun Q => (smoothKernelReduction_coordinates E H A M hM hs n hkill hn Q).1.symm)
  have hy : (fun Q : H => residue A ⟨Q.val.yc, (kernel_coordinates_mem E H n hkill A M hM hn Q).2⟩) =
      (fun Q => (smoothKernelReduction E H A M hM hs Q).yc) :=
    funext (fun Q => (smoothKernelReduction_coordinates E H A M hM hs n hkill hn Q).2.symm)
  rw [hx, hy]

end DkMath.Lib.NumberTheory.EllipticFiniteKernel
