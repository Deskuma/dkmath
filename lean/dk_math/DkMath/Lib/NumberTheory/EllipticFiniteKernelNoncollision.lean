/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.EllipticFiniteKernelCollision
import DkMath.Lib.NumberTheory.WeierstrassNodalOrbit

#print "file: DkMath.Lib.NumberTheory.EllipticFiniteKernelNoncollision"

/-!
# 非衝突軌道の整性と、同じ商座標の還元

[DkMath.Lib] 滑らかな核Hと滑らかな点Pの還元像が衝突しないとき、
各P+Qの還元はOでない。したがって各座標は付値環に属し、実際の
還元点の座標はその剰余である。正規化された有限座標和の還元を計算する。
剰余曲線の節点公式と標的の非特異性は別に接続する。
-/
namespace DkMath.Lib.NumberTheory
open WeierstrassCurve WeierstrassCurve.Affine IsLocalRing
open EllipticGoodReductionSeparation EllipticSmoothReduction WeierstrassVariableChange
open scoped BigOperators
noncomputable local instance instDecidableEqEllipticFiniteKernelNoncollision {α : Type*} : DecidableEq α :=
  Classical.decEq _

namespace WeierstrassModelReduction
variable {L : Type*} [Field L] [DecidableEq L] (A : ValuationSubring L)
  (M : WeierstrassCurve A) (V : WeierstrassCurve L) (hM : M.map A.subtype = V)

/-- [DkMath.Lib] 滑らかな点の還元がOでないとき、同じ実点の両座標は整で、
その剰余が実際の還元点の座標となる。有限点と無限遠を取り違えない。 -/
theorem modelReduce_coordinates_of_ne_zero (P : V.toAffine.Point)
    (hs : HasSmoothReduction M P) (hr : modelReduce A M V hM P ≠ 0) :
    ∃ (hx : P.xc ∈ A) (hy : P.yc ∈ A),
      (modelReduce A M V hM P).xc = residue A ⟨P.xc, hx⟩ ∧
      (modelReduce A M V hM P).yc = residue A ⟨P.yc, hy⟩ := by
  have hp : P ≠ 0 := fun he => hr (he ▸ modelReduce_zero A M V hM)
  have hx : P.xc ∈ A := by
    by_contra hn
    exact hr ((modelReduce_eq_zero_iff A M V hM hs).mpr (Or.inr hn))
  have hns := Point.nonsingular_xc_yc hp
  have hy := EllipticTorsionValuationIntegrality.y_mem_of_x_mem A M V hM hns.1 hx
  have hns' := (hasSmoothReduction_some_iff M hns).mp
    (by rwa [← Point.eq_some_xc_yc hp]) hx hy
  have he : P = Point.some P.xc P.yc hns := Point.eq_some_xc_yc hp
  have hred := (congrArg (modelReduce A M V hM) he).trans
    (modelReduce_some A M V hM hns hx hns')
  refine ⟨hx, hy, ?_, ?_⟩ <;> rw [hred] <;> rfl

end WeierstrassModelReduction

namespace EllipticFiniteKernel
open EllipticTorsionRepresentation WeierstrassModelReduction
variable {K : Type*} [Field K] [CharZero K] (E : WeierstrassCurve K) [E.IsElliptic]
  (H : AddSubgroup (Points E)) [Fintype H] (n : ℕ) (hkill : ∀ Q : H, n • Q.val = 0)
  (A : ValuationSubring (AlgebraicClosure K)) (M : WeierstrassCurve A)
  (hM : M.map A.subtype = E.map (algebraMap K (AlgebraicClosure K)))
  (hn : A.valuation (n : AlgebraicClosure K) = 1)
  (hs : ∀ Q : H, HasSmoothReduction M Q.val)
  (P : Points E) (hP : HasSmoothReduction M P)
  (hout : ∀ Q : H, modelReduce A M _ hM P ≠ modelReduce A M _ hM Q.val)

include hout in
omit [Fintype H] [CharZero K] [E.IsElliptic] in
/-- [DkMath.Lib] 同じ還元核の外にある点は、一般ファイバーでも同じHの外にある。 -/
theorem not_mem_of_reduction_noncollision : P ∉ H := by
  intro hp
  exact hout ⟨P, hp⟩ rfl

include hs hP hout in
omit [Fintype H] [CharZero K] [E.IsElliptic] in
/-- [DkMath.Lib] 衝突しない軌道の各点は、同じ整モデルで滑らかに有限点へ還元する。
Qと−Qを同じ実核内で扱い、還元関数を滑らかな点の上でだけ加法的に使う。 -/
theorem translated_reduction_ne_zero (Q : H) :
    HasSmoothReduction M (P + Q.val) ∧ modelReduce A M _ hM (P + Q.val) ≠ 0 := by
  have hsm := smooth_add_of_model A M _ hM hP (hs Q)
  constructor
  · exact hsm
  · intro hz
    have ha := modelReduce_add A M _ hM hP (hs Q)
    have hz' : modelReduce A M _ hM P + modelReduce A M _ hM Q.val = 0 := ha.symm.trans hz
    have hnq : modelReduce A M _ hM (-Q).val = -modelReduce A M _ hM Q.val := by
      change smoothKernelReduction E H A M hM hs (-Q) = -smoothKernelReduction E H A M hM hs Q
      exact map_neg _ Q
    exact hout (-Q) ((eq_neg_of_add_eq_zero_left hz').trans hnq.symm)


include hM hs hP hout in
omit [Fintype H] [CharZero K] [E.IsElliptic] in
/-- [DkMath.Lib] 非衝突軌道の全点の二座標は同じ付値環で整である。 -/
theorem translated_coordinates_mem (Q : H) : (P + Q.val).xc ∈ A ∧ (P + Q.val).yc ∈ A := by
  have h := translated_reduction_ne_zero E H A M hM hs P hP hout Q
  obtain ⟨hx, hy, _, _⟩ := modelReduce_coordinates_of_ne_zero A M _ hM (P + Q.val) h.1 h.2
  exact ⟨hx, hy⟩

omit [Fintype H] [CharZero K] [E.IsElliptic] in
/-- [DkMath.Lib] 非衝突軌道の座標の剰余は、同じ源点と同じ還元核点の和の座標に等しい。 -/
theorem translated_coordinates_residue (Q : H) :
    let hx := (translated_coordinates_mem E H A M hM hs P hP hout Q).1
    let hy := (translated_coordinates_mem E H A M hM hs P hP hout Q).2
    residue A ⟨(P + Q.val).xc, hx⟩ =
        (modelReduce A M _ hM P + smoothKernelReduction E H A M hM hs Q).xc ∧
      residue A ⟨(P + Q.val).yc, hy⟩ =
        (modelReduce A M _ hM P + smoothKernelReduction E H A M hM hs Q).yc := by
  have h := translated_reduction_ne_zero E H A M hM hs P hP hout Q
  obtain ⟨hx, hy, hxc, hyc⟩ := modelReduce_coordinates_of_ne_zero A M _ hM (P + Q.val) h.1 h.2
  have he := modelReduce_add A M _ hM hP (hs Q)
  have hq : smoothKernelReduction E H A M hM hs Q = modelReduce A M _ hM Q.val := rfl
  rw [← hq] at he
  constructor
  · exact hxc.symm.trans (congrArg Point.xc he)
  · exact hyc.symm.trans (congrArg Point.yc he)

include n hkill hn hM hs hP hout in
/-- [DkMath.Lib] 非衝突では同じ一般ファイバーの商座標も整である。
実際の核全体に添字付けた正規化和を使う。 -/
theorem kernelAt_coordinates_mem :
    let hp := not_mem_of_reduction_noncollision E H A M hM P hout
    kernelXAt E H P hp ∈ A ∧ kernelYAt E H P hp ∈ A := by
  dsimp only
  rw [kernelXAt_eq_sum, kernelYAt_eq_sum]
  constructor
  · apply A.sub_mem
    · exact A.sum_mem (fun Q _ => (translated_coordinates_mem E H A M hM hs P hP hout Q).1)
    · exact A.sum_mem (fun Q _ => (kernel_coordinates_mem E H n hkill A M hM hn Q).1)
  · apply A.sub_mem
    · exact A.sum_mem (fun Q _ => (translated_coordinates_mem E H A M hM hs P hP hout Q).2)
    · exact A.sum_mem (fun Q _ => (kernel_coordinates_mem E H n hkill A M hM hn Q).2)

/-- [DkMath.Lib] 非衝突の同じ商X,Yの剰余は、同じ還元核での正規化座標和。
一般ファイバーと剰余ファイバーで点や核を選び直さず、二座標を同時に運ぶ。
この等式だけでは剰余標的での非特異性は主張しない。 -/
theorem kernelAt_coordinates_residue :
    let hp := not_mem_of_reduction_noncollision E H A M hM P hout
    let hx := (kernelAt_coordinates_mem E H n hkill A M hM hn hs P hP hout).1
    let hy := (kernelAt_coordinates_mem E H n hkill A M hM hn hs P hP hout).2
    residue A ⟨kernelXAt E H P hp, hx⟩ =
      (∑ Q : H, (modelReduce A M _ hM P + smoothKernelReduction E H A M hM hs Q).xc) -
        ∑ Q : H, (smoothKernelReduction E H A M hM hs Q).xc ∧
    residue A ⟨kernelYAt E H P hp, hy⟩ =
      (∑ Q : H, (modelReduce A M _ hM P + smoothKernelReduction E H A M hM hs Q).yc) -
        ∑ Q : H, (smoothKernelReduction E H A M hM hs Q).yc := by
  dsimp only
  let hp := not_mem_of_reduction_noncollision E H A M hM P hout
  let tx (Q : H) : A := ⟨(P + Q.val).xc, (translated_coordinates_mem E H A M hM hs P hP hout Q).1⟩
  let ty (Q : H) : A := ⟨(P + Q.val).yc, (translated_coordinates_mem E H A M hM hs P hP hout Q).2⟩
  let kx (Q : H) : A := ⟨Q.val.xc, (kernel_coordinates_mem E H n hkill A M hM hn Q).1⟩
  let ky (Q : H) : A := ⟨Q.val.yc, (kernel_coordinates_mem E H n hkill A M hM hn Q).2⟩
  have ex : (⟨kernelXAt E H P hp, (kernelAt_coordinates_mem E H n hkill A M hM hn hs P hP hout).1⟩ : A) =
      (∑ Q, tx Q) - ∑ Q, kx Q := by
    apply Subtype.ext
    change kernelXAt E H P hp = A.subtype ((∑ Q, tx Q) - ∑ Q, kx Q)
    rw [map_sub, map_sum, map_sum]
    exact kernelXAt_eq_sum E H P hp
  have ey : (⟨kernelYAt E H P hp, (kernelAt_coordinates_mem E H n hkill A M hM hn hs P hP hout).2⟩ : A) =
      (∑ Q, ty Q) - ∑ Q, ky Q := by
    apply Subtype.ext
    change kernelYAt E H P hp = A.subtype ((∑ Q, ty Q) - ∑ Q, ky Q)
    rw [map_sub, map_sum, map_sum]
    exact kernelYAt_eq_sum E H P hp
  constructor
  · rw [ex, map_sub, map_sum, map_sum]
    congr 1
    · apply Finset.sum_congr rfl
      intro Q _
      exact (translated_coordinates_residue E H A M hM hs P hP hout Q).1
    · apply Finset.sum_congr rfl
      intro Q _
      exact (smoothKernelReduction_coordinates E H A M hM hs n hkill hn Q).1.symm
  · rw [ey, map_sub, map_sum, map_sum]
    congr 1
    · apply Finset.sum_congr rfl
      intro Q _
      exact (translated_coordinates_residue E H A M hM hs P hP hout Q).2
    · apply Finset.sum_congr rfl
      intro Q _
      exact (smoothKernelReduction_coordinates E H A M hM hs n hkill hn Q).2.symm

/-- [DkMath.Lib] 非衝突点の同じ商Xの剰余を、節点上のn倍点の座標で表す。
`e` は同じHを0からn−1までの倍数に列挙する同型であり、`henum` は
その列挙が同じ還元核の実点と一致することを記録する。原始根性と非衝突から
剰余点のn倍がOでないことも内部で示す。中心や列挙の存在はこの定理の仮定である。 -/
theorem kernelXAt_residue_nodal_orbit
    {x₀ y₀ α : ResidueField A}
    (F : EllipticNodalTorsion.NodalTorsion.Frame (M.map (residue A)) x₀ y₀ α)
    (hsep : α ≠ -(M.map (residue A)).a₁ - α) (hn0 : n ≠ 0)
    (R : (M.map (residue A)).toAffine.Point) (e : Fin n ≃ H)
    (henum : ∀ j : Fin n, smoothKernelReduction E H A M hM hs (e j) = j.val • R)
    (hroot : IsPrimitiveRoot (EllipticNodalTorsion.NodalTorsion.tc
      (M.map (residue A)) x₀ y₀ α R) n) :
    let hp := not_mem_of_reduction_noncollision E H A M hM P hout
    let hx := (kernelAt_coordinates_mem E H n hkill A M hM hn hs P hP hout).1
    residue A ⟨kernelXAt E H P hp, hx⟩ =
      (n : ResidueField A) ^ 2 * (n • modelReduce A M _ hM P).xc +
        ((n : ResidueField A) - (n : ResidueField A) ^ 2) * x₀ -
        ∑ Q : H, (smoothKernelReduction E H A M hM hs Q).xc := by
  let T := modelReduce A M _ hM P
  let tc := EllipticNodalTorsion.NodalTorsion.tc (M.map (residue A)) x₀ y₀ α
  let : NeZero n := ⟨hn0⟩
  have hT : n • T ≠ 0 := by
    intro hT0
    have ht : tc T ^ n = 1 := (WeierstrassNodalOrbit.nsmul_eq_zero_iff F hsep T).mp hT0
    obtain ⟨j, hj, he⟩ := hroot.eq_pow_of_pow_eq_one ht
    have hh : T = j • R := WeierstrassNodalOrbit.tc_injective F hsep (by
      rw [EllipticNodalTorsion.NodalTorsion.tc_nsmul F]
      exact he.symm)
    exact hout (e ⟨j, hj⟩) (hh.trans (henum ⟨j, hj⟩).symm)
  have hsum : (∑ Q : H, (T + smoothKernelReduction E H A M hM hs Q).xc) =
      ∑ j ∈ Finset.range n, (T + j • R).xc := by
    calc
      _ = ∑ j : Fin n, (T + smoothKernelReduction E H A M hM hs (e j)).xc :=
        (e.sum_comp _).symm
      _ = ∑ j : Fin n, (T + j.val • R).xc := by simp only [henum]
      _ = ∑ j ∈ Finset.range n, (T + j • R).xc := Fin.sum_univ_eq_sum_range (fun j : ℕ => (T + j • R).xc) n
  have horbit := WeierstrassNodalOrbit.translated_x_sum_nsmul F hsep T R hroot hT
  have hcoords := (kernelAt_coordinates_residue E H n hkill A M hM hn hs P hP hout).1
  change _ = (∑ Q : H, (T + smoothKernelReduction E H A M hM hs Q).xc) - _ at hcoords
  rw [hsum, horbit] at hcoords
  dsimp only
  linear_combination hcoords

/-- [DkMath.Lib] 素数位数の同じ滑らかな核では、節点比の原始根と巡回列挙を
核の点数・単射な還元から内部構成する。非衝突点の商Xの剰余が同じn倍点で表される。 -/
theorem kernelXAt_residue_nodal_prime [Fact n.Prime] (hcard : Nat.card H = n)
    {x₀ y₀ α : ResidueField A}
    (F : EllipticNodalTorsion.NodalTorsion.Frame (M.map (residue A)) x₀ y₀ α)
    (hsep : α ≠ -(M.map (residue A)).a₁ - α) :
    let hp := not_mem_of_reduction_noncollision E H A M hM P hout
    let hx := (kernelAt_coordinates_mem E H n hkill A M hM hn hs P hP hout).1
    residue A ⟨kernelXAt E H P hp, hx⟩ =
      (n : ResidueField A) ^ 2 * (n • modelReduce A M _ hM P).xc +
        ((n : ResidueField A) - (n : ResidueField A) ^ 2) * x₀ -
        ∑ Q : H, (smoothKernelReduction E H A M hM hs Q).xc := by
  let : NeZero n := ⟨(Fact.out : n.Prime).ne_zero⟩
  let e : ZMod n ≃+ H := addEquivOfPrimeCardEq (Nat.card_zmod n) hcard
  let f := smoothKernelReduction E H A M hM hs
  let R := f (e 1)
  let efin : Fin n ≃ H := (ZMod.finEquiv n).toEquiv.trans e.toEquiv
  have hord : addOrderOf R = n :=
    (addOrderOf_injective f (smoothKernelReduction_injective E H A M hM hs n hkill hn) (e 1)).trans
      ((e.addOrderOf_eq 1).trans (ZMod.addOrderOf_one n))
  have hroot := hord ▸ WeierstrassNodalFrame.primitiveRoot_tc F hsep R
  have henum (j : Fin n) : f (efin j) = j.val • R := by
    change f (e ((ZMod.finEquiv n) j)) = j.val • f (e 1)
    have hcast : (ZMod.finEquiv n) j = (j.val : ZMod n) := by
      cases n with
      | zero => exact Fin.elim0 j
      | succ n =>
        apply ZMod.val_injective (n + 1)
        rw [ZMod.val_natCast_of_lt j.isLt]
        rfl
    rw [hcast, ← Nat.smul_one_eq_cast, map_nsmul, map_nsmul]
  exact kernelXAt_residue_nodal_orbit E H n hkill A M hM hn hs P hP hout F hsep
    (Fact.out : n.Prime).ne_zero R efin henum hroot

end EllipticFiniteKernel
end DkMath.Lib.NumberTheory
