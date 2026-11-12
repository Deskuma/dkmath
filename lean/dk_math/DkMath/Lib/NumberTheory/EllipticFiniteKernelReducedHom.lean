/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.EllipticFiniteKernelNodalCenterAll

#print "file: DkMath.Lib.NumberTheory.EllipticFiniteKernelReducedHom"

/-!
# 同じ商準同型を実際の還元像へ降ろす

[DkMath.Lib] 源の零成分の還元像だけを定義域とし、商をとってから還元する。
同じ還元像を持つ二点の差は無限遠へ還元するため、その商像も無限遠へ還元する。
このことから代表の選択に依存しない準同型と可換図式を得る。
剰余点群全体への全射性や、剰余のVélu座標・冪写像との一致は主張しない。
-/
namespace DkMath.Lib.NumberTheory

namespace AdditiveRangeDescent
variable {G B C : Type*} [AddCommGroup G] [AddCommGroup B] [AddCommGroup C]

/-- [DkMath.Lib] 一方の準同型の核が他方の核に含まれると、同じ値の二点は他方でも同じ値を持つ。 -/
theorem eq_of_same_image (g : G →+ B) (h : G →+ C) (hk : g.ker ≤ h.ker)
    {x y : G} (he : g x = g y) : h x = h y := by
  apply sub_eq_zero.mp
  rw [← map_sub]
  apply AddMonoidHom.mem_ker.mp
  apply hk
  change g (x - y) = 0
  rw [map_sub, he, sub_self]

/-- [DkMath.Lib] 核の包含から、同じ準同型の実際の像への一意な因子を構成する。
選択した代表によらないことは核の包含から証明し、像全体が終域である必要はない。 -/
noncomputable def onRange (g : G →+ B) (h : G →+ C) (hk : g.ker ≤ h.ker) : g.range →+ C where
  toFun b := h (Classical.choose b.property)
  map_zero' := by
    have he : g (Classical.choose (0 : g.range).property) = g 0 := by
      rw [Classical.choose_spec (0 : g.range).property, map_zero]
      rfl
    rw [eq_of_same_image g h hk he, map_zero]
  map_add' a b := by
    have he : g (Classical.choose (a + b).property) =
        g (Classical.choose a.property + Classical.choose b.property) := by
      rw [Classical.choose_spec (a + b).property, map_add,
        Classical.choose_spec a.property, Classical.choose_spec b.property]
      rfl
    rw [eq_of_same_image g h hk he, map_add]

/-- [DkMath.Lib] 実際の像へ降りた準同型を元の点へ適用すると、元の準同型そのものになる。 -/
theorem onRange_apply (g : G →+ B) (h : G →+ C) (hk : g.ker ≤ h.ker) (x : G) :
    onRange g h hk ⟨g x, ⟨x, rfl⟩⟩ = h x := by
  apply eq_of_same_image g h hk
  exact Classical.choose_spec (⟨g x, ⟨x, rfl⟩⟩ : g.range).property

end AdditiveRangeDescent

namespace EllipticFiniteKernel
open WeierstrassCurve WeierstrassCurve.Affine IsLocalRing
open EllipticTorsionRepresentation EllipticGoodReductionSeparation EllipticSmoothReduction
open EllipticNodalTorsion.NodalTorsion WeierstrassVariableChange WeierstrassModelReduction
noncomputable local instance instDecidableEqEllipticFiniteKernelReducedHom {α : Type*} : DecidableEq α :=
  Classical.decEq _
private theorem pointEquiv_symm_of_eq {L : Type*} [Field L] {W V : WeierstrassCurve L} (h : W = V) :
    pointEquivOfModelEq h.symm = (pointEquivOfModelEq h).symm := by
  subst V
  rfl

private theorem pointEquiv_inverse_apply {L : Type*} [Field L] {W V : WeierstrassCurve L}
    (h : W = V) (P : V.toAffine.Point) : pointEquivOfModelEq h (pointEquivOfModelEq h.symm P) = P := by
  subst V
  rfl

variable {K : Type*} [Field K] [CharZero K] (E : WeierstrassCurve K) [E.IsElliptic]
  (H : AddSubgroup (Points E)) [Fintype H] (p : ℕ) [Fact p.Prime]
  (hcard : Nat.card H = p) (hp2 : p ≠ 2) (hkill : ∀ Q : H, p • Q.val = 0)
  (A : ValuationSubring (AlgebraicClosure K)) (M : WeierstrassCurve A)
  (hM : M.map A.subtype = E.map (algebraMap K (AlgebraicClosure K)))
  (hp : A.valuation (p : AlgebraicClosure K) = 1)
  (hs : ∀ Q : H, HasSmoothReduction M Q.val)
  {x₀ y₀ α : ResidueField A} (F : Frame (M.map (residue A)) x₀ y₀ α)
  (hsep : α ≠ -(M.map (residue A)).a₁ - α)

/-- [DkMath.Lib] 同じ零成分の還元核は、同じ実商を適用してからの還元核に含まれる。
無限遠と非整xを区別し、前章の全点商写像による無限遠近傍保存を使用する。 -/
theorem zeroComponent_reduction_ker_le :
    (zeroComponentReduction M).ker ≤
      ((zeroComponentReduction (valuationKernelModel E H p hkill A M hM hp)).comp
        (nodalZeroComponentHom E H p hcard hp2 hkill A M hM hp hs F hsep)).ker := by
  intro P hP
  let ho : Odd (Nat.card H) := hcard ▸ (Fact.out : p.Prime).odd_of_ne_two hp2
  let U := valuationKernelModel E H p hkill A M hM hp
  let hU := valuationKernelModel_map E H p hkill A M hM hp ho
  let T := pointEquivOfModelEq hM P.val
  have hsm : HasSmoothReduction M T := by
    apply (smooth_pointEquiv_of_model A M _ hM T).mp
    have he := pointEquiv_symm_of_eq hM
    rw [he, AddEquiv.symm_apply_apply]
    exact P.property
  have hr : modelReduce A M _ hM T = 0 := by
    change reducePointSmooth M (pointEquivOfModelEq hM.symm (pointEquivOfModelEq hM P.val)) = 0
    have he := pointEquiv_symm_of_eq hM
    rw [he, AddEquiv.symm_apply_apply]
    exact hP
  have hh := (oddKernelPointMap_of_reduce_zero E H p hkill A M hM hp ho T hsm hr).2
  change reducePointSmooth U (pointEquivOfModelEq hU.symm (oddKernelPointMap E H ho T)) = 0 at hh
  change reducePointSmooth U
    ((nodalZeroComponentHom E H p hcard hp2 hkill A M hM hp hs F hsep P).val) = 0
  change reducePointSmooth U (pointEquivOfModelEq hU.symm (oddKernelPointHom E H ho T)) = 0
  exact hh

/-- [DkMath.Lib] 同じ源零成分の実際の還元像から、同じ商標的の剰余点群への準同型。
定義域は実際の還元像であり、全剰余点が持ち上がるという主張を含めない。 -/
noncomputable def nodalReducedHom : (zeroComponentReduction M).range →+
    ((valuationKernelModel E H p hkill A M hM hp).map (residue A)).toAffine.Point :=
  AdditiveRangeDescent.onRange (zeroComponentReduction M)
    ((zeroComponentReduction (valuationKernelModel E H p hkill A M hM hp)).comp
      (nodalZeroComponentHom E H p hcard hp2 hkill A M hM hp hs F hsep))
    (zeroComponent_reduction_ker_le E H p hcard hp2 hkill A M hM hp hs F hsep)

/-- [DkMath.Lib] 同じ実際の零成分点で、商を取ってから還元することと、還元像上の準同型が可換。 -/
theorem nodalReducedHom_commutes (P : zeroComponentSubgroup M) :
    nodalReducedHom E H p hcard hp2 hkill A M hM hp hs F hsep
      ⟨zeroComponentReduction M P, ⟨P, rfl⟩⟩ =
      zeroComponentReduction (valuationKernelModel E H p hkill A M hM hp)
        (nodalZeroComponentHom E H p hcard hp2 hkill A M hM hp hs F hsep P) :=
  AdditiveRangeDescent.onRange_apply _ _ _ P

/-- [DkMath.Lib] 可換図式の右辺を、元の同じ全点商準同型と指定モデルでの還元として書く。
零成分への制限に使った中心の選択は、この具体的な右辺には現れない。 -/
theorem nodalReducedHom_commutes_model (P : zeroComponentSubgroup M) :
    nodalReducedHom E H p hcard hp2 hkill A M hM hp hs F hsep
      ⟨zeroComponentReduction M P, ⟨P, rfl⟩⟩ =
      modelReduce A (valuationKernelModel E H p hkill A M hM hp) (kernelModel E H)
        (valuationKernelModel_map E H p hkill A M hM hp (hcard ▸ (Fact.out : p.Prime).odd_of_ne_two hp2))
        (oddKernelPointHom E H (hcard ▸ (Fact.out : p.Prime).odd_of_ne_two hp2)
          (pointEquivOfModelEq hM P.val)) := by
  have hh := nodalReducedHom_commutes E H p hcard hp2 hkill A M hM hp hs F hsep P
  change _ = reducePointSmooth (valuationKernelModel E H p hkill A M hM hp)
    (pointEquivOfModelEq (valuationKernelModel_map E H p hkill A M hM hp
      (hcard ▸ (Fact.out : p.Prime).odd_of_ne_two hp2)).symm
      (oddKernelPointHom E H (hcard ▸ (Fact.out : p.Prime).odd_of_ne_two hp2) (pointEquivOfModelEq hM P.val))) at hh
  exact hh

/-- [DkMath.Lib] 同じHの各点の実際の還元像は、還元像上の商準同型でOへ送られる。
Hを別の剰余核へ置き換えず、元の商準同型の零ファイバーを使う。 -/
theorem nodalReducedHom_kills_kernel (Q : H) :
    let P : zeroComponentSubgroup M := ⟨kernelIntegralPointHom E H A M hM Q,
      (smooth_pointEquiv_of_model A M _ hM Q.val).mpr (hs Q)⟩
    nodalReducedHom E H p hcard hp2 hkill A M hM hp hs F hsep
      ⟨smoothKernelReduction E H A M hM hs Q, ⟨P, rfl⟩⟩ = 0 := by
  let P : zeroComponentSubgroup M := ⟨kernelIntegralPointHom E H A M hM Q,
    (smooth_pointEquiv_of_model A M _ hM Q.val).mpr (hs Q)⟩
  have hm : pointEquivOfModelEq hM P.val ∈ H := by
    change pointEquivOfModelEq hM (pointEquivOfModelEq hM.symm Q.val) ∈ H
    have he : pointEquivOfModelEq hM (pointEquivOfModelEq hM.symm Q.val) =
        (Q.val : (E.map (algebraMap K (AlgebraicClosure K))).toAffine.Point) :=
      pointEquiv_inverse_apply hM Q.val
    exact he.symm ▸ Q.property
  have hz := (nodalZeroComponentHom_eq_zero_iff E H p hcard hp2 hkill A M hM hp hs F hsep P).mpr hm
  have hh := nodalReducedHom_commutes E H p hcard hp2 hkill A M hM hp hs F hsep P
  rw [hz, map_zero] at hh
  exact hh

/-- [DkMath.Lib] 同じ滑らかなHの還元を、源の実際の還元像に値を持つ準同型として記録する。
各核点の実際の持上げを使用し、剰余点群全体への持上げは要求しない。 -/
noncomputable def reducedKernelIntoRange : H →+ (zeroComponentReduction M).range where
  toFun Q := ⟨smoothKernelReduction E H A M hM hs Q,
    ⟨⟨kernelIntegralPointHom E H A M hM Q,
      (smooth_pointEquiv_of_model A M _ hM Q.val).mpr (hs Q)⟩, rfl⟩⟩
  map_zero' := Subtype.ext (map_zero (smoothKernelReduction E H A M hM hs))
  map_add' Q R := Subtype.ext (map_add (smoothKernelReduction E H A M hM hs) Q R)

include p hkill hp in
omit [Fintype H] [Fact p.Prime] [E.IsElliptic] in
/-- [DkMath.Lib] 単元位数の同じHは、その還元像への埋め込みでも点を失わない。 -/
theorem reducedKernelIntoRange_injective :
    Function.Injective (reducedKernelIntoRange E H A M hM hs) := by
  intro Q R he
  exact smoothKernelReduction_injective E H A M hM hs p hkill hp (congrArg Subtype.val he)

/-- [DkMath.Lib] 同じ還元核の像は、同じ還元像上商準同型の核に含まれる。
逆包含はまだ主張しない。 -/
theorem reducedKernelIntoRange_le_ker :
    (reducedKernelIntoRange E H A M hM hs).range ≤
      (nodalReducedHom E H p hcard hp2 hkill A M hM hp hs F hsep).ker := by
  rintro _ ⟨Q, rfl⟩
  change nodalReducedHom E H p hcard hp2 hkill A M hM hp hs F hsep
    ⟨smoothKernelReduction E H A M hM hs Q, _⟩ = 0
  exact nodalReducedHom_kills_kernel E H p hcard hp2 hkill A M hM hp hs F hsep Q

/-- [DkMath.Lib] 同じ還元核で源の実際の還元像を割った商から、同じ標的剰余点群への準同型。
核の包含から構成する。単射性・全射性・同型性は別の問題として保持する。 -/
noncomputable def nodalReducedQuotientHom :
    (zeroComponentReduction M).range ⧸ (reducedKernelIntoRange E H A M hM hs).range →+
      ((valuationKernelModel E H p hkill A M hM hp).map (residue A)).toAffine.Point :=
  QuotientAddGroup.lift (reducedKernelIntoRange E H A M hM hs).range
    (nodalReducedHom E H p hcard hp2 hkill A M hM hp hs F hsep)
    (reducedKernelIntoRange_le_ker E H p hcard hp2 hkill A M hM hp hs F hsep)

/-- [DkMath.Lib] 還元像の剰余類を送ると、元の同じ還元像上準同型の値になる。 -/
theorem nodalReducedQuotientHom_mk (R : (zeroComponentReduction M).range) :
    nodalReducedQuotientHom E H p hcard hp2 hkill A M hM hp hs F hsep
      (QuotientAddGroup.mk R) = nodalReducedHom E H p hcard hp2 hkill A M hM hp hs F hsep R :=
  QuotientAddGroup.lift_mk _ _ R

/-- [DkMath.Lib] 核の還元像と衝突しない零成分点は、商の後に無限遠へ還元しない。
非衝突なら商の実際の有限座標は整である。一方、商像は既に滑らかなので、
無限遠への還元は点が無限遠または x 非整であることと同値であり、両方を除く。 -/
theorem nodalReducedHom_ne_zero_of_noncollision (P : zeroComponentSubgroup M)
    (hout : ∀ Q : H, zeroComponentReduction M P ≠ smoothKernelReduction E H A M hM hs Q) :
    nodalReducedHom E H p hcard hp2 hkill A M hM hp hs F hsep
      ⟨zeroComponentReduction M P, ⟨P, rfl⟩⟩ ≠ 0 := by
  let ho : Odd (Nat.card H) := hcard ▸ (Fact.out : p.Prime).odd_of_ne_two hp2
  let := kernelModel_isElliptic_of_odd_card E H ho
  let T := pointEquivOfModelEq hM P.val
  have hsm : HasSmoothReduction M T := by
    apply (smooth_pointEquiv_of_model A M _ hM T).mp
    rw [pointEquiv_symm_of_eq hM, AddEquiv.symm_apply_apply]
    exact P.property
  have hnon : ∀ Q : H, modelReduce A M _ hM T ≠ modelReduce A M _ hM Q.val := by
    intro Q
    have hh := hout Q
    change reducePointSmooth M P.val ≠ reducePointSmooth M (pointEquivOfModelEq hM.symm Q.val) at hh
    change reducePointSmooth M (pointEquivOfModelEq hM.symm (pointEquivOfModelEq hM P.val)) ≠ _
    rw [pointEquiv_symm_of_eq hM, AddEquiv.symm_apply_apply]
    exact hh
  have hmem := (kernelAt_coordinates_mem E H p hkill A M hM hp hs T hsm hnon).1
  let hT := not_mem_of_reduction_noncollision E H A M hM T hnon
  have he : oddKernelPointMap E H ho T = Point.some _ _ (kernelAt_nonsingular E H T hT) :=
    kernelPointMap_of_not_mem E H T hT
  have hsmooth := oddKernelPointMap_smooth_of_nodal_frame E H p hcard hp2 hkill A M hM hp hs F hsep T hsm
  intro hz
  have hz' : modelReduce A (valuationKernelModel E H p hkill A M hM hp) (kernelModel E H)
      (valuationKernelModel_map E H p hkill A M hM hp ho) (oddKernelPointMap E H ho T) = 0 := by
    exact (nodalReducedHom_commutes_model E H p hcard hp2 hkill A M hM hp hs F hsep P).symm.trans hz
  rcases (modelReduce_eq_zero_iff A _ _ _ hsmooth).mp hz' with hz0 | hx
  · rw [he] at hz0
    exact Point.some_ne_zero _ hz0
  · rw [he, Point.xc_some] at hx
    exact hx hmem

/-- [DkMath.Lib] 還元像上の商準同型の核は、同じ有限核 H の還元像に正確に一致する。
衝突する点は前章で零に写り、衝突しない点は整な有限商座標を持つので零に写らない。 -/
theorem nodalReducedHom_ker_eq :
    (nodalReducedHom E H p hcard hp2 hkill A M hM hp hs F hsep).ker =
      (reducedKernelIntoRange E H A M hM hs).range := by
  apply le_antisymm
  · intro R hR
    obtain ⟨P, hP⟩ := R.property
    have he : R = ⟨zeroComponentReduction M P, ⟨P, rfl⟩⟩ := Subtype.ext hP.symm
    subst R
    change nodalReducedHom E H p hcard hp2 hkill A M hM hp hs F hsep _ = 0 at hR
    by_contra hn
    have hout : ∀ Q : H, zeroComponentReduction M P ≠ smoothKernelReduction E H A M hM hs Q := by
      intro Q heq
      apply hn
      exact ⟨Q, Subtype.ext heq.symm⟩
    exact nodalReducedHom_ne_zero_of_noncollision E H p hcard hp2 hkill A M hM hp hs F hsep P hout hR
  · exact reducedKernelIntoRange_le_ker E H p hcard hp2 hkill A M hM hp hs F hsep

/-- [DkMath.Lib] 源の零成分点の商像が O へ還元することは、源の還元点が同じ核 H の
還元像にあることと同値である。実点そのものが核に属すると主張するものではない。 -/
theorem nodalReducedHom_eq_zero_iff (P : zeroComponentSubgroup M) :
    nodalReducedHom E H p hcard hp2 hkill A M hM hp hs F hsep
      ⟨zeroComponentReduction M P, ⟨P, rfl⟩⟩ = 0 ↔
      ∃ Q : H, zeroComponentReduction M P = smoothKernelReduction E H A M hM hs Q := by
  have hk := nodalReducedHom_ker_eq E H p hcard hp2 hkill A M hM hp hs F hsep
  constructor
  · intro hz
    have hm : (⟨zeroComponentReduction M P, ⟨P, rfl⟩⟩ : (zeroComponentReduction M).range) ∈
        (reducedKernelIntoRange E H A M hM hs).range := hk ▸ hz
    obtain ⟨Q, hQ⟩ := hm
    exact ⟨Q, (congrArg Subtype.val hQ).symm⟩
  · rintro ⟨Q, hQ⟩
    have hm : (⟨zeroComponentReduction M P, ⟨P, rfl⟩⟩ : (zeroComponentReduction M).range) ∈
        (reducedKernelIntoRange E H A M hM hs).range := ⟨Q, Subtype.ext hQ.symm⟩
    have hz : (⟨zeroComponentReduction M P, ⟨P, rfl⟩⟩ : (zeroComponentReduction M).range) ∈
        (nodalReducedHom E H p hcard hp2 hkill A M hM hp hs F hsep).ker := hk.symm ▸ hm
    exact hz

/-- [DkMath.Lib] 同じ還元核で割った準同型は単射である。
これは還元像上での正確な核の一致から従う第一同型定理の単射部分であり、
標的剰余点群への全射性を主張しない。 -/
theorem nodalReducedQuotientHom_injective :
    Function.Injective (nodalReducedQuotientHom E H p hcard hp2 hkill A M hM hp hs F hsep) := by
  apply (QuotientAddGroup.injective_lift_iff _ _ _).2
  exact (nodalReducedHom_ker_eq E H p hcard hp2 hkill A M hM hp hs F hsep).symm

end EllipticFiniteKernel
end DkMath.Lib.NumberTheory
