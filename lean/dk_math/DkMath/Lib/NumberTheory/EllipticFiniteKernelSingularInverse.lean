/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/
import DkMath.Lib.NumberTheory.EllipticFiniteKernelNodalLevels
import DkMath.Lib.NumberTheory.EllipticFiniteKernelZeroComponentExact
import DkMath.Lib.NumberTheory.EllipticTorsionDepth
import DkMath.Lib.NumberTheory.EllipticBranchComparison

#print "file: DkMath.Lib.NumberTheory.EllipticFiniteKernelSingularInverse"

/-!
# 特異核による商の零成分逆像

[DkMath.Lib] 単元位数の奇数捩れ点の深さを既存の四状態軌道定理から供給する。
商像が滑らかな特異点は半核点と同じ深さを持つ。同じ水準の二点について接方向の
同枝・反対枝を比較すると、対応する核点またはその反対点を引いて滑らかになる。
-/
namespace DkMath.Lib.NumberTheory.EllipticFiniteKernel
open WeierstrassCurve WeierstrassCurve.Affine IsLocalRing
open EllipticTorsionRepresentation EllipticGoodReductionSeparation EllipticSmoothReduction
open EllipticCriticalCentre EllipticCriticalCentreAlgebra EllipticTangentDirections
open EllipticBranchComparison EllipticShallowSlope EllipticTorsionDepth WeierstrassVariableChange
noncomputable local instance instDecidableEqEllipticFiniteKernelSingularInverse {α : Type*} : DecidableEq α := Classical.decEq _

private theorem model_equiv_symm {L : Type*} [Field L] {W V : WeierstrassCurve L} (h : W = V) :
    pointEquivOfModelEq h.symm = (pointEquivOfModelEq h).symm := by subst V; rfl

private theorem branch_distance_of_model {L : Type*} [Field L] {A : ValuationSubring L}
    (M : WeierstrassCurve A) (V : WeierstrassCurve L) (hm : M.map A.subtype = V)
    (C : CriticalCentre A V) (D : TangentDirections C) {x₁ y₁ x₂ y₂ : L}
    (h₁ : V.toAffine.Equation x₁ y₁) (h₂ : V.toAffine.Equation x₂ y₂)
    (hX₁ : A.valuation (x₁ - C.x) < 1) (hX₂ : A.valuation (x₂ - C.x) < 1)
    (heq : A.valuation (x₁ - C.x) = A.valuation (x₂ - C.x))
    (hsh : A.valuation (equationDefect V C.x C.y) < A.valuation (x₁ - C.x) ^ 2) :
    A.valuation (centreSlope C x₁ y₁ - centreSlope C x₂ y₂) < 1 ∨
      A.valuation (centreSlope C x₁ y₁ - centreSlope C x₂ y₂) = 1 := by
  subst V
  exact branch_distance_dichotomy M C D h₁ h₂ hX₁ hX₂ heq hsh

variable {K : Type*} [Field K] [CharZero K] (E : WeierstrassCurve K) [E.IsElliptic]
  (H : AddSubgroup (Points E)) [Fintype H] (p : ℕ) [Fact p.Prime]
  (hcard : Nat.card H = p) (hp2 : p ≠ 2) (hkill : ∀ Q : H, p • Q.val = 0)
  (A : ValuationSubring (AlgebraicClosure K)) (M : WeierstrassCurve A)
  (hM : M.map A.subtype = E.map (algebraMap K (AlgebraicClosure K)))
  (hp : A.valuation (p : AlgebraicClosure K) = 1)
  (C : CriticalCentre A (E.map (algebraMap K (AlgebraicClosure K)))) (D : TangentDirections C)
  (hbad : ∀ Q : H, Q.val ≠ 0 → ¬ HasSmoothReduction M Q.val)

include hp2 hkill hM hp D hbad in
omit [Fintype H] [E.IsElliptic] in
/-- [DkMath.Lib] 特異に還元する非零核点は、同じ節点中心に対して浅い。
既存の奇数捩れ軌道定理から、中心誤差の付値が距離の二乗より小さいことを供給する。 -/
theorem singular_kernel_shallow (Q : H) (hQ : Q.val ≠ 0) :
    A.valuation (equationDefect (E.map (algebraMap K (AlgebraicClosure K))) C.x C.y) <
      A.valuation (Q.val.xc - C.x) ^ 2 := by
  have hx := (nonsmooth_coordinates_congr E A M hM C Q.val (hbad Q hQ)).1
  have hns := Point.nonsingular_xc_yc hQ
  have he := Point.eq_some_xc_yc hQ
  have ht : p • Point.some Q.val.xc Q.val.yc hns = 0 := by
    rw [← he]
    exact hkill Q
  exact (odd_torsion_depth_of_model M _ hM C D ((Fact.out : p.Prime).odd_of_ne_two hp2)
    (by have := (Fact.out : p.Prime).two_le; omega) hp hns ht hx).1

include hp2 hkill hM hp D hbad in
omit [E.IsElliptic] in
/-- [DkMath.Lib] 各半核点における商座標の誤差条件を、特異な奇素数核から供給する。
4 が単元である必要はないので、剰余標数 2 も排除しない。 -/
theorem singular_kernel_half_deep :
    ∀ Q ∈ halfKernel E H, A.valuation (4 * equationDefect
      (E.map (algebraMap K (AlgebraicClosure K))) C.x C.y) < A.valuation (Q.val.xc - C.x) ^ 2 := by
  intro Q hQ
  have hQ0 : Q.val ≠ 0 := fun hz => ((mem_halfKernel E H Q).mp hQ).1 (Subtype.ext hz)
  have hsh := singular_kernel_shallow E H p hp2 hkill A M hM hp C D hbad Q hQ0
  rw [map_mul]
  exact (mul_le_of_le_one_left' ((A.valuation_le_one_iff _).mpr (ofNat_mem A 4))).trans_lt hsh

include hM D in
omit [CharZero K] [E.IsElliptic] in
/-- [DkMath.Lib] 同じ節点水準の浅い二つの実点では、差または和が零成分に入る。
傾きが同じ枝なら差、反対枝なら和を取り、無限遠と非整座標も既存の枝定理で扱う。 -/
theorem same_level_sub_or_add_smooth (P R : Points E) (hP0 : P ≠ 0) (hR0 : R ≠ 0)
    (hP : A.valuation (P.xc - C.x) < 1) (hR : A.valuation (R.xc - C.x) < 1)
    (heq : A.valuation (P.xc - C.x) = A.valuation (R.xc - C.x))
    (hsh : A.valuation (equationDefect (E.map (algebraMap K (AlgebraicClosure K))) C.x C.y) <
      A.valuation (P.xc - C.x) ^ 2) :
    HasSmoothReduction M (P - R) ∨ HasSmoothReduction M (P + R) := by
  have hPn := Point.nonsingular_xc_yc hP0
  have hRn := Point.nonsingular_xc_yc hR0
  have eP := Point.eq_some_xc_yc hP0
  have eR := Point.eq_some_xc_yc hR0
  have hd := branch_distance_of_model M _ hM C D hPn.1 hRn.1 hP hR heq hsh
  rcases hd with hd | hd
  · left
    rw [eP, eR]
    exact (sub_of_same_branch_of_model M _ hM C D hPn hRn hP hR heq hsh hd).1
  · right
    rw [eP, eR]
    exact (add_of_opposite_branch_of_model M _ hM C D hPn hRn hP hR heq hsh hd).1

include hcard hp2 hkill hM hp D hbad in
/-- [DkMath.Lib] 特異核側の正確な零成分逆像。
商像が滑らかなら、源点自身が滑らかか、同じ核の点を一つ引くと滑らかになる。
奇素数核の深さ、水準一致、および二方向の枝比較を同じ実点で接続する。
標的の臨界中心の存在だけはこの定理の入力である。 -/
theorem singular_kernel_smooth_iff_translate_with_target_centre
    (T : CriticalCentre A (kernelModel E H)) (P : Points E) :
    HasSmoothReduction (valuationKernelModel E H p hkill A M hM hp)
      (oddKernelPointMap E H (hcard ▸ (Fact.out : p.Prime).odd_of_ne_two hp2) P) ↔
      ∃ Q : H, HasSmoothReduction M (P - Q.val) := by
  let ho : Odd (Nat.card H) := hcard ▸ (Fact.out : p.Prime).odd_of_ne_two hp2
  constructor
  · intro himage
    by_cases hP : HasSmoothReduction M P
    · exact ⟨0, by simpa using hP⟩
    by_cases hPH : P ∈ H
    · refine ⟨⟨P, hPH⟩, ?_⟩
      change HasSmoothReduction M (P - P)
      rw [sub_self]
      exact hasSmoothReduction_zero M _
    have hdeep := singular_kernel_half_deep E H p hp2 hkill A M hM hp C D hbad
    obtain ⟨Q, hQ, hlev⟩ := singular_smooth_implies_kernel_level E H A C ho P hPH
      p hkill M hM hp T hbad hP hdeep himage
    have hP0 : P ≠ 0 := fun hz => hPH (hz ▸ H.zero_mem)
    have hQ0 : Q.val ≠ 0 := fun hz => ((mem_halfKernel E H Q).mp hQ).1 (Subtype.ext hz)
    have hPX := (nonsmooth_coordinates_congr E A M hM C P hP).1
    have hQX := (nonsmooth_coordinates_congr E A M hM C Q.val (hbad Q hQ0)).1
    have hsh := singular_kernel_shallow E H p hp2 hkill A M hM hp C D hbad Q hQ0
    rw [← hlev] at hsh
    rcases same_level_sub_or_add_smooth E A M hM C D P Q.val hP0 hQ0 hPX hQX hlev hsh with hs | hs
    · exact ⟨Q, hs⟩
    · exact ⟨-Q, by simpa only [AddSubgroup.coe_neg, sub_neg_eq_add] using hs⟩
  · rintro ⟨Q, hQ⟩
    exact singular_target_smooth_of_kernel_translate E H A C ho P p hkill M hM hp hbad Q hQ

include hcard hp2 hkill hM hp D hbad in
/-- [DkMath.Lib] 特異核側の同じ商標的に臨界中心を構成する。
源の中心と二方向から節点 Frame を作り、同じ剰余モデルの一致から標的の
判別式非単元性と c₄ 単元性を供給する。標的曲線を別途選び直さない。 -/
theorem exists_singular_kernel_criticalCentre : Nonempty (CriticalCentre A (kernelModel E H)) := by
  let ho : Odd (Nat.card H) := hcard ▸ (Fact.out : p.Prime).odd_of_ne_two hp2
  let U := valuationKernelModel E H p hkill A M hM hp
  have hU : U.map A.subtype = kernelModel E H := valuationKernelModel_map E H p hkill A M hM hp ho
  obtain ⟨F, hsep⟩ := WeierstrassNodalFrame.residue_frame_of_model A M _ hM C D
  have hi := kernelModel_nodal_conditions E H hcard hp2 hkill A M hM hp (Or.inr hbad) F hsep
  apply EllipticCriticalCentre.exists_criticalCentre A (kernelModel E H)
  · rw [← hU, map_a₁]; exact U.a₁.property
  · rw [← hU, map_a₂]; exact U.a₂.property
  · rw [← hU, map_a₃]; exact U.a₃.property
  · rw [← hU, map_a₄]; exact U.a₄.property
  · rw [← hU, map_a₆]; exact U.a₆.property
  · exact kernelModel_discriminant_ne_zero_of_odd_card E H ho
  · exact hi.1
  · exact hi.2

include hcard hp2 hkill hM hp D hbad in
/-- [DkMath.Lib] 特異な奇素数核の同じ商写像による零成分の逆像は、源の零成分と H の和。
源中心・分離した二方向を保持し、標的中心・核点の浅さ・水準一致・枝比較を内部で供給する。
剰余点群の全射性やスキーム isogeny を仮定しない。 -/
theorem singular_kernel_smooth_iff_translate (P : Points E) :
    HasSmoothReduction (valuationKernelModel E H p hkill A M hM hp)
      (oddKernelPointMap E H (hcard ▸ (Fact.out : p.Prime).odd_of_ne_two hp2) P) ↔
      ∃ Q : H, HasSmoothReduction M (P - Q.val) := by
  obtain ⟨T⟩ := exists_singular_kernel_criticalCentre E H p hcard hp2 hkill A M hM hp C D hbad
  exact singular_kernel_smooth_iff_translate_with_target_centre E H p hcard hp2 hkill A M hM hp C D hbad T P

include hcard hp2 hkill hM hp D hbad in
/-- [DkMath.Lib] 特異核側の同じ零成分制限は全射である。
全点群の全射性で標的零成分点を持ち上げ、逆像判定で核点を引いて源の零成分へ移す。 -/
theorem singularKernelZeroComponentHom_surjective :
    Function.Surjective (singularKernelZeroComponentHom E H A M hM C p hkill hp
      (hcard ▸ (Fact.out : p.Prime).odd_of_ne_two hp2) hbad) := by
  let ho : Odd (Nat.card H) := hcard ▸ (Fact.out : p.Prime).odd_of_ne_two hp2
  let := kernelModel_isElliptic_of_odd_card E H ho
  let U := valuationKernelModel E H p hkill A M hM hp
  let hU := valuationKernelModel_map E H p hkill A M hM hp ho
  intro R
  obtain ⟨P, hP⟩ := oddKernelPointHom_surjective E H ho (pointEquivOfModelEq hU R.val)
  have ht : HasSmoothReduction U (oddKernelPointMap E H ho P) := by
    rw [show oddKernelPointMap E H ho P = pointEquivOfModelEq hU R.val from hP]
    apply (smooth_pointEquiv_of_model A U _ hU _).mp
    rw [model_equiv_symm hU, AddEquiv.symm_apply_apply]
    exact R.property
  obtain ⟨Q, hQ⟩ := (singular_kernel_smooth_iff_translate E H p hcard hp2 hkill A M hM hp C D hbad P).mp ht
  let P₀ : zeroComponentSubgroup M := ⟨pointEquivOfModelEq hM.symm (P - Q.val),
    (smooth_pointEquiv_of_model A M _ hM (P - Q.val)).mpr hQ⟩
  refine ⟨P₀, ?_⟩
  apply Subtype.ext
  apply (pointEquivOfModelEq hU).injective
  rw [singularKernelZeroComponentHom_geometric]
  have he : pointEquivOfModelEq hM P₀.val = P - Q.val := by
    change pointEquivOfModelEq hM (pointEquivOfModelEq hM.symm (P - Q.val)) = _
    rw [model_equiv_symm hM]
    exact (pointEquivOfModelEq hM).apply_symm_apply (P - Q.val)
  rw [he, map_sub, show oddKernelPointHom E H ho Q.val = 0 from kernelPointMap_of_mem E H Q.val Q.property,
    sub_zero]
  exact hP

include hcard hp2 hkill hM hp D hbad in
/-- [DkMath.Lib] 特異核側では、同じ源の零成分と同じ標的の零成分は加法同型。
既存の制限準同型の単射性と、上で証明した全射性から構成する。 -/
noncomputable def singularZeroComponentEquiv : zeroComponentSubgroup M ≃+
    zeroComponentSubgroup (valuationKernelModel E H p hkill A M hM hp) :=
  AddEquiv.ofBijective (singularKernelZeroComponentHom E H A M hM C p hkill hp
    (hcard ▸ (Fact.out : p.Prime).odd_of_ne_two hp2) hbad)
    ⟨singularKernelZeroComponentHom_injective E H A M hM C p hkill hp _ hbad,
      singularKernelZeroComponentHom_surjective E H p hcard hp2 hkill A M hM hp C D hbad⟩

include hcard hp2 hkill hM hp D hbad in
/-- [DkMath.Lib] 同じモデル上の部分群として、特異核側の標的零成分の逆像は源零成分と H の和に等しい。 -/
theorem singular_zeroComponent_comap_eq_sup_kernel :
    (zeroComponentSubgroup (valuationKernelModel E H p hkill A M hM hp)).comap
      (modelKernelPointHom E H p hkill A M hM hp (hcard ▸ (Fact.out : p.Prime).odd_of_ne_two hp2)) =
      zeroComponentSubgroup M ⊔ modelKernelSubgroup E H A M hM :=
  (singular_zeroComponent_surjective_iff_comap_eq E H p hkill A M hM hp
    (hcard ▸ (Fact.out : p.Prime).odd_of_ne_two hp2) C hbad).mp
    (singularKernelZeroComponentHom_surjective E H p hcard hp2 hkill A M hM hp C D hbad)

include hcard hp2 hkill hM hp D hbad in
/-- [DkMath.Lib] 特異核側では、標的零成分の実際の還元像を源から実現でき、
標的の還元核も源の還元核から同じ商写像で持ち上がる。
これは実際の零成分点の還元像に関する結論で、剰余点全体の持上げとは区別する。 -/
theorem singular_zeroComponent_reduction_and_kernel_lift :
    (∀ R, ∃ P, zeroComponentReduction M P = singularTargetReduction E H p hkill A M hM hp hbad R) ∧
    (∀ R, singularTargetReduction E H p hkill A M hM hp hbad R = 0 →
      ∃ P, zeroComponentReduction M P = 0 ∧
        singularKernelZeroComponentHom E H A M hM C p hkill hp
          (hcard ▸ (Fact.out : p.Prime).odd_of_ne_two hp2) hbad P = R) :=
  (singular_zeroComponent_surjective_iff_reduction_and_kernel E H p hkill A M hM hp
    (hcard ▸ (Fact.out : p.Prime).odd_of_ne_two hp2) C hbad).mp
      (singularKernelZeroComponentHom_surjective E H p hcard hp2 hkill A M hM hp C D hbad)

end DkMath.Lib.NumberTheory.EllipticFiniteKernel
