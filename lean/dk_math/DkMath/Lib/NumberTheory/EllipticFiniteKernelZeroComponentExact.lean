/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.EllipticFiniteKernelNodalInverse
import DkMath.Lib.NumberTheory.EllipticFiniteKernelReductionSquare

#print "file: DkMath.Lib.NumberTheory.EllipticFiniteKernelZeroComponentExact"

/-!
# 零成分の像、逆像と有限核

[DkMath.Lib] 全点準同型の全射性を零成分の逆像判定と組み合わせる。
点群の零成分の商同型は剰余曲線の点群の商や剰余点の持上げとは異なる。
特異核側では逆像の等式と零成分の像の等式を群論で結び、その条件を明示する。
-/
namespace DkMath.Lib.NumberTheory
namespace AdditiveSubgroupExact
variable {G B : Type*} [AddCommGroup G] [AddCommGroup B]

/-- [DkMath.Lib] 全点準同型の全射性の下では、部分群の像が標的部分群に等しいことと、
標的部分群の逆像が源部分群と同じ核の和に等しいことが同値である。 -/
theorem map_eq_iff_comap_eq_sup_ker (f : G →+ B) (S : AddSubgroup G) (T : AddSubgroup B)
    (hf : Function.Surjective f) : S.map f = T ↔ T.comap f = S ⊔ f.ker := by
  constructor
  · intro h
    rw [← h, AddSubgroup.comap_map_eq]
  · intro h
    have hm := congrArg (fun U : AddSubgroup G => U.map f) h
    rw [AddSubgroup.map_comap_eq_self_of_surjective hf] at hm
    have he : (S ⊔ f.ker).map f = S.map f := by
      rw [AddSubgroup.map_sup]
      simp
    exact (hm.trans he).symm

/-- [DkMath.Lib] 源部分群が標的部分群へ送られるなら、源部分群と核の和は
標的部分群の逆像に含まれる。この方向には全射性は要らない。 -/
theorem sup_ker_le_comap (f : G →+ B) (S : AddSubgroup G) (T : AddSubgroup B)
    (h : S.map f ≤ T) : S ⊔ f.ker ≤ T.comap f := by
  exact sup_le (AddSubgroup.map_le_iff_le_comap.mp h) (AddSubgroup.ker_le_comap f T)

/-- [DkMath.Lib] 部分群間の準同型が元の準同型の制限であるとき、制限の全射性と
源部分群の像が標的部分群に等しいことは同値。 -/
theorem restricted_surjective_iff_map_eq (f : G →+ B) (S : AddSubgroup G) (T : AddSubgroup B)
    (g : S →+ T) (hg : ∀ x : S, (g x).val = f x.val) :
    Function.Surjective g ↔ S.map f = T := by
  constructor
  · intro h
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact hg ⟨x, hx⟩ ▸ (g ⟨x, hx⟩).property
    · intro y hy
      obtain ⟨x, hx⟩ := h ⟨y, hy⟩
      exact ⟨x.val, x.property, (hg x).symm.trans (congrArg Subtype.val hx)⟩
  · intro h y
    have hy : y.val ∈ S.map f := h.symm ▸ y.property
    obtain ⟨x, hx, he⟩ := hy
    exact ⟨⟨x, hx⟩, Subtype.ext ((hg ⟨x, hx⟩).trans he)⟩

/-- [DkMath.Lib] 可換な還元図式で制限準同型が全射であることは、標的の各還元像を
源から実現でき、さらに標的の還元核の各点を源の還元核から持ち上げられることと同値。
前者は剰余点の像、後者は無限遠近傍の持上げという別々の要件である。 -/
theorem surjective_iff_reduction_and_kernel {R : Type*} [AddCommGroup R]
    (f : G →+ B) (rG : G →+ R) (rB : B →+ R)
    (hc : ∀ x, rB (f x) = rG x) :
    Function.Surjective f ↔
      (∀ y, ∃ x, rG x = rB y) ∧
      (∀ y, rB y = 0 → ∃ x, rG x = 0 ∧ f x = y) := by
  constructor
  · intro hf
    constructor
    · intro y
      obtain ⟨x, rfl⟩ := hf y
      exact ⟨x, (hc x).symm⟩
    · intro y hy
      obtain ⟨x, hx⟩ := hf y
      exact ⟨x, (hc x).symm.trans (hx ▸ hy), hx⟩
  · rintro ⟨hred, hker⟩ y
    obtain ⟨x, hx⟩ := hred y
    have hz : rB (y - f x) = 0 := by
      rw [map_sub, hc x, hx, sub_self]
    obtain ⟨z, _, hz⟩ := hker (y - f x) hz
    refine ⟨z + x, ?_⟩
    rw [map_add, hz, sub_add_cancel]

end AdditiveSubgroupExact
end DkMath.Lib.NumberTheory

namespace DkMath.Lib.NumberTheory.EllipticFiniteKernel
open WeierstrassCurve WeierstrassCurve.Affine IsLocalRing
open EllipticTorsionRepresentation EllipticGoodReductionSeparation EllipticSmoothReduction
open EllipticCriticalCentre EllipticNodalTorsion.NodalTorsion WeierstrassVariableChange
noncomputable local instance {α : Type*} : DecidableEq α := Classical.decEq _
private theorem symm_model_equiv {L : Type*} [Field L] {W V : WeierstrassCurve L} (h : W = V) :
    pointEquivOfModelEq h.symm = (pointEquivOfModelEq h).symm := by subst V; rfl

variable {K : Type*} [Field K] [CharZero K] (E : WeierstrassCurve K) [E.IsElliptic]
  (H : AddSubgroup (Points E)) [Fintype H] (p : ℕ) [Fact p.Prime]
  (hcard : Nat.card H = p) (hp2 : p ≠ 2) (hkill : ∀ Q : H, p • Q.val = 0)
  (A : ValuationSubring (AlgebraicClosure K)) (M : WeierstrassCurve A)
  (hM : M.map A.subtype = E.map (algebraMap K (AlgebraicClosure K)))
  (hp : A.valuation (p : AlgebraicClosure K) = 1)
  (hs : ∀ Q : H, HasSmoothReduction M Q.val)
  (C : CriticalCentre A (E.map (algebraMap K (AlgebraicClosure K))))
  {x₀ y₀ α : ResidueField A} (F : Frame (M.map (residue A)) x₀ y₀ α)
  (hsep : α ≠ -(M.map (residue A)).a₁ - α) (hCx : residue A ⟨C.x, C.x_mem⟩ = x₀)

include C hCx in
/-- [DkMath.Lib] 滑らかな核側の零成分制限は全射。標的零成分点を全点準同型で持ち上げ、
零成分逆像の同値でその持上げが源の零成分に属すると分かる。剰余点の持上げとは別である。 -/
theorem nodalZeroComponentHom_surjective :
    Function.Surjective (nodalZeroComponentHom E H p hcard hp2 hkill A M hM hp hs F hsep) := by
  let ho : Odd (Nat.card H) := hcard ▸ (Fact.out : p.Prime).odd_of_ne_two hp2
  let U := valuationKernelModel E H p hkill A M hM hp
  let hU := valuationKernelModel_map E H p hkill A M hM hp ho
  intro R
  obtain ⟨P, hP⟩ := oddKernelPointHom_surjective E H ho (pointEquivOfModelEq hU R.val)
  have ht : HasSmoothReduction U (oddKernelPointMap E H ho P) := by
    rw [show oddKernelPointMap E H ho P = pointEquivOfModelEq hU R.val from hP]
    apply (smooth_pointEquiv_of_model A U _ hU _).mp
    rw [symm_model_equiv hU, AddEquiv.symm_apply_apply]
    exact R.property
  have hsP := (oddKernelPointMap_smooth_iff E H p hcard hp2 hkill A M hM hp hs C F hsep hCx P).mp ht
  let P₀ : zeroComponentSubgroup M := ⟨pointEquivOfModelEq hM.symm P,
    (smooth_pointEquiv_of_model A M _ hM P).mpr hsP⟩
  refine ⟨P₀, ?_⟩
  apply Subtype.ext
  apply (pointEquivOfModelEq hU).injective
  change pointEquivOfModelEq hU (pointEquivOfModelEq hU.symm
    (oddKernelPointHom E H ho (pointEquivOfModelEq hM P₀.val))) = _
  rw [symm_model_equiv hU, AddEquiv.apply_symm_apply]
  change oddKernelPointHom E H ho (pointEquivOfModelEq hM (pointEquivOfModelEq hM.symm P)) = _
  have he : pointEquivOfModelEq hM (pointEquivOfModelEq hM.symm P) = P := by
    rw [symm_model_equiv hM]
    exact (pointEquivOfModelEq hM).apply_symm_apply P
  exact (congrArg (oddKernelPointHom E H ho) he).trans hP

/-- [DkMath.Lib] 源零成分内での H。点を同じ源モデルから一般ファイバーへ輸送し、
元の有限核との所属を記録する。 -/
noncomputable def zeroComponentKernel : AddSubgroup (zeroComponentSubgroup M) :=
  H.comap ((pointEquivOfModelEq hM).toAddMonoidHom.comp (zeroComponentSubgroup M).subtype)

include hs in
/-- [DkMath.Lib] 元の H の各点を、同じ源モデルの零成分内の核に輸送する。
滑らかな核の仮定は、各点が零成分の実際の元となるために使用する。 -/
noncomputable def kernelToZeroComponentKernel : H →+ zeroComponentKernel E H A M hM where
  toFun Q := ⟨⟨kernelIntegralPointHom E H A M hM Q,
    (smooth_pointEquiv_of_model A M _ hM Q.val).mpr (hs Q)⟩, by
      change pointEquivOfModelEq hM (pointEquivOfModelEq hM.symm Q.val) ∈ H
      have he : pointEquivOfModelEq hM (pointEquivOfModelEq hM.symm Q.val) = Q.val := by
        rw [symm_model_equiv hM]
        exact (pointEquivOfModelEq hM).apply_symm_apply Q.val
      exact he.symm ▸ Q.property⟩
  map_zero' := Subtype.ext (Subtype.ext (map_zero (kernelIntegralPointHom E H A M hM)))
  map_add' Q R := Subtype.ext (Subtype.ext (map_add (kernelIntegralPointHom E H A M hM) Q R))

include hs in
/-- [DkMath.Lib] 零成分内の核は、元の幾何学的有限核 H と加法同型である。
したがって零成分の商は、別の核ではなく元の H による商である。 -/
noncomputable def kernelEquivZeroComponentKernel : H ≃+ zeroComponentKernel E H A M hM :=
  AddEquiv.ofBijective (kernelToZeroComponentKernel E H A M hM hs) ⟨by
    intro Q R h
    apply Subtype.ext
    apply (pointEquivOfModelEq hM.symm).injective
    exact congrArg (fun x : zeroComponentKernel E H A M hM => x.val.val) h, by
    intro P
    let Q : H := ⟨pointEquivOfModelEq hM P.val.val, P.property⟩
    refine ⟨Q, Subtype.ext (Subtype.ext ?_)⟩
    change pointEquivOfModelEq hM.symm (pointEquivOfModelEq hM P.val.val) = P.val.val
    rw [symm_model_equiv hM, AddEquiv.symm_apply_apply]⟩

/-- [DkMath.Lib] 零成分制限の核は、同じ有限核を源零成分内に表示した部分群に等しい。 -/
theorem nodalZeroComponentHom_ker :
    (nodalZeroComponentHom E H p hcard hp2 hkill A M hM hp hs F hsep).ker =
      zeroComponentKernel E H A M hM := by
  ext P
  exact nodalZeroComponentHom_eq_zero_iff E H p hcard hp2 hkill A M hM hp hs F hsep P

include C hCx in
/-- [DkMath.Lib] 滑らかな核側の幾何学的零成分は、同じ H による商として標的零成分と加法同型。
これは代数閉包上の点群の同型であり、剰余点群の全射性やスキーム商を主張しない。 -/
noncomputable def nodalZeroComponentQuotientEquiv :
    (zeroComponentSubgroup M ⧸ zeroComponentKernel E H A M hM) ≃+
      zeroComponentSubgroup (valuationKernelModel E H p hkill A M hM hp) :=
  (QuotientAddGroup.quotientAddEquivOfEq
    (nodalZeroComponentHom_ker E H p hcard hp2 hkill A M hM hp hs F hsep).symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective _
      (nodalZeroComponentHom_surjective E H p hcard hp2 hkill A M hM hp hs C F hsep hCx))

/-- [DkMath.Lib] 商同型の代表の値は、既存の同じ零成分制限準同型の値である。 -/
theorem nodalZeroComponentQuotientEquiv_mk (P : zeroComponentSubgroup M) :
    nodalZeroComponentQuotientEquiv E H p hcard hp2 hkill A M hM hp hs C F hsep hCx
      (QuotientAddGroup.mk P) = nodalZeroComponentHom E H p hcard hp2 hkill A M hM hp hs F hsep P := rfl

end DkMath.Lib.NumberTheory.EllipticFiniteKernel

namespace DkMath.Lib.NumberTheory.EllipticFiniteKernel
open WeierstrassCurve WeierstrassCurve.Affine
open EllipticTorsionRepresentation EllipticGoodReductionSeparation EllipticSmoothReduction
open EllipticCriticalCentre WeierstrassVariableChange
open WeierstrassModelReduction IsLocalRing
noncomputable local instance {α : Type*} : DecidableEq α := Classical.decEq _
variable {K : Type*} [Field K] [CharZero K] (E : WeierstrassCurve K) [E.IsElliptic]
  (H : AddSubgroup (Points E)) [Fintype H] (n : ℕ) (hkill : ∀ Q : H, n • Q.val = 0)
  (A : ValuationSubring (AlgebraicClosure K)) (M : WeierstrassCurve A)
  (hM : M.map A.subtype = E.map (algebraMap K (AlgebraicClosure K)))
  (hn : A.valuation (n : AlgebraicClosure K) = 1) (ho : Odd (Nat.card H))

/-- [DkMath.Lib] 同じ全点商準同型を、指定された源・標的の付値環モデルの
一般ファイバー間へ輸送した準同型。 -/
noncomputable def modelKernelPointHom : (M.map A.subtype).toAffine.Point →+
    ((valuationKernelModel E H n hkill A M hM hn).map A.subtype).toAffine.Point :=
  (pointEquivOfModelEq (valuationKernelModel_map E H n hkill A M hM hn ho).symm).toAddMonoidHom.comp
    ((oddKernelPointHom E H ho).comp (pointEquivOfModelEq hM).toAddMonoidHom)

/-- [DkMath.Lib] モデルの同型による前後の輸送は、同じ全点準同型の全射性を保つ。 -/
theorem modelKernelPointHom_surjective :
    Function.Surjective (modelKernelPointHom E H n hkill A M hM hn ho) := by
  intro R
  let hU := valuationKernelModel_map E H n hkill A M hM hn ho
  obtain ⟨P, hP⟩ := oddKernelPointHom_surjective E H ho (pointEquivOfModelEq hU R)
  refine ⟨pointEquivOfModelEq hM.symm P, ?_⟩
  change pointEquivOfModelEq hU.symm (oddKernelPointHom E H ho
    (pointEquivOfModelEq hM (pointEquivOfModelEq hM.symm P))) = R
  have he : pointEquivOfModelEq hM (pointEquivOfModelEq hM.symm P) = P := by
    rw [symm_model_equiv hM]
    exact (pointEquivOfModelEq hM).apply_symm_apply P
  rw [he, hP, symm_model_equiv hU, AddEquiv.symm_apply_apply]

/-- [DkMath.Lib] 同じ H を源モデルの一般ファイバー上で表示した部分群。 -/
noncomputable def modelKernelSubgroup : AddSubgroup (M.map A.subtype).toAffine.Point :=
  H.comap (pointEquivOfModelEq hM).toAddMonoidHom

/-- [DkMath.Lib] モデルに輸送しても、全点準同型の核は同じ H の逆像である。 -/
theorem modelKernelPointHom_ker : (modelKernelPointHom E H n hkill A M hM hn ho).ker =
    modelKernelSubgroup E H A M hM := by
  ext P
  change pointEquivOfModelEq (valuationKernelModel_map E H n hkill A M hM hn ho).symm
    (oddKernelPointHom E H ho (pointEquivOfModelEq hM P)) = 0 ↔ pointEquivOfModelEq hM P ∈ H
  constructor
  · intro hh
    have hz : oddKernelPointHom E H ho (pointEquivOfModelEq hM P) = 0 := by
      apply (pointEquivOfModelEq (valuationKernelModel_map E H n hkill A M hM hn ho).symm).injective
      exact hh.trans (map_zero _).symm
    have hm : pointEquivOfModelEq hM P ∈ (oddKernelPointHom E H ho).ker := hz
    rwa [oddKernelPointHom_ker E H ho] at hm
  · intro hm
    have hk : pointEquivOfModelEq hM P ∈ (oddKernelPointHom E H ho).ker := by
      rwa [oddKernelPointHom_ker E H ho]
    change oddKernelPointHom E H ho (pointEquivOfModelEq hM P) = 0 at hk
    rw [hk, map_zero]

variable (C : CriticalCentre A (E.map (algebraMap K (AlgebraicClosure K))))
  (hbad : ∀ Q : H, Q.val ≠ 0 → ¬ HasSmoothReduction M Q.val)

include C hbad in
/-- [DkMath.Lib] 特異核側でも、源の零成分と同じ H の和は標的零成分の逆像に入る。
全点商準同型の核と、既存の前向き零成分輸送だけを使う。 -/
theorem singular_zeroComponent_sup_kernel_le_comap :
    zeroComponentSubgroup M ⊔ modelKernelSubgroup E H A M hM ≤
      (zeroComponentSubgroup (valuationKernelModel E H n hkill A M hM hn)).comap
        (modelKernelPointHom E H n hkill A M hM hn ho) := by
  rw [← modelKernelPointHom_ker E H n hkill A M hM hn ho]
  apply AdditiveSubgroupExact.sup_ker_le_comap
  rintro _ ⟨P, hP, rfl⟩
  exact (singularKernelZeroComponentHom E H A M hM C n hkill hn ho hbad ⟨P, hP⟩).property

/-- [DkMath.Lib] 特異核側の零成分逆像が E₀+H に一致することは、
同じ零成分制限準同型が全射であることと同値。全点群上の全射性を使用する。
この定理は制限自体の全射性を仮定も結論もしていない。 -/
theorem singular_zeroComponent_surjective_iff_comap_eq :
    Function.Surjective (singularKernelZeroComponentHom E H A M hM C n hkill hn ho hbad) ↔
      (zeroComponentSubgroup (valuationKernelModel E H n hkill A M hM hn)).comap
        (modelKernelPointHom E H n hkill A M hM hn ho) =
      zeroComponentSubgroup M ⊔ modelKernelSubgroup E H A M hM := by
  have hg (P : zeroComponentSubgroup M) :
      (singularKernelZeroComponentHom E H A M hM C n hkill hn ho hbad P).val =
        modelKernelPointHom E H n hkill A M hM hn ho P.val := rfl
  rw [AdditiveSubgroupExact.restricted_surjective_iff_map_eq _ _ _ _ hg]
  rw [AdditiveSubgroupExact.map_eq_iff_comap_eq_sup_ker _ _ _
    (modelKernelPointHom_surjective E H n hkill A M hM hn ho),
    modelKernelPointHom_ker E H n hkill A M hM hn ho]

/-- [DkMath.Lib] 特異核側で標的零成分の還元を、同一の源剰余モデルへ輸送する。
既存の剰余モデル等式により、二つの還元準同型が同じ終域を持つ。 -/
noncomputable def singularTargetReduction :
    zeroComponentSubgroup (valuationKernelModel E H n hkill A M hM hn) →+
      (M.map (residue A)).toAffine.Point :=
  (pointEquivOfModelEq (valuationKernelModel_residue_eq_of_not_smooth E H n hkill A M hM hn hbad)).toAddMonoidHom.comp
    (zeroComponentReduction (valuationKernelModel E H n hkill A M hM hn))

/-- [DkMath.Lib] 特異核側の実際の零成分制限は、同じ剰余モデル上で還元と可換である。
標的剰余モデルの等式輸送と源モデルの一般ファイバーへの等式輸送を明示する。 -/
theorem singular_zeroComponent_reduction_commutes (P : zeroComponentSubgroup M) :
    singularTargetReduction E H n hkill A M hM hn hbad
      (singularKernelZeroComponentHom E H A M hM C n hkill hn ho hbad P) =
      zeroComponentReduction M P := by
  let hU := valuationKernelModel_map E H n hkill A M hM hn ho
  let T := pointEquivOfModelEq hM P.val
  have ht : HasSmoothReduction M T := by
    apply (smooth_pointEquiv_of_model A M _ hM T).mp
    rw [symm_model_equiv hM, AddEquiv.symm_apply_apply]
    exact P.property
  have hh := oddKernelPointMap_reduction_square E H n hkill A M hM hn C ho hbad T ht
  change pointEquivOfModelEq _ (reducePointSmooth _ (pointEquivOfModelEq hU.symm
    (oddKernelPointHom E H ho T))) = reducePointSmooth M (pointEquivOfModelEq hM.symm T) at hh
  rw [symm_model_equiv hM, AddEquiv.symm_apply_apply] at hh
  exact hh

/-- [DkMath.Lib] 特異核側の零成分制限が全射であることを、同じ剰余モデルでの
還元像の実現と、標的還元核の源還元核からの持上げに分解する。
この二条件の成立はここでは主張しない。 -/
theorem singular_zeroComponent_surjective_iff_reduction_and_kernel :
    Function.Surjective (singularKernelZeroComponentHom E H A M hM C n hkill hn ho hbad) ↔
      (∀ R, ∃ P, zeroComponentReduction M P = singularTargetReduction E H n hkill A M hM hn hbad R) ∧
      (∀ R, singularTargetReduction E H n hkill A M hM hn hbad R = 0 →
        ∃ P, zeroComponentReduction M P = 0 ∧
          singularKernelZeroComponentHom E H A M hM C n hkill hn ho hbad P = R) :=
  AdditiveSubgroupExact.surjective_iff_reduction_and_kernel _ _ _
    (singular_zeroComponent_reduction_commutes E H n hkill A M hM hn ho C hbad)

end DkMath.Lib.NumberTheory.EllipticFiniteKernel
