/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.EllipticFiniteKernelNonsingular
import DkMath.Lib.NumberTheory.EllipticStableLine

#print "file: DkMath.Lib.NumberTheory.EllipticFiniteKernelPointDescent"

/-!
# 同じ有限核の全点関数を元の体の曲線へ降ろす

[DkMath.Lib] 係数が降りることと、全点関数がGalois同変であることを結ぶ。
Hが集合として安定なら、Galois元は和の添字Hを置換する。この置換を
実際の特殊化値に適用し、Hの上の無限遠点も含めた同変性を証明する。

標的は既存のdescendedKernelModelそのものである。別の曲線や仮想的な点群を
導入せず、基底変換の等式による点の移送でoddKernelPointMapと同定する。
この関数の加法性は本ファイルの仮定にも結論にも含めない。
-/
namespace DkMath.Lib.NumberTheory.EllipticFiniteKernel
open WeierstrassCurve WeierstrassCurve.Affine
open EllipticTorsionRepresentation EllipticFunctionField
open DkMath.Lib.RepresentationTheory
open scoped BigOperators
noncomputable local instance instDecidableEqEllipticFiniteKernelPointDescent {k : Type*} : DecidableEq k := Classical.decEq _

/-- [DkMath.Lib] モデルの等式による実点群の移送。座標や加法を変更しない。 -/
noncomputable def pointModelEquiv {k : Type*} [Field k]
    {W V : WeierstrassCurve k} (h : W = V) : W.toAffine.Point ≃+ V.toAffine.Point := by
  classical
  subst V
  exact AddEquiv.refl _

/-- [DkMath.Lib] 等式による移送は有限点の二座標を保存する。 -/
theorem pointModelEquiv_some {k : Type*} [Field k]
    {W V : WeierstrassCurve k} (h : W = V) {x y : k} (hxy : W.toAffine.Nonsingular x y) :
    pointModelEquiv h (.some x y hxy) = .some x y (h ▸ hxy) := by
  subst V
  rfl

variable {K : Type*} [Field K] [CharZero K] (E : WeierstrassCurve K) [E.IsElliptic]

omit [CharZero K] [E.IsElliptic] in
/-- [DkMath.Lib] 安定核への所属はGalois作用の前後で同値。逆元の安定性も使用する。 -/
theorem pointAction_mem_kernel_iff (H : AddSubgroup (Points E))
    (hH : ∀ σ P, P ∈ H → pointAction E σ P ∈ H)
    (σ : Field.absoluteGaloisGroup K) (P : Points E) :
    pointAction E σ P ∈ H ↔ P ∈ H := by
  constructor
  · intro h
    have hi := hH σ⁻¹ _ h
    rwa [← pointAction_mul, inv_mul_cancel, pointAction_one] at hi
  · exact hH σ P

omit [CharZero K] in
/-- [DkMath.Lib] 特殊化した同じX_HはGalois作用と可換。
有限和の添字の置換なので、核の各点が有理である必要はない。 -/
theorem kernelXAt_galois (H : AddSubgroup (Points E)) [Fintype H]
    (hH : ∀ σ P, P ∈ H → pointAction E σ P ∈ H)
    (σ : Field.absoluteGaloisGroup K) (P : Points E) (hP : P ∉ H) :
    kernelXAt E H (pointAction E σ P)
        (fun h => hP ((pointAction_mem_kernel_iff E H hH σ P).mp h)) =
      σ.toAlgHom (kernelXAt E H P hP) := by
  rw [kernelXAt_eq_sum, kernelXAt_eq_sum, map_sub, kernel_sum_xc_galois E H hH, map_sum]
  congr 1
  symm
  apply Fintype.sum_equiv (kernelGaloisEquiv E H hH σ)
  intro Q
  have ha := congrArg Point.xc ((pointAction E σ).map_add P Q.val)
  exact (point_xc_map σ.toAlgHom (P + Q.val)).symm.trans ha

omit [CharZero K] in
/-- [DkMath.Lib] 特殊化した同じY_Hも同じ添字の置換でGalois同変となる。 -/
theorem kernelYAt_galois (H : AddSubgroup (Points E)) [Fintype H]
    (hH : ∀ σ P, P ∈ H → pointAction E σ P ∈ H)
    (σ : Field.absoluteGaloisGroup K) (P : Points E) (hP : P ∉ H) :
    kernelYAt E H (pointAction E σ P)
        (fun h => hP ((pointAction_mem_kernel_iff E H hH σ P).mp h)) =
      σ.toAlgHom (kernelYAt E H P hP) := by
  rw [kernelYAt_eq_sum, kernelYAt_eq_sum, map_sub, kernel_sum_yc_galois E H hH, map_sum]
  congr 1
  symm
  apply Fintype.sum_equiv (kernelGaloisEquiv E H hH σ)
  intro Q
  have ha := congrArg Point.yc ((pointAction E σ).map_add P Q.val)
  exact (point_yc_map σ.toAlgHom (P + Q.val)).symm.trans ha

/-- [DkMath.Lib] 同じ奇数核の全点関数は反転を保存する。
核上のOも含めて証明するが、任意の二点の加法性はこれからは従わない。 -/
theorem oddKernelPointMap_neg (H : AddSubgroup (Points E)) [Fintype H]
    (hodd : Odd (Nat.card H)) (P : Points E) :
    oddKernelPointMap E H hodd (-P) = -oddKernelPointMap E H hodd P := by
  let := kernelModel_isElliptic_of_odd_card E H hodd
  change kernelPointMap E H (-P) = -kernelPointMap E H P
  by_cases hP : P ∈ H
  · rw [kernelPointMap_of_mem E H (-P) (H.neg_mem hP), kernelPointMap_of_mem E H P hP, neg_zero]
  · have hPn : -P ∉ H := fun hm => hP (H.neg_mem_iff.mp hm)
    rw [kernelPointMap_of_not_mem E H (-P) hPn, kernelPointMap_of_not_mem E H P hP, Point.neg_some]
    congr 1
    · exact kernelXAt_neg E H P hP
    · simpa only [negY, kernelModel_a₁, kernelModel_a₃] using kernelYAt_neg E H P hP

/-- [DkMath.Lib] 同じ奇数安定核のK係数標的上の全点関数。
既存の全点関数を、既存のモデル降下の等式だけで移送する。 -/
noncomputable def descendedKernelPointMap (H : AddSubgroup (Points E)) [Fintype H]
    (hodd : Odd (Nat.card H)) (hH : ∀ σ P, P ∈ H → pointAction E σ P ∈ H) :
    Points E → Points (descendedKernelModel E H hH) := fun P =>
  (pointModelEquiv (descendedKernelModel_map E H hH)).symm (oddKernelPointMap E H hodd P)

/-- [DkMath.Lib] 移送を戻すと、同じ全点関数そのものである。 -/
theorem descendedKernelPointMap_transport (H : AddSubgroup (Points E)) [Fintype H]
    (hodd : Odd (Nat.card H)) (hH : ∀ σ P, P ∈ H → pointAction E σ P ∈ H)
    (P : Points E) :
    pointModelEquiv (descendedKernelModel_map E H hH)
      (descendedKernelPointMap E H hodd hH P) = oddKernelPointMap E H hodd P :=
  (pointModelEquiv (descendedKernelModel_map E H hH)).apply_symm_apply _

/-- [DkMath.Lib] 同じ核の外では、降下した全点関数も同じ有限座標を持つ。 -/
theorem descendedKernelPointMap_of_not_mem (H : AddSubgroup (Points E)) [Fintype H]
    (hodd : Odd (Nat.card H)) (hH : ∀ σ P, P ∈ H → pointAction E σ P ∈ H)
    (P : Points E) (hP : P ∉ H) :
    ∃ hxy, descendedKernelPointMap E H hodd hH P =
      .some (kernelXAt E H P hP) (kernelYAt E H P hP) hxy := by
  let := kernelModel_isElliptic_of_odd_card E H hodd
  have hn := kernelAt_nonsingular E H P hP
  have he := descendedKernelModel_map E H hH
  have hxy : ((descendedKernelModel E H hH).map
      (algebraMap K (AlgebraicClosure K))).toAffine.Nonsingular
        (kernelXAt E H P hP) (kernelYAt E H P hP) := he.symm ▸ hn
  refine ⟨hxy, ?_⟩
  apply (pointModelEquiv he).injective
  exact (descendedKernelPointMap_transport E H hodd hH P).trans
    ((kernelPointMap_of_not_mem E H P hP).trans (pointModelEquiv_some he hxy).symm)

/-- [DkMath.Lib] K係数標的へ移した全点関数の零ファイバーも正確にH。 -/
theorem descendedKernelPointMap_eq_zero_iff (H : AddSubgroup (Points E)) [Fintype H]
    (hodd : Odd (Nat.card H)) (hH : ∀ σ P, P ∈ H → pointAction E σ P ∈ H)
    (P : Points E) : descendedKernelPointMap E H hodd hH P = 0 ↔ P ∈ H := by
  let e := pointModelEquiv (descendedKernelModel_map E H hH)
  have hz : e (0 : ((descendedKernelModel E H hH).map
      (algebraMap K (AlgebraicClosure K))).toAffine.Point) = 0 := e.map_zero
  rw [← oddKernelPointMap_eq_zero_iff E H hodd P]
  constructor
  · intro h
    exact (descendedKernelPointMap_transport E H hodd hH P).symm.trans
      ((congrArg e h).trans hz)
  · intro h
    apply e.injective
    exact (descendedKernelPointMap_transport E H hodd hH P).trans (h.trans hz.symm)

/-- [DkMath.Lib] 同じK係数標的上でもHの平行移動不変性を保つ。 -/
theorem descendedKernelPointMap_translation (H : AddSubgroup (Points E)) [Fintype H]
    (hodd : Odd (Nat.card H)) (hH : ∀ σ P, P ∈ H → pointAction E σ P ∈ H)
    (P : Points E) (Q : H) :
    descendedKernelPointMap E H hodd hH (P + Q.val) = descendedKernelPointMap E H hodd hH P := by
  exact congrArg (pointModelEquiv (descendedKernelModel_map E H hH)).symm
    (oddKernelPointMap_translation E H hodd P Q)

/-- [DkMath.Lib] 降下後の同じ全点関数も反転を保存する。 -/
theorem descendedKernelPointMap_neg (H : AddSubgroup (Points E)) [Fintype H]
    (hodd : Odd (Nat.card H)) (hH : ∀ σ P, P ∈ H → pointAction E σ P ∈ H)
    (P : Points E) :
    descendedKernelPointMap E H hodd hH (-P) = -descendedKernelPointMap E H hodd hH P := by
  have he := congrArg (pointModelEquiv (descendedKernelModel_map E H hH)).symm
    (oddKernelPointMap_neg E H hodd P)
  exact he.trans ((pointModelEquiv (descendedKernelModel_map E H hH)).symm.map_neg _)

/-- [DkMath.Lib] 同じ全点関数のGalois同変性。核上のOと核外の有限点の両方を扱う。
群準同型性を仮定せず、標準の実点Galois作用との可換図式を閉じる。 -/
theorem descendedKernelPointMap_equivariant (H : AddSubgroup (Points E)) [Fintype H]
    (hodd : Odd (Nat.card H)) (hH : ∀ σ P, P ∈ H → pointAction E σ P ∈ H)
    (σ : Field.absoluteGaloisGroup K) (P : Points E) :
    descendedKernelPointMap E H hodd hH (pointAction E σ P) =
      pointAction (descendedKernelModel E H hH) σ (descendedKernelPointMap E H hodd hH P) := by
  by_cases hP : P ∈ H
  · have hz := (descendedKernelPointMap_eq_zero_iff E H hodd hH P).mpr hP
    have hzσ := (descendedKernelPointMap_eq_zero_iff E H hodd hH _).mpr (hH σ P hP)
    rw [hzσ, hz, map_zero]
  · have hPσ : pointAction E σ P ∉ H := fun h =>
      hP ((pointAction_mem_kernel_iff E H hH σ P).mp h)
    obtain ⟨hn, he⟩ := descendedKernelPointMap_of_not_mem E H hodd hH P hP
    obtain ⟨hnσ, heσ⟩ := descendedKernelPointMap_of_not_mem E H hodd hH _ hPσ
    rw [heσ, he]
    change Point.some _ _ _ = Point.some _ _ _
    congr 1
    · exact kernelXAt_galois E H hH σ P hP
    · exact kernelYAt_galois E H hH σ P hP

/-- [DkMath.Lib] 個々の点が固定されなくても、そのH剰余類が固定なら像はK有理点。
同変性とH軌道不変性を合わせた降下であり、加法性やtorsionの保存は使わない。
零かどうかは同じHへの所属と同値なので、核外の点は非零有理点へ降りる。 -/
theorem exists_rational_image_of_fixed_coset (H : AddSubgroup (Points E)) [Fintype H]
    (hodd : Odd (Nat.card H)) (hH : ∀ σ P, P ∈ H → pointAction E σ P ∈ H)
    (P : Points E) (hP : ∀ σ, ∃ Q : H, pointAction E σ P = P + Q.val) :
    ∃ R : (descendedKernelModel E H hH).toAffine.Point,
      baseChangePoint (descendedKernelModel E H hH) R = descendedKernelPointMap E H hodd hH P ∧
      (R = 0 ↔ P ∈ H) := by
  have hf (σ : Field.absoluteGaloisGroup K) :
      pointAction (descendedKernelModel E H hH) σ (descendedKernelPointMap E H hodd hH P) =
        descendedKernelPointMap E H hodd hH P := by
    obtain ⟨Q, hQ⟩ := hP σ
    exact (descendedKernelPointMap_equivariant E H hodd hH σ P).symm.trans
      ((congrArg (descendedKernelPointMap E H hodd hH) hQ).trans
        (descendedKernelPointMap_translation E H hodd hH P Q))
  obtain ⟨R, hR⟩ := exists_baseChangePoint_of_fixed (descendedKernelModel E H hH) _ hf
  refine ⟨R, hR, ?_⟩
  rw [← descendedKernelPointMap_eq_zero_iff E H hodd hH P, ← hR]
  constructor
  · intro h; subst R; rfl
  · intro h
    exact baseChangePoint_injective (descendedKernelModel E H hH) h

omit [CharZero K] [E.IsElliptic] in
/-- [DkMath.Lib] 部分空間の同じ実点像への所属を、元のtorsion部分空間へ戻す。
torsion包含の単射性を使い、別の核との同一視を要求しない。 -/
theorem torsion_mem_pointSubgroup_iff (p : ℕ) [Fact p.Prime]
    (L : Submodule (ZMod p) (Torsion E p)) (P : Torsion E p) :
    P.val ∈ pointSubgroup E p L ↔ P ∈ L := by
  constructor
  · rintro ⟨Q, hQ, he⟩
    have hQP : Q = P := Subtype.ext he
    exact hQP ▸ hQ
  · intro hP
    exact ⟨P, hP, rfl⟩

/-- [DkMath.Lib] Cofixed条件から、同じ商座標の実際のK有理像を構成する。
像の非零性はP∉Lと同値。像がp捩れであるという追加結論は、加法性の証明を待つ。
有限核・モデル・点の対応・同変性を外部providerにせず、既存の構成をそのまま使う。 -/
theorem exists_rational_image_of_cofixed (p : ℕ) [Fact p.Prime]
    (L : Submodule (ZMod p) (Torsion E p)) [Fintype (pointSubgroup E p L)]
    (hodd : Odd (Nat.card (pointSubgroup E p L)))
    (hL : IsCofixedOn (representation E p) L) (P : Torsion E p) :
    ∃ R : (descendedKernelModel E (pointSubgroup E p L)
        (pointSubgroup_stable E p L hL.isStable)).toAffine.Point,
      baseChangePoint _ R = descendedKernelPointMap E (pointSubgroup E p L) hodd
        (pointSubgroup_stable E p L hL.isStable) P.val ∧ (R = 0 ↔ P ∈ L) := by
  have hcoset (σ : Field.absoluteGaloisGroup K) :
      ∃ Q : pointSubgroup E p L, pointAction E σ P.val = P.val + Q.val := by
    let D : Torsion E p := representation E p σ P - P
    have hD : D.val ∈ pointSubgroup E p L := ⟨D, hL σ P, rfl⟩
    refine ⟨⟨D.val, hD⟩, ?_⟩
    change pointAction E σ P.val = P.val + (pointAction E σ P.val - P.val)
    abel
  obtain ⟨R, he, hz⟩ := exists_rational_image_of_fixed_coset E (pointSubgroup E p L)
    hodd (pointSubgroup_stable E p L hL.isStable) P.val hcoset
  exact ⟨R, he, hz.trans (torsion_mem_pointSubgroup_iff E p L P)⟩

end DkMath.Lib.NumberTheory.EllipticFiniteKernel
