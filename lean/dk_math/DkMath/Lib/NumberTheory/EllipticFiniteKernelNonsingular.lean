/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.EllipticFiniteKernelTwoTorsion

#print "file: DkMath.Lib.NumberTheory.EllipticFiniteKernelNonsingular"

/-!
# 奇数核の標的モデルの非特異性を閉じる

[DkMath.Lib] 元の楕円曲線の2捩れ三次式から三つの実際の非零反転固定点を作る。
奇数核では全て核の外にあり、同じX_Hによる像は互いに異なる。
前回の三根判定へ入力を内部供給し、同じkernelModelのΔ≠0を証明する。
従って同じ全点関数は標的楕円性の外部入力なしで使える。加法性は別の命題である。
-/
namespace DkMath.Lib.NumberTheory.EllipticFiniteKernel
open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open EllipticFunctionField EllipticTorsionRepresentation
variable {K : Type*} [Field K] [CharZero K] (E : WeierstrassCurve K) [E.IsElliptic]
noncomputable local instance : DecidableEq (AlgebraicClosure K) := Classical.decEq _

/-- [DkMath.Lib] 同じ曲線に三つの実際の相異なる非零反転固定点を構成する。
抽象的な三根や仮想的な別群で置換せず、同じPoints Eへ入れる。 -/
theorem exists_three_nonzero_fixed_points :
    ∃ P : Fin 3 → Points E, (∀ i, P i ≠ 0) ∧ (∀ i, -P i = P i) ∧ Function.Injective P := by
  let k := AlgebraicClosure K
  let W := E⁄k
  let : W.IsElliptic := by
    change (E.map (algebraMap K k)).IsElliptic
    infer_instance
  have ha : W.twoTorsionPolynomial.a ≠ 0 := by change (4 : k) ≠ 0; norm_num
  have hd : W.twoTorsionPolynomial.discr ≠ 0 := by
    rw [twoTorsionPolynomial_discr]
    exact mul_ne_zero (by norm_num) W.Δ'.ne_zero
  have hs : (W.twoTorsionPolynomial.toPoly.map (RingHom.id k)).Splits := IsAlgClosed.splits _
  obtain ⟨r₁, r₂, r₃, hr⟩ := (Cubic.splits_iff_roots_eq_three ha).mp hs
  obtain ⟨h₁₂, h₁₃, h₂₃⟩ := (Cubic.discr_ne_zero_iff_roots_ne ha hr).mp hd
  let r : Fin 3 → k := ![r₁, r₂, r₃]
  have hinj : Function.Injective r := by
    intro i j he
    fin_cases i <;> fin_cases j <;> simp_all [r]
  have hroots : W.twoTorsionPolynomial.toPoly.roots = {r₁, r₂, r₃} := by
    simpa only [Cubic.map_roots, Polynomial.map_id] using hr
  have hv : ∀ i, W.twoTorsionPolynomial.toPoly.IsRoot (r i) := by
    intro i
    apply (Polynomial.mem_roots (Cubic.ne_zero_of_a_ne_zero ha)).mp
    rw [hroots]
    fin_cases i <;> simp [r]
  have hex (i : Fin 3) : ∃ y, ∃ h : W.toAffine.Nonsingular (r i) y,
      (Point.some (r i) y h : W.toAffine.Point) + Point.some (r i) y h = 0 :=
    (Point.isRoot_twoTorsionPolynomial_iff (W := W.toAffine) ⟨by norm_num⟩ W.Δ'.ne_zero (r i)).mp (hv i)
  choose y hy hsum using hex
  let P : Fin 3 → Points E := fun i => Point.some (r i) (y i) (hy i)
  refine ⟨P, fun i => Point.some_ne_zero _, ?_, ?_⟩
  · intro i
    have hi : P i + P i = 0 := hsum i
    exact neg_eq_of_add_eq_zero_left hi
  · intro i j he
    apply hinj
    exact congrArg Point.xc he

/-- [DkMath.Lib] 奇数位数の同じ有限核では、構成した標的モデルの判別式は非零。
三点の存在・核外条件・三値の分離は全て内部供給する。 -/
theorem kernelModel_discriminant_ne_zero_of_odd_card
    (H : AddSubgroup (Points E)) [Fintype H] (hodd : Odd (Nat.card H)) :
    (kernelModel E H).Δ ≠ 0 := by
  obtain ⟨P, hP0, hn, hinj⟩ := exists_three_nonzero_fixed_points E
  have hout (i : Fin 3) : P i ∉ H := fun hi =>
    hP0 i (eq_zero_of_mem_odd_kernel_fixed E H hodd _ hi (hn i))
  apply kernelModel_discriminant_of_twoTorsion_separation E H P hout hn
  intro i j he
  apply hinj
  exact kernelXAt_injective_on_twoTorsion E H hodd (P i) (P j)
    (hn i) (hn j) (hout i) (hout j) he

/-- [DkMath.Lib] 奇数核の同じ標的にIsEllipticを実際に供給する。 -/
theorem kernelModel_isElliptic_of_odd_card
    (H : AddSubgroup (Points E)) [Fintype H] (hodd : Odd (Nat.card H)) :
    (kernelModel E H).IsElliptic :=
  ⟨isUnit_iff_ne_zero.mpr (kernelModel_discriminant_ne_zero_of_odd_card E H hodd)⟩

/-- [DkMath.Lib] 同じ安定奇数核のK係数モデルも楕円曲線である。
前回の係数降下の等式と判別式の基底変換を実際に使う。 -/
theorem descendedKernelModel_isElliptic_of_odd_card
    (H : AddSubgroup (Points E)) [Fintype H] (hodd : Odd (Nat.card H))
    (hH : ∀ σ P, P ∈ H → pointAction E σ P ∈ H) :
    (descendedKernelModel E H hH).IsElliptic := by
  refine ⟨isUnit_iff_ne_zero.mpr ?_⟩
  intro hz
  have h := congrArg WeierstrassCurve.Δ (descendedKernelModel_map E H hH)
  rw [WeierstrassCurve.map_Δ, hz, map_zero] at h
  exact kernelModel_discriminant_ne_zero_of_odd_card E H hodd h.symm

/-- [DkMath.Lib] 標的楕円性のproviderを要求しない、同じ奇数核の全点関数。 -/
noncomputable def oddKernelPointMap
    (H : AddSubgroup (Points E)) [Fintype H] (hodd : Odd (Nat.card H)) :
    Points E → (kernelModel E H).toAffine.Point := by
  let := kernelModel_isElliptic_of_odd_card E H hodd
  exact kernelPointMap E H

/-- [DkMath.Lib] 同じ奇数核の全点関数の零ファイバーは、外部楕円性入力なしにHと一致。 -/
theorem oddKernelPointMap_eq_zero_iff
    (H : AddSubgroup (Points E)) [Fintype H] (hodd : Odd (Nat.card H)) (P : Points E) :
    oddKernelPointMap E H hodd P = 0 ↔ P ∈ H := by
  let := kernelModel_isElliptic_of_odd_card E H hodd
  exact kernelPointMap_eq_zero_iff E H P

/-- [DkMath.Lib] 同じ奇数核の全点関数はHの平行移動で不変。加法性とは区別する。 -/
theorem oddKernelPointMap_translation
    (H : AddSubgroup (Points E)) [Fintype H] (hodd : Odd (Nat.card H)) (P : Points E) (Q : H) :
    oddKernelPointMap E H hodd (P + Q.val) = oddKernelPointMap E H hodd P := by
  let := kernelModel_isElliptic_of_odd_card E H hodd
  exact kernelPointMap_translation E H P Q

end DkMath.Lib.NumberTheory.EllipticFiniteKernel
