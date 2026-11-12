/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.EllipticTorsionFinite
import Mathlib.Data.Set.Card

#print "file: DkMath.Lib.NumberTheory.EllipticTorsionCardBound"

/-!
# 有限性から個数の上界へ: 根の数と座標ファイバーを数える

無限遠点以外のn-torsion点のx座標はΨSqₙの根である。異なる根は次数以下しかなく、
一つのx座標の上にはPと−Pの高々2点しかない。従って
  |E[n]| ≤ 1 + 2(n²−1)
となる。根の分離性や全ての根から点を復元することは要求しない。

無限遠点のxRepは[1,0]なので、有限座標のファイバーはxRep=[x,1]で切り出す。
xRepの第一成分だけを使うと、同じ値を持つ無限遠点を混ぜてしまう点に注意する。
P=−Pの場合にはファイバーは1点になり得るので、常に2点と数えてはならない。
有限性はNOTE-012の実際の点群の定理から供給し、今回はその有限集合を定量化する。
-/
namespace DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
open WeierstrassCurve Polynomial
open scoped WeierstrassCurve.Affine
variable {K : Type*} [Field K] (E : WeierstrassCurve K)

/-- 無限遠点を含めない、指定した有限x座標の上の実際の点の集合。 -/
def affineXFiber (x : AlgebraicClosure K) : Set (Points E) :=
  {P | P.xRep = ![x, 1]}

/-- 同じx座標の点はPと−Pに限られるので、このファイバーは有限である。 -/
theorem affineXFiber_finite (x : AlgebraicClosure K) : (affineXFiber E x).Finite :=
  (E.toAffine⁄(AlgebraicClosure K)).finite_preimage_xRep x

/-- 存在しないファイバー、自己逆の点、二つの点をまとめて「高々2点」と扱う。 -/
theorem affineXFiber_ncard_le_two (x : AlgebraicClosure K) : (affineXFiber E x).ncard ≤ 2 := by
  classical
  rcases Set.eq_empty_or_nonempty (affineXFiber E x) with he | ⟨Q, hQ⟩
  · rw [he]
    simp
  · have hQ' : Q.xRep = ![x, 1] := hQ
    have he : affineXFiber E x = {Q, -Q} := by
      ext P
      change P.xRep = ![x, 1] ↔ P = Q ∨ P = -Q
      rw [← hQ']
      exact Affine.Point.xRep_eq_xRep_iff
    rw [he]
    calc ({Q, -Q} : Set (Points E)).ncard ≤ ({-Q} : Set (Points E)).ncard + 1 :=
        Set.ncard_insert_le Q _
      _ = 2 := by simp

variable [CharZero K]

/-- 非零次数のn-torsionの個数の粗い上界。有限性・位数公式は外部の仮定にしない。 -/
theorem card_torsion_le_degree_bound (n : ℕ) (hn : n ≠ 0) :
    Nat.card (Torsion E n) ≤ 1 + 2 * (n ^ 2 - 1) := by
  classical
  have := finite_torsion_of_ne_zero E n hn
  let := Fintype.ofFinite (Torsion E n)
  let W := E.baseChange (AlgebraicClosure K)
  let q := W.ΨSq (n : ℤ)
  have hq : q ≠ 0 := W.ΨSq_ne_zero (by exact_mod_cast hn)
  let roots := q.roots.toFinset
  let fiber := fun x => (affineXFiber_finite E x).toFinset
  let cover := insert 0 (roots.biUnion fiber)
  let embedding : Torsion E n ↪ Points E := ⟨Subtype.val, Subtype.val_injective⟩
  have hcover : ∀ P : Torsion E n, P.val ∈ cover := by
    intro P
    rcases P with ⟨P, hP⟩
    cases P with
    | zero => exact Finset.mem_insert_self _ _
    | some x y h =>
      apply Finset.mem_insert_of_mem
      apply Finset.mem_biUnion.mpr
      refine ⟨x, ?_, ?_⟩
      · exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hq).mpr
          (torsion_some_coordinate_root E n h hP))
      · exact (affineXFiber_finite E x).mem_toFinset.mpr rfl
  have hincl : Finset.univ.map embedding ⊆ cover := by
    intro P hP
    obtain ⟨Q, _, rfl⟩ := Finset.mem_map.mp hP
    exact hcover Q
  have hrootcard : roots.card ≤ n ^ 2 - 1 := by
    calc roots.card ≤ q.roots.card := Multiset.toFinset_card_le _
      _ ≤ q.natDegree := Polynomial.card_roots' q
      _ ≤ n ^ 2 - 1 := by
        simpa only [Int.natAbs_natCast] using W.natDegree_ΨSq_le (n : ℤ)
  have hfibercard : ∀ x, (fiber x).card ≤ 2 := by
    intro x
    simpa only [fiber, ← Set.ncard_eq_toFinset_card] using affineXFiber_ncard_le_two E x
  calc Nat.card (Torsion E n) = (Finset.univ.map embedding).card := by
        simp only [Finset.card_map, Finset.card_univ, Nat.card_eq_fintype_card]
    _ ≤ cover.card := Finset.card_le_card hincl
    _ ≤ (roots.biUnion fiber).card + 1 := Finset.card_insert_le _ _
    _ ≤ (∑ x ∈ roots, (fiber x).card) + 1 := Nat.add_le_add_right Finset.card_biUnion_le 1
    _ ≤ roots.card * 2 + 1 := by
      apply Nat.add_le_add_right
      simpa only [Finset.sum_const, smul_eq_mul] using
        (Finset.sum_le_sum (fun x _ => hfibercard x))
    _ ≤ 1 + 2 * (n ^ 2 - 1) := by omega

end DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
