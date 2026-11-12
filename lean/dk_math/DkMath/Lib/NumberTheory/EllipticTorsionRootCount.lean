/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.EllipticTorsionNontrivial

#print "file: DkMath.Lib.NumberTheory.EllipticTorsionRootCount"

/-!
# 根の重複度を捨て、実際のtorsion点を座標ファイバーで数える

ΨSqₙの多重度込みの根の数と、相異なる根の数は区別する。
NOTE-014の座標同値により、実際のE[n]は無限遠点と各根の上の有限ファイバーへ分割される。
異なるxのファイバーは交わらず、無限遠点も有限ファイバーには入らない。
従って点数は1にファイバーの点数の和を加えたものである。

楕円曲線性があれば各根を非特異点へ持ち上げられる。奇数nでは非零n-torsionは
自己反転できないので、一つの根にPと−Pのちょうど2点が対応する。
これで |E[n]|=1+2r が得られる。ただしrは相異なる根の数であり、
多項式の次数との等号や、一般の奇素数でのrの下界はこの定理に含めない。
-/
namespace DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
open WeierstrassCurve Polynomial
open scoped WeierstrassCurve.Affine
variable {K : Type*} [Field K] (E : WeierstrassCurve K)

/-- ΨSqₙの相異なる根。toFinsetで多重度を捨てたことを明示する。 -/
noncomputable def divisionRoots (n : ℕ) : Finset (AlgebraicClosure K) := by
  classical
  exact ((E.baseChange (AlgebraicClosure K)).ΨSq (n : ℤ)).roots.toFinset

/-- 相異なる根の個数。多重度込みのroots.cardや次数とは別の量である。 -/
noncomputable def divisionRootCount (n : ℕ) : ℕ := (divisionRoots E n).card

/-- 有限xファイバーに無限遠点を混ぜない。xRepの第二成分で区別する。 -/
theorem zero_not_mem_affineXFiber (x : AlgebraicClosure K) : (0 : Points E) ∉ affineXFiber E x := by
  intro h
  have he := congrFun h 1
  change (0 : AlgebraicClosure K) = 1 at he
  exact zero_ne_one he

variable [CharZero K]

/-- 非零指数ではΨSqが非零なので、有限根集合への所属とIsRootが一致する。 -/
theorem mem_divisionRoots_iff (n : ℕ) (hn : n ≠ 0) (x : AlgebraicClosure K) :
    x ∈ divisionRoots E n ↔ ((E.baseChange (AlgebraicClosure K)).ΨSq (n : ℤ)).IsRoot x := by
  classical
  exact Multiset.mem_toFinset.trans (Polynomial.mem_roots
    ((E.baseChange (AlgebraicClosure K)).ΨSq_ne_zero (by exact_mod_cast hn)))

/-- 根の上にある実際の有限座標点は、同じ群のn倍写像の核に入る。 -/
theorem affineXFiber_killed (n : ℕ) {x : AlgebraicClosure K}
    (hx : ((E.baseChange (AlgebraicClosure K)).ΨSq (n : ℤ)).IsRoot x)
    {P : Points E} (hP : P ∈ affineXFiber E x) : n • P = 0 := by
  classical
  cases P with
  | zero => exact False.elim (zero_not_mem_affineXFiber E x hP)
  | some x' y h =>
    have he : x' = x := congrFun hP 0
    subst x'
    exact (torsion_some_iff_coordinate_root E n h).mpr hx

/-- 有限根集合と実際の有限座標ファイバーによる、重複のない正確な点数分割。
楕円曲線性を要求しないので、特異点の上の空ファイバーもそのまま0点として数える。 -/
theorem card_torsion_eq_one_add_sum_fibers (n : ℕ) (hn : n ≠ 0) :
    Nat.card (Torsion E n) = 1 + ∑ x ∈ divisionRoots E n, (affineXFiber E x).ncard := by
  classical
  let fiber := fun x => (affineXFiber_finite E x).toFinset
  let cover := insert 0 ((divisionRoots E n).biUnion fiber)
  have hiff : ∀ P : Points E, n • P = 0 ↔ P ∈ cover := by
    intro P
    constructor
    · intro hP
      cases P with
      | zero => exact Finset.mem_insert_self _ _
      | some x y h =>
        apply Finset.mem_insert_of_mem
        apply Finset.mem_biUnion.mpr
        exact ⟨x, (mem_divisionRoots_iff E n hn x).mpr (torsion_some_coordinate_root E n h hP),
          (affineXFiber_finite E x).mem_toFinset.mpr rfl⟩
    · intro hP
      rcases Finset.mem_insert.mp hP with rfl | hP
      · exact nsmul_zero _
      · obtain ⟨x, hx, hPx⟩ := Finset.mem_biUnion.mp hP
        exact affineXFiber_killed E n ((mem_divisionRoots_iff E n hn x).mp hx)
          ((affineXFiber_finite E x).mem_toFinset.mp hPx)
  have hzero : (0 : Points E) ∉ (divisionRoots E n).biUnion fiber := by
    intro h
    obtain ⟨x, _, hx⟩ := Finset.mem_biUnion.mp h
    exact zero_not_mem_affineXFiber E x ((affineXFiber_finite E x).mem_toFinset.mp hx)
  have hdisj : (↑(divisionRoots E n) : Set (AlgebraicClosure K)).PairwiseDisjoint fiber := by
    intro x _ y _ hxy
    apply Finset.disjoint_left.mpr
    intro P hPx hPy
    have hx := (affineXFiber_finite E x).mem_toFinset.mp hPx
    have hy := (affineXFiber_finite E y).mem_toFinset.mp hPy
    have he := congrFun (hx.symm.trans hy) 0
    exact hxy he
  change Nat.card {P : Points E // n • P = 0} = _
  rw [Nat.card_congr (Equiv.subtypeEquivRight hiff)]
  change (cover : Set (Points E)).ncard = _
  rw [Set.ncard_coe_finset]
  dsimp only [cover]
  rw [Finset.card_insert_of_notMem hzero, Finset.card_biUnion hdisj]
  simp only [fiber, ← Set.ncard_eq_toFinset_card]
  omega

omit [CharZero K] in
/-- 非零の奇数torsion点は自己反転しない。奇数倍と二倍で零なら元の点も零となる。 -/
theorem torsion_ne_neg_of_odd {n : ℕ} (hn : Odd n) (P : Torsion E n) (hP : P ≠ 0) :
    P.val ≠ -P.val := by
  intro he
  let Q : Points E := P.val
  have htwo : 2 • Q = 0 := by rw [two_nsmul]; exact eq_neg_iff_add_eq_zero.mp he
  have hkill : n • Q = 0 := P.property
  obtain ⟨k, hk⟩ := hn
  rw [hk, add_nsmul, one_nsmul, mul_nsmul, htwo,
    nsmul_zero, zero_add] at hkill
  exact hP (Subtype.ext hkill)

variable [E.IsElliptic]

/-- 根の上に実際の非零torsion点を取る。相異なる根ごとの非空性を供給する。 -/
theorem exists_torsion_over_root (n : ℕ) {x : AlgebraicClosure K}
    (hx : ((E.baseChange (AlgebraicClosure K)).ΨSq (n : ℤ)).IsRoot x) :
    ∃ P : Torsion E n, P.val ∈ affineXFiber E x ∧ P ≠ 0 := by
  classical
  obtain ⟨y, hy⟩ := exists_affine_equation_y E x
  have : (E.baseChange (AlgebraicClosure K)).IsElliptic := by
    change (E.map (algebraMap K (AlgebraicClosure K))).IsElliptic
    infer_instance
  have hns := Affine.equation_iff_nonsingular.mp hy
  refine ⟨⟨Affine.Point.some x y hns, (torsion_some_iff_coordinate_root E n hns).mpr hx⟩,
    rfl, ?_⟩
  intro he
  exact Affine.Point.some_ne_zero hns (congrArg Subtype.val he)

/-- 奇数指数では各根の上のPと−Pは異なる二点であり、ファイバーはちょうど2点。 -/
theorem affineXFiber_ncard_eq_two_of_odd {n : ℕ} (hn : Odd n) {x : AlgebraicClosure K}
    (hx : ((E.baseChange (AlgebraicClosure K)).ΨSq (n : ℤ)).IsRoot x) :
    (affineXFiber E x).ncard = 2 := by
  classical
  obtain ⟨P, hPx, hP⟩ := exists_torsion_over_root E n hx
  have he : affineXFiber E x = {P.val, -P.val} := by
    ext Q
    change Q.xRep = ![x, 1] ↔ Q = P.val ∨ Q = -P.val
    rw [← hPx]
    exact Affine.Point.xRep_eq_xRep_iff
  rw [he, Set.ncard_pair (torsion_ne_neg_of_odd E hn P hP)]

/-- 奇数指数の実際の点数は、相異なる除法多項式の根の数rを使って1+2rとなる。 -/
theorem card_torsion_eq_one_add_twice_roots {n : ℕ} (hn : Odd n) :
    Nat.card (Torsion E n) = 1 + 2 * divisionRootCount E n := by
  classical
  have hn0 : n ≠ 0 := by intro h; subst n; simp at hn
  rw [card_torsion_eq_one_add_sum_fibers E n hn0]
  have hf : ∑ x ∈ divisionRoots E n, (affineXFiber E x).ncard =
      (divisionRoots E n).card * 2 := by
    calc _ = ∑ _x ∈ divisionRoots E n, 2 := Finset.sum_congr rfl (fun x hx =>
        affineXFiber_ncard_eq_two_of_odd E hn ((mem_divisionRoots_iff E n hn0 x).mp hx))
      _ = _ := by simp
  rw [hf, divisionRootCount]
  omega

end DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
