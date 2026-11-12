/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.EllipticTorsionDimensionCriteria

#print "file: DkMath.Lib.NumberTheory.EllipticTwoTorsionRank"

/-!
# 指数2では、三次多項式の判別式から実際の次元2まで閉じる

2-torsionの有限座標点は自己反転するので、根ごとのファイバーは2点ではなく1点である。
ΨSq₂は4X³+b₂X²+2b₄X+b₆で、その三次判別式は16Δとなる。
標数0の楕円曲線ではこれは非零であり、代数閉包上で相異なる根がちょうど3個ある。
座標同値と非特異性から各根は実際の一点を与え、無限遠点と合わせて|E[2]|=4となる。
この幾何学的計算の後に有限F₂空間の濃度公式へ戻し、次元2を得る。
一般の奇素数の根の下界や、Frey表現の既約性へ拡張したとは主張しない。
-/
namespace DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
open WeierstrassCurve Polynomial
open scoped WeierstrassCurve.Affine
variable {K : Type*} [Field K] [CharZero K] (E : WeierstrassCurve K) [E.IsElliptic]

/-- 二倍零の点は自己反転するので、根の上のファイバーはちょうど一点となる。 -/
theorem affineXFiber_ncard_eq_one_at_two {x : AlgebraicClosure K}
    (hx : ((E.baseChange (AlgebraicClosure K)).ΨSq 2).IsRoot x) :
    (affineXFiber E x).ncard = 1 := by
  classical
  obtain ⟨P, hPx, _⟩ := exists_torsion_over_root E 2 hx
  have hself : P.val = -P.val := by
    apply eq_neg_iff_add_eq_zero.mpr
    have hk : 2 • P.val = 0 := P.property
    simpa only [two_nsmul] using hk
  have he : affineXFiber E x = {P.val} := by
    ext Q
    change Q.xRep = ![x, 1] ↔ Q = P.val
    rw [← hPx]
    have hh : Q.xRep = P.val.xRep ↔ Q = P.val ∨ Q = -P.val := Affine.Point.xRep_eq_xRep_iff
    simpa only [← hself, or_self] using hh
  rw [he, Set.ncard_singleton]

/-- 楕円曲線の判別式が非零なので、2-torsionの三次式は相異なる根をちょうど3個持つ。 -/
theorem divisionRootCount_two : divisionRootCount E 2 = 3 := by
  classical
  let W := E.baseChange (AlgebraicClosure K)
  have : W.IsElliptic := by
    change (E.map (algebraMap K (AlgebraicClosure K))).IsElliptic
    infer_instance
  have hd : W.twoTorsionPolynomial.discr ≠ 0 :=
    W.twoTorsionPolynomial_discr_ne_zero_of_isElliptic (isUnit_iff_ne_zero.mpr (by norm_num))
  have hc := Cubic.card_roots_of_discr_ne_zero (P := W.twoTorsionPolynomial)
    (φ := RingHom.id (AlgebraicClosure K))
    (by change (4 : AlgebraicClosure K) ≠ 0; norm_num)
    (by rw [Polynomial.map_id]; exact IsAlgClosed.splits _) hd
  simpa only [divisionRootCount, divisionRoots, Nat.cast_ofNat, WeierstrassCurve.ΨSq_two,
    WeierstrassCurve.Ψ₂Sq_eq, Cubic.map, RingHom.id_apply, Cubic.roots] using hc

/-- 各根の上の一点と無限遠点から、実際のE[2]は正確に4点である。 -/
theorem card_torsion_two : Nat.card (Torsion E 2) = 4 := by
  classical
  rw [card_torsion_eq_one_add_sum_fibers E 2 (by decide)]
  have hf : ∑ x ∈ divisionRoots E 2, (affineXFiber E x).ncard = divisionRootCount E 2 := by
    calc _ = ∑ _x ∈ divisionRoots E 2, 1 := Finset.sum_congr rfl (fun x hx =>
        affineXFiber_ncard_eq_one_at_two E ((mem_divisionRoots_iff E 2 (by decide) x).mp hx))
      _ = _ := by simp [divisionRootCount]
  rw [hf, divisionRootCount_two]

/-- 位数4を今回の幾何学から供給し、旧来の条件付き次元定理を使わずに次元2を得る。 -/
theorem finrank_torsion_two : Module.finrank (ZMod 2) (Torsion E 2) = 2 := by
  have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Torsion E 2)
  rw [card_torsion_two E, Nat.card_zmod] at hc
  exact (Nat.pow_right_injective (by decide : 2 ≤ 2) (by simpa only [Nat.reducePow] using hc)).symm

/-- 標準torsionBy表示にも同じ実際の次元2を運ぶ。 -/
theorem finrank_standardTorsion_two : Module.finrank (ZMod 2) (StandardTorsion E 2) = 2 := by
  rw [← (torsionByLinearEquiv E 2).finrank_eq]
  exact finrank_torsion_two E

/-- 指数2では、任意の非零点の張る直線の外に実際の第二の点が存在する。 -/
theorem exists_torsion_two_outside_span (P : Torsion E 2) (hP : P ≠ 0) :
    ∃ Q : Torsion E 2, Q ∉ Submodule.span (ZMod 2) ({P} : Set (Torsion E 2)) :=
  (finrank_torsion_eq_two_iff_exists_outside_span E 2 P hP).mp (finrank_torsion_two E)

end DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
