/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.EllipticTorsionDimensionBound

#print "file: DkMath.Lib.NumberTheory.EllipticTorsionNontrivial"

/-!
# 楕円曲線性から実際の非零torsion点を作る

NOTE-013は非特異点群一般について次元0・1・2を候補として残した。
ここでは楕円曲線性を追加し、除法多項式の根から実際の非零点を構成する。
n>1なら標数0でΨSqₙの次数はn²−1>0であり、代数閉包に根xが存在する。
曲線方程式はyについてモニック二次式なのでyも取れる。楕円曲線性により
この座標点は非特異である。ψₙ(P)²=ΨSqₙ(x)=0からψₙ(P)=0を得て、
NOTE-012の実際の倍写像との同値を逆向きに使えば[n]P=Oとなる。
有限座標の点は無限遠点ではないので、この点は零点ではない。

素数pでは有限性と非零点から1≤dim(E[p])≤2、位数の候補p・p²を得る。
根の重複度や分離性は使わず、根を一つだけ取る。このため次元1の排除には届かない。
標数0は座標体の仮定であり、残余空間の係数体Fₚの標数とは区別する。
-/
namespace DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
open WeierstrassCurve Polynomial
open scoped WeierstrassCurve.Affine
variable {K : Type*} [Field K] (E : WeierstrassCurve K)

/-- 任意の有限x座標に対して、代数閉包上で曲線方程式を満たすyが存在する。
これは座標の存在だけであり、楕円曲線性を与えるまでは非特異性を主張しない。 -/
theorem exists_affine_equation_y (x : AlgebraicClosure K) :
    ∃ y, (E.toAffine⁄(AlgebraicClosure K)).Equation x y := by
  let W := E.baseChange (AlgebraicClosure K)
  let q := W.toAffine.polynomial.map (Polynomial.evalRingHom x)
  have hd : q.degree = 2 := by
    dsimp only [q]
    rw [Affine.monic_polynomial.degree_map, Affine.degree_polynomial]
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_root q (by rw [hd]; decide)
  refine ⟨y, ?_⟩
  change q.eval y = 0 at hy
  change W.toAffine.polynomial.evalEval x y = 0
  simpa only [q, Polynomial.eval_map, Polynomial.eval₂_evalRingHom] using hy

variable [CharZero K]

/-- 非特異な有限座標点では、n倍零とΨSqₙの根であることが同値である。
逆向きではψの平方零からψの零を取り出し、実際の群の倍写像へ戻す。 -/
theorem torsion_some_iff_coordinate_root (n : ℕ) {x y : AlgebraicClosure K}
    (h : (E.toAffine⁄(AlgebraicClosure K)).Nonsingular x y) :
    (nsmulAddMonoidHom n : Points E →+ Points E) (Affine.Point.some x y h) = 0 ↔
      ((E.baseChange (AlgebraicClosure K)).ΨSq (n : ℤ)).IsRoot x := by
  classical
  refine ⟨torsion_some_coordinate_root E n h, ?_⟩
  intro hx
  have hs := EllipticDivision.WeierstrassCurve.evalEval_ψ_sq
    (E.baseChange (AlgebraicClosure K)) h.1 (n : ℤ)
  have hψ : ((E.baseChange (AlgebraicClosure K)).ψ (n : ℤ)).evalEval x y = 0 := by
    exact eq_zero_of_pow_eq_zero (hs.trans hx)
  have hz := (EllipticDivision.WeierstrassCurve.smul_eq_zero_iff_evalEval_ψ
    (E.baseChange (AlgebraicClosure K)) h (n : ℤ)).mpr hψ
  rw [natCast_zsmul] at hz
  exact hz

variable [E.IsElliptic]

/-- n>1なら、除法多項式の根を非特異点へ持ち上げて非零n-torsionを得る。
素数性や位数公式は不要。n=1を含めると零点だけなので、この条件を保持する。 -/
theorem exists_nonzero_torsion_of_one_lt (n : ℕ) (hn : 1 < n) :
    ∃ P : Torsion E n, P ≠ 0 := by
  classical
  let W := E.baseChange (AlgebraicClosure K)
  have hd : 0 < (W.ΨSq (n : ℤ)).natDegree :=
    W.natDegree_ΨSq_pos (by simpa only [Int.natAbs_natCast] using hn)
      (by exact_mod_cast (by omega : n ≠ 0))
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root (W.ΨSq (n : ℤ)) (by
    exact ne_of_gt (Polynomial.natDegree_pos_iff_degree_pos.mp hd))
  obtain ⟨y, hy⟩ := exists_affine_equation_y E x
  have : W.IsElliptic := by
    change (E.map (algebraMap K (AlgebraicClosure K))).IsElliptic
    infer_instance
  have hns : W.toAffine.Nonsingular x y := Affine.equation_iff_nonsingular.mp hy
  let P : Torsion E n := ⟨Affine.Point.some x y hns,
    (torsion_some_iff_coordinate_root E n hns).mpr hx⟩
  refine ⟨P, ?_⟩
  intro hP
  exact Affine.Point.some_ne_zero hns (congrArg Subtype.val hP)

/-- 非零点の存在を、標準のNontrivial命題として公開する。 -/
theorem torsion_nontrivial_of_one_lt (n : ℕ) (hn : 1 < n) : Nontrivial (Torsion E n) := by
  obtain ⟨P, hP⟩ := exists_nonzero_torsion_of_one_lt E n hn
  exact ⟨⟨P, 0, hP⟩⟩

variable (p : ℕ) [Fact p.Prime]

/-- 標数0の楕円曲線の素数torsionには、実際の異なる二点がある。 -/
instance torsionNontrivial : Nontrivial (Torsion E p) :=
  torsion_nontrivial_of_one_lt E p (Fact.out : p.Prime).one_lt

/-- 有限性はNOTE-012、非零性は今回の幾何学から供給して次元の正値性を得る。 -/
theorem finrank_torsion_pos : 0 < Module.finrank (ZMod p) (Torsion E p) :=
  Module.finrank_pos

/-- NOTE-013の上界と合わせ、楕円曲線では次元の候補0を排除する。 -/
theorem finrank_torsion_bounds :
    1 ≤ Module.finrank (ZMod p) (Torsion E p) ∧
      Module.finrank (ZMod p) (Torsion E p) ≤ 2 :=
  ⟨finrank_torsion_pos E p, finrank_torsion_le_two E p⟩

/-- 楕円曲線のp-torsionの次元は1または2。次元1の排除は別の幾何学である。 -/
theorem finrank_torsion_one_or_two :
    Module.finrank (ZMod p) (Torsion E p) = 1 ∨
      Module.finrank (ZMod p) (Torsion E p) = 2 := by
  have h := finrank_torsion_bounds E p
  omega

/-- 濃度公式から、位数の候補もpまたはp²へ限定される。 -/
theorem card_torsion_prime_or_prime_sq :
    Nat.card (Torsion E p) = p ∨ Nat.card (Torsion E p) = p ^ 2 := by
  have hc := Module.natCard_eq_pow_finrank (K := ZMod p) (V := Torsion E p)
  rw [Nat.card_zmod] at hc
  rcases finrank_torsion_one_or_two E p with h | h
  · left; simpa only [h, pow_one] using hc
  · right; simpa only [h] using hc

/-- 少なくともp点、多くともp²点。p²点の存在を証明したとは読まない。 -/
theorem card_torsion_bounds : p ≤ Nat.card (Torsion E p) ∧ Nat.card (Torsion E p) ≤ p ^ 2 := by
  refine ⟨?_, card_torsion_le_prime_sq E p⟩
  rcases card_torsion_prime_or_prime_sq E p with h | h
  · exact h.ge
  · rw [h]
    exact Nat.le_pow (by decide : 0 < 2)

/-- 同じ点を保つ線形同型で、標準torsionBy表示へ正の次元を運ぶ。 -/
theorem finrank_standardTorsion_pos :
    0 < Module.finrank (ZMod p) (StandardTorsion E p) := by
  rw [← (torsionByLinearEquiv E p).finrank_eq]
  exact finrank_torsion_pos E p

end DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
