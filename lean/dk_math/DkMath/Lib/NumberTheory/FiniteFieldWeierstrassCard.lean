/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.Lib.NumberTheory.EllipticFunctionField
import DkMath.Lib.NumberTheory.EllipticSmoothTorsionReduction
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Card.Arithmetic

#print "file: DkMath.Lib.NumberTheory.FiniteFieldWeierstrassCard"

/-!
# 有限体上の Weierstrass 点数の初等上界

有限体上の Weierstrass 方程式では、固定した有限 `x` 座標に対して `y` は二次方程式
を満たすため、高々二点しかない。無限遠点を別に数えることで、楕円曲線の点数は
`2 * |K| + 1` 以下になる。

ここでは Hasse の評価や群構造を使わない。必要なのは、`xRep` による有限点の識別と
`xRep_eq_xRep_iff` による「同じ `x` なら `P` または `-P`」という幾何学的事実だけである。
-/

namespace DkMath.Lib.NumberTheory

open WeierstrassCurve WeierstrassCurve.Affine

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

/-- 零点を除いた、指定有限 `x` 座標の Weierstrass 点の集合。 -/
def nonzeroXFiber (W : WeierstrassCurve K) (x : K) : Set W.toAffine.Point :=
  {P | P ≠ 0 ∧ P.xc = x}

omit [DecidableEq K] [Fintype K] in
/-- 固定 `x` 座標の非零点は高々二点である。 -/
theorem nonzeroXFiber_ncard_le_two (W : WeierstrassCurve K)
    [W.IsElliptic] (x : K) : (nonzeroXFiber W x).ncard ≤ 2 := by
  classical
  rcases Set.eq_empty_or_nonempty (nonzeroXFiber W x) with he | ⟨Q, hQ⟩
  · rw [he]
    simp
  · have hQ0 : Q ≠ 0 := hQ.1
    have hQx : Q.xc = x := hQ.2
    have he : nonzeroXFiber W x = {Q, -Q} := by
      ext P
      constructor
      · intro hP
        rcases P with _ | ⟨px, py, hp⟩
        · exact (hP.1 rfl).elim
        · rcases Q with _ | ⟨qx, qy, hq⟩
          · exact (hQ0 rfl).elim
          · have hx : px = qx := by simpa [Point.xc_some] using hP.2.trans hQ.2.symm
            rcases (Point.X_eq_iff (W := W.toAffine) (x₁ := px) (y₁ := py)
              (x₂ := qx) (y₂ := qy)).mp hx with h | h
            · exact Or.inl h
            · exact Or.inr h
      · intro hP
        rcases hP with rfl | rfl
        · exact hQ
        · have hnegx : (-Q).xc = Q.xc := by
            cases Q <;> rfl
          exact ⟨by simpa using hQ0, hnegx.trans hQx⟩
    rw [he]
    calc ({Q, -Q} : Set W.toAffine.Point).ncard ≤ ({-Q} : Set W.toAffine.Point).ncard + 1 :=
        Set.ncard_insert_le Q _
      _ = 2 := by simp

omit [DecidableEq K] in
/-- 有限体上の Weierstrass 点数は `2 * |K| + 1` 以下。 -/
theorem card_weierstrass_points_le_two_mul_card_add_one
    (W : WeierstrassCurve K) [W.IsElliptic] :
    Nat.card W.toAffine.Point ≤ 2 * Fintype.card K + 1 := by
  classical
  let : Fintype {xy : K × K // W.toAffine.Equation xy.1 xy.2} :=
    Fintype.ofFinite _
  let : Finite (WithZero {xy : K × K // W.toAffine.Equation xy.1 xy.2}) := by
    change Finite (Option {xy : K × K // W.toAffine.Equation xy.1 xy.2})
    infer_instance
  let : Fintype (WithZero {xy : K × K // W.toAffine.Equation xy.1 xy.2}) :=
    Fintype.ofFinite _
  let : Fintype W.toAffine.Point := Fintype.ofEquiv _ W.toAffine.pointEquiv.symm
  have hcover : (Set.univ : Set W.toAffine.Point) ⊆
      insert 0 (⋃ x : K, nonzeroXFiber W x) := by
    intro P hP
    cases P with
    | zero => exact Set.mem_insert _ _
    | some x y hxy =>
      apply Set.mem_insert_iff.mpr
      right
      exact Set.mem_iUnion.mpr ⟨x, ⟨Point.some_ne_zero hxy, by simp⟩⟩
  calc
    Nat.card W.toAffine.Point = (Set.univ : Set W.toAffine.Point).ncard := by simp
    _ ≤ (insert 0 (⋃ x : K, nonzeroXFiber W x)).ncard := Set.ncard_mono hcover
    _ ≤ (⋃ x : K, nonzeroXFiber W x).ncard + 1 := Set.ncard_insert_le _ _
    _ ≤ (∑ x : K, (nonzeroXFiber W x).ncard) + 1 :=
      Nat.add_le_add_right (Set.ncard_iUnion_le_of_fintype _) 1
    _ ≤ (∑ _x : K, 2) + 1 :=
      Nat.add_le_add_right (Finset.sum_le_sum (fun x _ => nonzeroXFiber_ncard_le_two W x)) 1
    _ = 2 * Fintype.card K + 1 := by simp [mul_comm]

/--
有限標的群への単射準同型が、点の加法位数を標的の個数で抑える一般補題。

良還元の具体的な還元写像をこの定理へ接続するには、捩れ点上の還元単射性を別途
供給する必要がある。この補題自体は還元環や楕円曲線に依存せず、後段の局所還元 API
から再利用できる最小の群論的核を公開する。
-/
theorem addOrderOf_le_natCard_of_injective_addMonoidHom
    {G H : Type*} [AddGroup G] [AddGroup H] [Finite H]
    (f : G →+ H) (hf : Function.Injective f) (Q : G) :
    addOrderOf Q ≤ Nat.card H := by
  rw [← addOrderOf_injective f hf Q]
  have hfin : ((⊤ : AddSubgroup H) : Set H).Finite := by simp
  have htop : Nat.card (⊤ : AddSubgroup H) = Nat.card H :=
    Nat.card_congr (AddSubgroup.topEquiv (G := H))
  simpa [htop] using
    (AddSubgroup.addOrderOf_le_card (⊤ : AddSubgroup H) hfin (by simp : f Q ∈ (⊤ : AddSubgroup H)))

/-- 有限体上の Weierstrass 点の加法位数は、点数の初等上界を越えない。

これは前の二つの教科書補題の直接の組合せである。`W.toAffine.Point` 自体を
有限標的群とみなし、恒等準同型を `addOrderOf_le_natCard_of_injective_addMonoidHom`
へ渡す。後段で良還元の還元写像を有限体上のこの点群へ接続すれば、捩れ点の位数
制限として再利用できる。
-/
theorem addOrderOf_le_two_mul_card_add_one_of_weierstrass
    (W : WeierstrassCurve K) [W.IsElliptic] (Q : W.toAffine.Point) :
    addOrderOf Q ≤ 2 * Fintype.card K + 1 := by
  classical
  let : Fintype {xy : K × K // W.toAffine.Equation xy.1 xy.2} :=
    Fintype.ofFinite _
  let : Finite (WithZero {xy : K × K // W.toAffine.Equation xy.1 xy.2}) := by
    change Finite (Option {xy : K × K // W.toAffine.Equation xy.1 xy.2})
    infer_instance
  let : Fintype (WithZero {xy : K × K // W.toAffine.Equation xy.1 xy.2}) :=
    Fintype.ofFinite _
  let : Fintype W.toAffine.Point := Fintype.ofEquiv _ W.toAffine.pointEquiv.symm
  have h := addOrderOf_le_natCard_of_injective_addMonoidHom
    (AddMonoidHom.id (W.toAffine.Point)) (Function.injective_id) Q
  rw [Nat.card_eq_fintype_card] at h
  exact h.trans (by
    simpa only [Nat.card_eq_fintype_card] using
      (card_weierstrass_points_le_two_mul_card_add_one W))

/-- 有限体 Weierstrass 群では、`2p` 位数の点は `2q+1 < 2p` なら存在しない。

この命題は Hasse の評価や Mazur の分類を使わない。有限体上の各 `x` に対する
二次方程式の根数上界だけから得た点数評価と、有限群内の位数評価を `omega` で
接続したものである。良還元の一般ファイバーからここへ到達するには、別途、
還元写像の単射性と剰余体モデルの同定を供給する。
-/
theorem no_two_mul_order_of_weierstrass_of_card_lt
    (W : WeierstrassCurve K) [W.IsElliptic] {p : ℕ}
    (hsmall : 2 * Fintype.card K + 1 < 2 * p) :
    ¬ ∃ Q : W.toAffine.Point, addOrderOf Q = 2 * p := by
  rintro ⟨Q, hQ⟩
  have hbound := addOrderOf_le_two_mul_card_add_one_of_weierstrass W Q
  rw [hQ] at hbound
  omega

/-- `#K ≤ q < p` なら、有限体 `K` の初等点数上界は `2p` より小さい。

素数性をこの算術補題の内部に埋め込まず、実際の Frey 側で `q` と `p` の素数性・
良還元を別途保持できる形にしている。有限体 `𝔽_q` への特殊化では
`Fintype.card K = q` を `hcard` に渡せばよい。
-/
theorem no_two_mul_order_of_weierstrass_of_card_le
    (W : WeierstrassCurve K) [W.IsElliptic] {p : ℕ}
    {q : ℕ} (hcard : Fintype.card K ≤ q) (hqp : q < p) :
    ¬ ∃ Q : W.toAffine.Point, addOrderOf Q = 2 * p := by
  apply no_two_mul_order_of_weierstrass_of_card_lt W
  omega

/-- 良還元モデルの滑らかな `n` 捩れ集合を、有限剰余体の初等点数で抑える。

`EllipticSmoothTorsionReduction.finite_and_ncard_le_of_residue_bound` は、単元位数の
還元単射性を一般の剰余点数上界へ輸送する。この定理では剰余モデルが良還元である
ことを `hgood` から明示的に `IsElliptic` として供給し、直前の有限体 Weierstrass
点数評価を剰余 `n` 捩れ集合へ適用する。有限体への同定や `FreyLocalReduction`
との接続は、この定理の外側で行う。
-/
theorem finite_smooth_torsion_ncard_le_two_mul_residue_card_add_one
    {L : Type*} [Field L] [CharZero L] [DecidableEq L] (A : ValuationSubring L)
    (W : WeierstrassCurve A) [Fintype (IsLocalRing.ResidueField A)]
    (hgood : (W.map (IsLocalRing.residue A)).Δ ≠ 0) {n : ℕ}
    (hn : A.valuation (n : L) = 1) :
    {P : (W.map A.subtype).toAffine.Point |
        EllipticGoodReductionSeparation.HasSmoothReduction W P ∧ n • P = 0}.Finite ∧
      {P : (W.map A.subtype).toAffine.Point |
        EllipticGoodReductionSeparation.HasSmoothReduction W P ∧ n • P = 0}.ncard ≤
        2 * Fintype.card (IsLocalRing.ResidueField A) + 1 := by
  classical
  let W₀ := W.map (IsLocalRing.residue A)
  let : W₀.IsElliptic := ⟨isUnit_iff_ne_zero.mpr hgood⟩
  let : Fintype {xy : IsLocalRing.ResidueField A × IsLocalRing.ResidueField A //
      W₀.toAffine.Equation xy.1 xy.2} := Fintype.ofFinite _
  let : Finite (WithZero {xy : IsLocalRing.ResidueField A × IsLocalRing.ResidueField A //
      W₀.toAffine.Equation xy.1 xy.2}) := by
    change Finite (Option {xy : IsLocalRing.ResidueField A × IsLocalRing.ResidueField A //
      W₀.toAffine.Equation xy.1 xy.2})
    infer_instance
  let : Fintype (WithZero {xy : IsLocalRing.ResidueField A × IsLocalRing.ResidueField A //
      W₀.toAffine.Equation xy.1 xy.2}) := Fintype.ofFinite _
  let : Fintype W₀.toAffine.Point := Fintype.ofEquiv _ W₀.toAffine.pointEquiv.symm
  let T : Set W₀.toAffine.Point := {P | n • P = 0}
  have hfinite : T.Finite := Set.toFinite _
  have hbound : T.ncard ≤ 2 * Fintype.card (IsLocalRing.ResidueField A) + 1 := by
    calc
      T.ncard ≤ (Set.univ : Set W₀.toAffine.Point).ncard :=
        Set.ncard_mono (by intro P hP; exact Set.mem_univ P)
      _ = Nat.card W₀.toAffine.Point := by simp
      _ ≤ 2 * Fintype.card (IsLocalRing.ResidueField A) + 1 :=
        card_weierstrass_points_le_two_mul_card_add_one W₀
  exact EllipticSmoothTorsionReduction.finite_and_ncard_le_of_residue_bound
    W hn hfinite hbound

end DkMath.Lib.NumberTheory
