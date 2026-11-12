/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.EllipticMultiplicationCoordinates
import DkMath.Lib.NumberTheory.EllipticTorsionDimensionCriteria

#print "file: DkMath.Lib.NumberTheory.EllipticTorsionRegularFiber"

/-!
# 正則ファイバーの根から、実際のねじれ点群への単射

H_c=Φₙ−cΨSqₙは次数n²を持ち、有限個の例外値を避ければ分離的になる。
各根xを点Pに持ち上げると、[n]Pのx座標はcである。固定した有限座標点Qに対して
[n]PはQか−Qなので、必要ならPを−Pへ替える。符号を変えてもx座標は保存され、
相異なる根から[n]⁻¹(Q)への単射を得る。Q=−Qの場合も同じ選択ができるため、
2-torsion由来の値を別に避ける必要はなく、奇数条件も使わない。

非空ファイバーは一点の平行移動で核と全単射になる。従ってn²≤|E[n]|を得る。
素数ではNOTE-013の上界と合わせ、正確な位数p²・次元2が確定する。
一般の合成数での正確な位数の上界や、ガロア表現の既約性は別の問題である。
-/
namespace DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
open WeierstrassCurve Polynomial
open scoped WeierstrassCurve.Affine
open DkMath.Lib.Algebra
variable {K : Type*} [Field K] [CharZero K] (E : WeierstrassCurve K)

/-- 倍写像のx座標がcになるための一変数多項式。 -/
noncomputable def multiplicationFiberPolynomial (n : ℕ) (c : AlgebraicClosure K) :
    Polynomial (AlgebraicClosure K) := RationalPolynomialFiber.fiberPolynomial
  ((E.baseChange (AlgebraicClosure K)).Φ (n : ℤ))
  ((E.baseChange (AlgebraicClosure K)).ΨSq (n : ℤ)) c

omit [CharZero K] in
/-- 非零指数では分子と分母の次数差が1なので、cによらず次数はn²。 -/
theorem multiplication_fiber_natDegree (n : ℕ) (hn : n ≠ 0) (c : AlgebraicClosure K) :
    (multiplicationFiberPolynomial E n c).natDegree = n ^ 2 := by
  let W := E.baseChange (AlgebraicClosure K)
  change (W.Φ (n : ℤ) - C c * W.ΨSq (n : ℤ)).natDegree = _
  rw [natDegree_sub_eq_left_of_natDegree_lt, W.natDegree_Φ, Int.natAbs_natCast]
  apply lt_of_le_of_lt (natDegree_C_mul_le c _)
  have hd := W.natDegree_ΨSq_le (n : ℤ)
  rw [Int.natAbs_natCast] at hd
  rw [W.natDegree_Φ, Int.natAbs_natCast]
  have hp : 0 < n ^ 2 := pow_pos (Nat.pos_of_ne_zero hn) _
  omega

/-- 実際のn倍写像の一つのファイバー。元は同じ幾何学的な点群の点である。 -/
def MultiplicationFiber (n : ℕ) (Q : Points E) := {P : Points E // n • P = Q}

/-- 非空ファイバーは一点の平行移動によって元のn-torsionの核と全単射になる。 -/
noncomputable def torsionEquivMultiplicationFiber (n : ℕ) (Q P₀ : Points E) (hP₀ : n • P₀ = Q) :
    Torsion E n ≃ MultiplicationFiber E n Q where
  toFun T := ⟨T.val + P₀, by
    rw [nsmul_add, show n • T.val = 0 from T.property, zero_add, hP₀]⟩
  invFun P := ⟨P.val - P₀, by
    change n • (P.val - P₀) = 0
    rw [nsmul_sub, P.property, hP₀, sub_self]⟩
  left_inv T := by apply Subtype.ext; exact add_sub_cancel_right _ _
  right_inv P := by apply Subtype.ext; exact sub_add_cancel _ _

variable [E.IsElliptic]

/-- 重根を持つファイバーの例外値は有限である。 -/
theorem multiplication_finite_not_separable (n : ℕ) (hn : n ≠ 0) :
    {c : AlgebraicClosure K | ¬ (multiplicationFiberPolynomial E n c).Separable}.Finite :=
  RationalPolynomialFiber.finite_not_separable_fiber (multiplication_polynomials_isCoprime E n)
    (multiplication_wronskian_ne_zero E n hn)

/-- 平方因子を持つファイバーの例外値も有限である。 -/
theorem multiplication_finite_not_squarefree (n : ℕ) (hn : n ≠ 0) :
    {c : AlgebraicClosure K | ¬ Squarefree (multiplicationFiberPolynomial E n c)}.Finite :=
  RationalPolynomialFiber.finite_not_squarefree_fiber (multiplication_polynomials_isCoprime E n)
    (multiplication_wronskian_ne_zero E n hn)

/-- 代数閉包の無限性によって、分離的な良いファイバーを選べる。 -/
theorem exists_multiplication_separable_fiber (n : ℕ) (hn : n ≠ 0) :
    ∃ c : AlgebraicClosure K, (multiplicationFiberPolynomial E n c).Separable := by
  obtain ⟨c, hc, _⟩ := RationalPolynomialFiber.exists_separable_fiber_avoiding
    (multiplication_polynomials_isCoprime E n) (multiplication_wronskian_ne_zero E n hn)
    (Set.finite_empty : (∅ : Set (AlgebraicClosure K)).Finite)
  exact ⟨c, hc⟩

omit [E.IsElliptic] [CharZero K] in
/-- 良いファイバーでは重複を捨てた相異なる根もちょうどn²個ある。 -/
theorem multiplication_separable_root_card (n : ℕ) (hn : n ≠ 0) (c : AlgebraicClosure K)
    (hc : (multiplicationFiberPolynomial E n c).Separable) :
    Nat.card {x : AlgebraicClosure K // (multiplicationFiberPolynomial E n c).IsRoot x} = n ^ 2 := by
  classical
  let H := multiplicationFiberPolynomial E n c
  have hm : ∀ x, H.IsRoot x ↔ x ∈ H.roots.toFinset := fun x =>
    (Multiset.mem_toFinset.trans (Polynomial.mem_roots hc.ne_zero)).symm
  rw [Nat.card_congr (Equiv.subtypeEquivRight hm)]
  change (H.roots.toFinset : Set (AlgebraicClosure K)).ncard = _
  rw [Set.ncard_coe_finset, Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots hc),
    IsAlgClosed.card_roots_eq_natDegree]
  exact multiplication_fiber_natDegree E n hn c

/-- 根から固定した有限座標点Qの倍写像ファイバーへ、x座標を保存して持ち上げる。
符号の二択は排他的である必要がなく、Q=−Qも許す。 -/
theorem exists_aligned_multiplication_preimage (n : ℕ) {c yQ x : AlgebraicClosure K}
    (hQ : (E.toAffine⁄(AlgebraicClosure K)).Nonsingular c yQ)
    (hx : (multiplicationFiberPolynomial E n c).IsRoot x) :
    ∃ P : Points E, (nsmulAddMonoidHom n : Points E →+ Points E) P =
      Affine.Point.some c yQ hQ ∧ P.xRep = ![x, 1] := by
  classical
  let W := E.baseChange (AlgebraicClosure K)
  have hd := RationalPolynomialFiber.eval_denominator_ne_zero (multiplication_polynomials_isCoprime E n) hx
  have hr : (W.Φ (n : ℤ)).eval x = c * (W.ΨSq (n : ℤ)).eval x := by
    have hh := hx
    change (W.Φ (n : ℤ) - C c * W.ΨSq (n : ℤ)).eval x = 0 at hh
    simpa only [eval_sub, eval_mul, eval_C, sub_eq_zero] using hh
  obtain ⟨y, hy⟩ := exists_affine_equation_y E x
  have : W.IsElliptic := by
    change (E.map (algebraMap K (AlgebraicClosure K))).IsElliptic
    infer_instance
  have hns : W.toAffine.Nonsingular x y := Affine.equation_iff_nonsingular.mp hy
  obtain ⟨x', y', h', he, hcoord⟩ := multiplication_finite_coordinates E n hns hd
  have hxc : x' = c := mul_right_cancel₀ hd (hcoord.trans hr)
  let P : Points E := Affine.Point.some x y hns
  let Q : Points E := Affine.Point.some c yQ hQ
  have he' : n • P = (Affine.Point.some x' y' h' : Points E) := he
  have hrep : (n • P).xRep = Q.xRep := by
    calc (n • P).xRep = ![x', 1] := congrArg (fun T : Points E => T.xRep) he'
      _ = Q.xRep := by rw [hxc]; rfl
  have hcase : n • P = Q ∨ n • P = -Q := Affine.Point.xRep_eq_xRep_iff.mp hrep
  rcases hcase with hh | hh
  · exact ⟨P, hh, rfl⟩
  · refine ⟨-P, ?_, ?_⟩
    · change n • (-P) = Q
      rw [neg_nsmul, hh, neg_neg]
    · have hh' : (-P).xRep = P.xRep := Affine.Point.xRep_neg P
      exact hh'.trans rfl

/-- 根ごとの符号選択はx座標を保存するので、相異なる根から異なる点を得る単射となる。 -/
noncomputable def multiplicationRootEmbedding (n : ℕ) (c yQ : AlgebraicClosure K)
    (hQ : (E.toAffine⁄(AlgebraicClosure K)).Nonsingular c yQ) :
    {x : AlgebraicClosure K // (multiplicationFiberPolynomial E n c).IsRoot x} ↪
      MultiplicationFiber E n (Affine.Point.some c yQ hQ) := by
  classical
  choose f hf using fun x : {x : AlgebraicClosure K // (multiplicationFiberPolynomial E n c).IsRoot x} =>
    exists_aligned_multiplication_preimage E n hQ x.property
  refine ⟨fun x => ⟨f x, (hf x).1⟩, ?_⟩
  intro x₁ x₂ he
  apply Subtype.ext
  have hh := congrArg (fun P : MultiplicationFiber E n (Affine.Point.some c yQ hQ) => P.val.xRep) he
  rw [(hf x₁).2, (hf x₂).2] at hh
  exact congrFun hh 0

/-- 良いファイバーのn²個の相異なる根を実際の核へ単射で運び、下界だけを得る。 -/
theorem square_le_card_torsion (n : ℕ) (hn : n ≠ 0) : n ^ 2 ≤ Nat.card (Torsion E n) := by
  classical
  have := finite_torsion_of_ne_zero E n hn
  obtain ⟨c, hc⟩ := exists_multiplication_separable_fiber E n hn
  obtain ⟨yQ, hyQ⟩ := exists_affine_equation_y E c
  have : (E.baseChange (AlgebraicClosure K)).IsElliptic := by
    change (E.map (algebraMap K (AlgebraicClosure K))).IsElliptic
    infer_instance
  have hQ := Affine.equation_iff_nonsingular.mp hyQ
  have hdeg : 0 < (multiplicationFiberPolynomial E n c).natDegree := by
    rw [multiplication_fiber_natDegree E n hn c]
    exact pow_pos (Nat.pos_of_ne_zero hn) _
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root (multiplicationFiberPolynomial E n c)
    (ne_of_gt (natDegree_pos_iff_degree_pos.mp hdeg))
  obtain ⟨P₀, hP₀, _⟩ := exists_aligned_multiplication_preimage E n hQ hx
  let j := multiplicationRootEmbedding E n c yQ hQ
  let e := torsionEquivMultiplicationFiber E n (Affine.Point.some c yQ hQ) P₀ hP₀
  rw [← multiplication_separable_root_card E n hn c hc]
  exact Nat.card_le_card_of_injective (fun x => e.symm (j x)) (e.symm.injective.comp j.injective)

/-- 素数では既存の上界p²と今回の幾何学的下界が一致し、正確な位数が確定する。 -/
theorem card_torsion_prime_sq (p : ℕ) [Fact p.Prime] : Nat.card (Torsion E p) = p ^ 2 :=
  Nat.le_antisymm (card_torsion_le_prime_sq E p) (square_le_card_torsion E p (Fact.out : p.Prime).ne_zero)

/-- 位数の外部入力なしで、標数0の楕円曲線の実際のp-torsionは二次元である。 -/
theorem finrank_torsion_prime (p : ℕ) [Fact p.Prime] : Module.finrank (ZMod p) (Torsion E p) = 2 := by
  have hc := Module.natCard_eq_pow_finrank (K := ZMod p) (V := Torsion E p)
  rw [card_torsion_prime_sq E p, Nat.card_zmod] at hc
  exact (Nat.pow_right_injective (Fact.out : p.Prime).two_le hc).symm

/-- 任意の非零p-torsion点の直線の外に、同じ実際の曲線の第二の点が存在する。 -/
theorem exists_torsion_prime_outside_span (p : ℕ) [Fact p.Prime] (P : Torsion E p) (hP : P ≠ 0) :
    ∃ Q : Torsion E p, Q ∉ Submodule.span (ZMod p) ({P} : Set (Torsion E p)) :=
  (finrank_torsion_eq_two_iff_exists_outside_span E p P hP).mp (finrank_torsion_prime E p)

/-- 標準torsionBy表示にも、点を保つ線形同型で同じ二次元を運ぶ。 -/
theorem finrank_standardTorsion_prime (p : ℕ) [Fact p.Prime] :
    Module.finrank (ZMod p) (StandardTorsion E p) = 2 := by
  rw [← (torsionByLinearEquiv E p).finrank_eq]
  exact finrank_torsion_prime E p

/-- 奇素数では、既存の正確な二点ファイバー計数へ戻して相異なる根の数も確定する。 -/
theorem divisionRootCount_odd_prime (p : ℕ) [Fact p.Prime] (hp : Odd p) :
    divisionRootCount E p = (p ^ 2 - 1) / 2 := by
  have hc := card_torsion_eq_one_add_twice_roots E hp
  rw [card_torsion_prime_sq E p] at hc
  omega

end DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
