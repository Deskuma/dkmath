/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.EllipticTorsionRootCount
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

#print "file: DkMath.Lib.NumberTheory.EllipticTorsionDimensionCriteria"

/-!
# 二次元への残る入力を、点数・直線の外の点・相異なる根の下界へ翻訳する

NOTE-014で次元は1か2、位数はpかp²に限られた。従ってpより多くの点があれば
二次元に確定する。非零点Pの張る直線の外にQがあることも同じ条件である。
奇素数ではNOTE-015の正確な計数 |E[p]|=1+2r を使い、(p−1)/2<rへ翻訳できる。

これらは入力を交換する同値と条件付きの接続である。一般の奇素数について
直線の外の点や根の下界を供給する幾何学そのものを証明したとは主張しない。
位数p²を入力する旧来の次元定理を経由せず、実際の有限空間の濃度公式から証明する。
-/
namespace DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
variable {K : Type*} [Field K] [CharZero K] (E : WeierstrassCurve K) [E.IsElliptic]
  (p : ℕ) [Fact p.Prime]

/-- p個より多い点さえあれば、pかp²という二者択一のpを排除できる。 -/
theorem card_torsion_eq_prime_sq_of_prime_lt (h : p < Nat.card (Torsion E p)) :
    Nat.card (Torsion E p) = p ^ 2 := by
  rcases card_torsion_prime_or_prime_sq E p with hc | hc
  · omega
  · exact hc

/-- 小さい追加下界から二次元へ。正確な位数を外部の引数としては受け取らない。 -/
theorem finrank_torsion_eq_two_of_prime_lt (h : p < Nat.card (Torsion E p)) :
    Module.finrank (ZMod p) (Torsion E p) = 2 := by
  have hc := Module.natCard_eq_pow_finrank (K := ZMod p) (V := Torsion E p)
  rw [card_torsion_eq_prime_sq_of_prime_lt E p h, Nat.card_zmod] at hc
  exact (Nat.pow_right_injective (Fact.out : p.Prime).two_le hc).symm

/-- 次元2とpを超える点数は同値。p²個を最初から構成する必要はない。 -/
theorem finrank_torsion_eq_two_iff_prime_lt_card :
    Module.finrank (ZMod p) (Torsion E p) = 2 ↔ p < Nat.card (Torsion E p) := by
  refine ⟨?_, finrank_torsion_eq_two_of_prime_lt E p⟩
  intro hd
  have hc := Module.natCard_eq_pow_finrank (K := ZMod p) (V := Torsion E p)
  rw [Nat.card_zmod, hd] at hc
  rw [hc]
  have hp := (Fact.out : p.Prime).two_le
  nlinarith

omit [E.IsElliptic] in
/-- 指定した非零点Pの直線の外に点Qがあることが、二次元への正確な残りの入力。 -/
theorem finrank_torsion_eq_two_iff_exists_outside_span (P : Torsion E p) (hP : P ≠ 0) :
    Module.finrank (ZMod p) (Torsion E p) = 2 ↔
      ∃ Q : Torsion E p, Q ∉ Submodule.span (ZMod p) ({P} : Set (Torsion E p)) := by
  have hline : Module.finrank (ZMod p) (Submodule.span (ZMod p) ({P} : Set (Torsion E p))) = 1 :=
    finrank_span_singleton hP
  constructor
  · intro hd
    by_contra hn
    push Not at hn
    have ht : Submodule.span (ZMod p) ({P} : Set (Torsion E p)) = ⊤ :=
      Submodule.eq_top_iff'.mpr hn
    rw [ht, finrank_top, hd] at hline
    omega
  · rintro ⟨Q, hQ⟩
    have ht : Submodule.span (ZMod p) ({P} : Set (Torsion E p)) ≠ ⊤ := by
      intro ht
      exact hQ (ht ▸ Submodule.mem_top)
    have hd := Submodule.finrank_lt ht
    rw [hline] at hd
    have hu := finrank_torsion_le_two E p
    omega

/-- 奇素数なら、相異なる根の下界だけで次元2を判定できる。自然数の除算を明示する。 -/
theorem finrank_torsion_eq_two_iff_root_count (hp : Odd p) :
    Module.finrank (ZMod p) (Torsion E p) = 2 ↔ (p - 1) / 2 < divisionRootCount E p := by
  rw [finrank_torsion_eq_two_iff_prime_lt_card, card_torsion_eq_one_add_twice_roots E hp]
  obtain ⟨k, hk⟩ := hp
  omega

/-- 実際の非零点の直線の外を見つける問題と、相異なる根の下界は同値である。 -/
theorem exists_outside_span_iff_root_count (hp : Odd p) (P : Torsion E p) (hP : P ≠ 0) :
    (∃ Q : Torsion E p, Q ∉ Submodule.span (ZMod p) ({P} : Set (Torsion E p))) ↔
      (p - 1) / 2 < divisionRootCount E p :=
  (finrank_torsion_eq_two_iff_exists_outside_span E p P hP).symm.trans
    (finrank_torsion_eq_two_iff_root_count E p hp)

end DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
