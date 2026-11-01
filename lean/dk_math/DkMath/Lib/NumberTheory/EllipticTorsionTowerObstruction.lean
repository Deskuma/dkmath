/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.Algebra.TorsionTowerFrobenius
import DkMath.Lib.NumberTheory.EllipticTorsionAllCard

#print "file: DkMath.Lib.NumberTheory.EllipticTorsionTowerObstruction"

/-!
# 実際の楕円曲線の点群へ最終矛盾を接続する

一般群の最終矛盾に、既に証明済みの楕円曲線の二つの幾何学的事実を供給する。
`#E[p]=p²` と、非零整数による倍写像の全射性である。別の形式的な群や外部
濃度 provider に置き換えず、既存の `Points E` と `Torsion E p` をそのまま使う。

残る仮定は、実際の塔の底 `H` の濃度 `p`、上段 `K` の `p` 捩れが `H` へ落ちること、
および正の還元点数 `N` による scalar absorption である。これらは大域 torsion 議論の
未実装部分であり、ここでは構成したと主張しない。
-/

namespace DkMath.Lib.NumberTheory.EllipticTorsionRepresentation

open DkMath.Lib.Algebra TorsionTowerFrobenius

variable {F : Type*} [Field F] [CharZero F] (E : WeierstrassCurve F) [E.IsElliptic]
    {p : ℕ} [Fact p.Prime]

/-- 完成済みの幾何学で二つの一般群仮定を埋めた、楕円曲線の最終捩れ塔矛盾。 -/
theorem false_of_prime_torsion_tower_scalar_absorbs
    (H K : AddSubgroup (Points E)) {N : ℕ} (hN : 0 < N)
    (hHcard : Nat.card H = p)
    (hdown : ∀ x ∈ K, p • x = 0 → x ∈ H)
    (habsorb : ∀ y : Points E, p ^ N • y = 0 → N • y ∈ K) : False := by
  apply false_of_rank_two_scalar_absorbs (Fact.out : p.Prime) H K hN
  · exact card_torsion_sq E p (Fact.out : p.Prime).ne_zero
  · exact hHcard
  · intro t
    exact multiplication_surjective E (p ^ t) (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
  · exact hdown
  · exact habsorb

/-- 実際の Frobenius 作用の商上の固定性と Cayley–Hamilton 関係が供給されれば、
scalar absorption を利用側に再証明させず、既存の幾何学と一括して矛盾を得る。 -/
theorem false_of_prime_torsion_tower_frobenius
    (H K : AddSubgroup (Points E)) {N : ℕ} (hN : 0 < N)
    (hHcard : Nat.card H = p)
    (hdown : ∀ x ∈ K, p • x = 0 → x ∈ H)
    (φ : Points E →+ Points E) (ell : ℤ)
    (hfixed : ∀ y : Points E, p ^ N • y = 0 → φ y - y ∈ K)
    (hCH : ∀ y : Points E, p ^ N • y = 0 →
      φ (φ y) + ell • y = (ell + 1 - (N : ℤ)) • φ y) : False := by
  exact false_of_prime_torsion_tower_scalar_absorbs E H K hN hHcard hdown
    (fun y hy => nsmul_mem_of_frobenius_relation K φ (p ^ N) N ell hfixed hCH hy)

end DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
