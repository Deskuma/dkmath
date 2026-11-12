/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyResidualGeometry
import DkMath.Lib.NumberTheory.EllipticTorsionDimensionBound

#print "file: DkMath.FLT.FreyResidualDimensionBound"

/-!
# 同じFrey Sourceの残余空間の次元上界

同じ有理曲線の実際のE[p]について、有限性と座標の個数上界を組み合わせて
Fₚ次元が高々2であることを公開する。位数p²・次元2・非零性の追加仮定はない。
得られるのは上界であり、次元の候補0・1・2のうち2を選ぶには下からの情報が必要である。
基底を持つFₚ²への同型、GL₂表現、既約性をこの上界だけで構成してはならない。
既存の有限レベルも同じSourceのまま保持する。
-/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
variable {p : ℕ} (S : Source p)

/-- 非零指数での、根と高々2点のファイバーから得る個数上界。 -/
theorem residual_card_le_degree_bound (hp : p ≠ 0) :
    Nat.card S.ResidualSpace ≤ 1 + 2 * (p ^ 2 - 1) :=
  card_torsion_le_degree_bound S.rationalCurve p hp

/-- 素数指数の実際の残余空間は高々2次元である。 -/
theorem residual_finrank_le_two [Fact p.Prime] :
    Module.finrank (ZMod p) S.ResidualSpace ≤ 2 :=
  finrank_torsion_le_two S.rationalCurve p

/-- 濃度公式へ戻して改善した位数上界。位数p²の下界とは区別する。 -/
theorem residual_card_le_prime_sq [Fact p.Prime] : Nat.card S.ResidualSpace ≤ p ^ 2 :=
  card_torsion_le_prime_sq S.rationalCurve p

/-- 次元の候補は0・1・2であり、2に確定したとは主張しない。 -/
theorem residual_finrank_cases [Fact p.Prime] :
    Module.finrank (ZMod p) S.ResidualSpace = 0 ∨
      Module.finrank (ZMod p) S.ResidualSpace = 1 ∨
      Module.finrank (ZMod p) S.ResidualSpace = 2 :=
  finrank_torsion_cases S.rationalCurve p

/-- 位数の候補は1・p・p²である。 -/
theorem residual_card_prime_cases [Fact p.Prime] :
    Nat.card S.ResidualSpace = 1 ∨ Nat.card S.ResidualSpace = p ∨
      Nat.card S.ResidualSpace = p ^ 2 :=
  card_torsion_prime_cases S.rationalCurve p

/-- 次元上界・改善した個数上界・有限レベルを同じ曲線上でまとめる入口。 -/
theorem residual_bounded_profile [Fact p.Prime] :
    Module.finrank (ZMod p) S.ResidualSpace ≤ 2 ∧
      Nat.card S.ResidualSpace ≤ p ^ 2 ∧ S.ResidualFactorsThroughFiniteLevel :=
  ⟨S.residual_finrank_le_two, S.residual_card_le_prime_sq,
    S.residual_factorsThroughFiniteLevel_of_prime⟩

end DkMath.FLT.Frey.Source
