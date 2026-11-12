/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.EllipticTorsionCardBound
import DkMath.Lib.NumberTheory.EllipticTorsionRankTwo

#print "file: DkMath.Lib.NumberTheory.EllipticTorsionDimensionBound"

/-!
# 正確な位数公式を使わずに、実際のE[p]の次元を上から抑える

有限性はNOTE-012で証明した。同じ実際の点群について、今回の個数の粗い上界と
有限Fₚ空間の濃度公式を合わせると
  p^dim(E[p]) = |E[p]| ≤ 1+2(p²−1) < p³
となる。p≥2なので指数も比較でき、dim(E[p])≤2が得られる。
特にp=2でも7<8で同じ議論が通り、奇素数だけに限定する必要がない。

この次元上界を濃度公式へ戻すと、|E[p]|≤p²にまで上界を改善できる。
これは等号の証明ではない。許される次元は0・1・2であり、非零性や次元2の下界、
既約性は別途証明しなければならない。位数公式の条件付き定理を証明経路に使わない。
-/
namespace DkMath.Lib.NumberTheory.EllipticTorsionRepresentation

/-- p≥2なら、根と高々2点のファイバーによる粗い個数上界はp³より小さい。 -/
theorem degree_bound_lt_cube (p : ℕ) (hp : 2 ≤ p) :
    1 + 2 * (p ^ 2 - 1) < p ^ 3 := by
  have hsq : 0 < p ^ 2 := pow_pos (by omega : 0 < p) _
  have hmul : 2 * p ^ 2 ≤ p ^ 3 := by
    calc 2 * p ^ 2 ≤ p * p ^ 2 := Nat.mul_le_mul_right _ hp
      _ = p ^ 3 := by ring
  omega

variable {K : Type*} [Field K] [CharZero K] (E : WeierstrassCurve K)
  (p : ℕ) [Fact p.Prime]

/-- 実際のp-torsionの次元は高々2。位数p²や非零性を引数に取らない。 -/
theorem finrank_torsion_le_two : Module.finrank (ZMod p) (Torsion E p) ≤ 2 := by
  have hp : p.Prime := Fact.out
  have hc := (card_torsion_le_degree_bound E p hp.ne_zero).trans_lt
    (degree_bound_lt_cube p hp.two_le)
  have hpow := Module.natCard_eq_pow_finrank (K := ZMod p) (V := Torsion E p)
  rw [Nat.card_zmod] at hpow
  rw [hpow] at hc
  have hd := (Nat.pow_lt_pow_iff_right hp.one_lt).mp hc
  omega

/-- 次元上界の意味を明示する。現段階では0と1を除外していない。 -/
theorem finrank_torsion_cases :
    Module.finrank (ZMod p) (Torsion E p) = 0 ∨
      Module.finrank (ZMod p) (Torsion E p) = 1 ∨
      Module.finrank (ZMod p) (Torsion E p) = 2 := by
  have h := finrank_torsion_le_two E p
  omega

/-- 次元上界を濃度へ戻すと、粗い上界をp²へ改善できる。等号は結論しない。 -/
theorem card_torsion_le_prime_sq : Nat.card (Torsion E p) ≤ p ^ 2 := by
  have hpow := Module.natCard_eq_pow_finrank (K := ZMod p) (V := Torsion E p)
  rw [Nat.card_zmod] at hpow
  rw [hpow]
  exact pow_le_pow_right' (Fact.out : p.Prime).one_le (finrank_torsion_le_two E p)

/-- 位数の可能性も1・p・p²に限定できる。位数p²の下界は別の幾何学的入力となる。 -/
theorem card_torsion_prime_cases :
    Nat.card (Torsion E p) = 1 ∨ Nat.card (Torsion E p) = p ∨
      Nat.card (Torsion E p) = p ^ 2 := by
  have hpow := Module.natCard_eq_pow_finrank (K := ZMod p) (V := Torsion E p)
  rw [Nat.card_zmod] at hpow
  rcases finrank_torsion_cases E p with h | h | h
  · left; simpa only [h, pow_zero] using hpow
  · right; left; simpa only [h, pow_one] using hpow
  · right; right; simpa only [h] using hpow

/-- 点を保つ線形同型により、標準torsionBy表示にも同じ次元上界を運べる。 -/
theorem finrank_standardTorsion_le_two :
    Module.finrank (ZMod p) (StandardTorsion E p) ≤ 2 := by
  rw [← (torsionByLinearEquiv E p).finrank_eq]
  exact finrank_torsion_le_two E p

end DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
