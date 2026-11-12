/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.EllipticTorsionStandardEquiv
import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Finiteness

#print "file: DkMath.Lib.NumberTheory.EllipticTorsionRankTwo"

/-!
# 位数p²から次元2へ: 幾何学と線形代数の境界

素数pについて、実際のE[p]の位数がp²と分かれば、まず有限性が得られる。
有限Fₚ空間の濃度公式 |V|=p^dim(V) とp≥2から次元2が従う。
ここでは位数公式を引数として明示する。これは楕円曲線の位数公式そのものの証明ではない。
`Nat.card` は無限型では0なので、p²≠0から有限性を取り出す手順も省かない。

Mathlibの除法多項式の次数計算だけでは、実際の点のn倍写像の核の位数はまだ決まらない。
必要なのは倍写像と除法多項式の接続、根の重複度、各根上の点の数を結ぶ幾何学である。
標数がpでない楕円曲線について、この幾何学からhcardを供給することを残す。
この境界の後の線形代数は曲線の非特異性や標数を使わずに再利用できる。
-/
namespace DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
variable {K : Type*} [Field K] (E : WeierstrassCurve K) (p : ℕ) [Fact p.Prime]

/-- 位数p²が実際の点群で証明された場合、その点群は有限である。 -/
theorem finite_of_card_sq (hcard : Nat.card (Torsion E p) = p ^ 2) : Finite (Torsion E p) :=
  Nat.finite_of_card_ne_zero (hcard ▸ pow_ne_zero 2 (Fact.out : p.Prime).ne_zero)

/-- 位数p²を入力とする次元2。位数の幾何学的providerを隠さない。 -/
theorem finrank_eq_two_of_card_sq (hcard : Nat.card (Torsion E p) = p ^ 2) :
    Module.finrank (ZMod p) (Torsion E p) = 2 := by
  have := finite_of_card_sq E p hcard
  have hc := Module.natCard_eq_pow_finrank (K := ZMod p) (V := Torsion E p)
  rw [hcard, Nat.card_zmod] at hc
  exact (Nat.pow_right_injective (Fact.out : p.Prime).two_le hc).symm

omit [Fact p.Prime] in
/-- 位数providerは点を保つ標準アダプタで相互変換できる。 -/
theorem standard_card_sq_iff :
    Nat.card (StandardTorsion E p) = p ^ 2 ↔ Nat.card (Torsion E p) = p ^ 2 := by
  rw [Nat.card_congr (torsionByLinearEquiv E p).toEquiv]

/-- 標準torsionByで証明された位数公式も、同じ実際の点群の次元2へ接続する。 -/
theorem finrank_eq_two_of_standard_card_sq
    (hcard : Nat.card (StandardTorsion E p) = p ^ 2) :
    Module.finrank (ZMod p) (Torsion E p) = 2 :=
  finrank_eq_two_of_card_sq E p ((standard_card_sq_iff E p).mp hcard)

end DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
