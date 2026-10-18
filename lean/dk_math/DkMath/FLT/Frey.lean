/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.FreyPrimeValuation

#print "file: DkMath.FLT.Frey"

/-!
# NOTE-005: 原始冪和から Frey の局所算術へ

この公開入口は三つの段階を混ぜない。
(1) 冪和・非零性・原始性・整数モデルの分母条件を持つ `Source`、
(2) そこから構成した実際の Weierstrass モデルと判別式、
(3) 奇素数ごとの判別式付値と c₄ の可除性、である。

source の整数・共通因子・符号を取り直さず、そのまま保持する。
向き付け済みの整数からの構成は `ofOriented` が分母条件を証明する。
任意の反例の向き付け、素数2での最小性、mod-p 表現、モジュラー性、
レベル降下の供給は、ここで得た局所算術とは別の未実装境界である。
-/

namespace DkMath.FLT.Frey

open DkMath.Lib.NumberTheory FreyGapCubic GNFreyDiscriminant FreyPrimeValuation

/-- 座標と算術前提を保持する入力。p の素数性はこれらの代数計算には不要。
FLT の素数指数への応用では別途 p が素数であることを供給する。 -/
structure Source (p : ℕ) where
  a : ℤ
  b : ℤ
  c : ℤ
  a_ne : a ≠ 0
  b_ne : b ≠ 0
  c_ne : c ≠ 0
  coprime : IsCoprime a b
  equation : a ^ p + b ^ p = c ^ p
  normalization : IntegralNormalization (a ^ p) (b ^ p)

namespace Source
variable {p : ℕ} (S : Source p)

/-- 全ての整数座標を保った非零積。付値の零デフォルトを誤用しないための前提。 -/
theorem product_ne_zero : S.a * S.b * S.c ≠ 0 :=
  mul_ne_zero (mul_ne_zero S.a_ne S.b_ne) S.c_ne

/-- 同じ a,b から得る実際の整係数モデル。 -/
def curve : WeierstrassCurve ℤ := integral (S.a ^ p) (S.b ^ p)

/-- 同じ座標から得る有理数上の正規化モデル。 -/
def rationalCurve : WeierstrassCurve ℚ := normalized ((S.a : ℚ) ^ p) ((S.b : ℚ) ^ p)

/-- 整数モデルと有理数モデルの一致を実際の基底変換で保持する。 -/
theorem curve_map : S.curve.map (Int.castRingHom ℚ) = S.rationalCurve := by
  simpa only [curve, rationalCurve, Int.cast_pow] using
    integral_map (S.a ^ p) (S.b ^ p) S.normalization

/-- 非零入力の冪和曲線はℚ上で楕円曲線である。 -/
theorem rationalCurve_isElliptic : S.rationalCurve.IsElliptic := by
  apply normalized_isElliptic
  · exact pow_ne_zero _ (by exact_mod_cast S.a_ne)
  · exact pow_ne_zero _ (by exact_mod_cast S.b_ne)
  · have heq : (S.a : ℚ) ^ p + (S.b : ℚ) ^ p = (S.c : ℚ) ^ p := by
      exact_mod_cast S.equation
    rw [heq]
    exact pow_ne_zero _ (by exact_mod_cast S.c_ne)

/-- GN と整数判別式を結ぶ分母なしの等式。原始性を落とした再構成は行わない。 -/
theorem discriminant_gn (hp : Odd p) :
    256 * S.curve.Δ = (S.a * S.b) ^ (2 * p) *
      ((S.a + S.b) * gnFactor p S.a S.b) ^ 2 :=
  integral_discriminant_gn hp _ _ S.normalization

/-- 奇素数での局所算術の束。ℓ=p でもこの算術的結論までは成立する。 -/
theorem local_arithmetic (hp : 0 < p) {ℓ : ℕ} [Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2)
    (hd : (ℓ : ℤ) ∣ S.a * S.b * S.c) :
    (ℓ : ℤ) ∣ S.curve.Δ ∧ ¬ (ℓ : ℤ) ∣ S.curve.c₄ ∧
      padicValInt ℓ S.curve.Δ = 2 * p * padicValInt ℓ (S.a * S.b * S.c) ∧
      p ∣ padicValInt ℓ S.curve.Δ := by
  exact ⟨(prime_dvd_integral_discriminant_iff hp hℓ2 S.normalization S.equation).mpr hd,
    not_dvd_integral_c4 hp Fact.out S.coprime S.equation S.normalization hd,
    integral_valuation_of_solution hℓ2 S.normalization S.equation S.product_ne_zero,
    exponent_dvd_integral_valuation hℓ2 S.normalization S.equation S.product_ne_zero⟩

/-- 奇素数が abc を割らない時、実際に剰余体へ写したモデルは楕円曲線になる。
最小モデルを選んだと主張せず、このモデルの非特異性だけを述べる。 -/
theorem reduction_isElliptic (hp : 0 < p) {ℓ : ℕ} [Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2)
    (hd : ¬ (ℓ : ℤ) ∣ S.a * S.b * S.c) :
    (S.curve.map (Int.castRingHom (ZMod ℓ))).IsElliptic := by
  constructor
  rw [isUnit_iff_ne_zero, WeierstrassCurve.map_Δ]
  change ((S.curve.Δ : ℤ) : ZMod ℓ) ≠ 0
  intro hz
  exact hd ((prime_dvd_integral_discriminant_iff hp hℓ2 S.normalization S.equation).mp
    ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz))

end Source

/-- 向き付け済みの座標から source を構成する。分母条件は外部へ丸投げしない。
ここでは座標の並べ替えを行わず、入力した原始性と非零性をそのまま保持する。 -/
def ofOriented {p : ℕ} (hp : Odd p) (hp4 : 4 ≤ p) (a b c : ℤ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hab : IsCoprime a b)
    (heq : a ^ p + b ^ p = c ^ p) (ha4 : 4 ∣ a + 1) (hbe : Even b) : Source p where
  a := a
  b := b
  c := c
  a_ne := ha
  b_ne := hb
  c_ne := hc
  coprime := hab
  equation := heq
  normalization := normalization_of_oriented hp hp4 ha4 hbe

end DkMath.FLT.Frey
