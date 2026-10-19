/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.FreyLocalReduction

#print "file: DkMath.FLT.Frey"

/-!
# NOTE-005: 原始冪和から Frey の局所算術へ

この公開入口は四つの段階を混ぜない。
(1) 冪和・非零性・原始性・整数モデルの分母条件を持つ `Source`、
(2) そこから構成した実際の Weierstrass モデルと判別式、
(3) 奇素数ごとの判別式付値と c₄ の可除性、
(4) ℤ_(ℓ) に関する正式な最小性・良還元・乗法的還元、である。

source の整数・共通因子・符号を取り直さず、そのまま保持する。
向き付け済みの整数からの構成は `ofOriented` が分母条件を証明する。
任意の反例の向き付けは `FreyCounterexample`、素数2での最小性は `FreyTwo` で接続する。
mod-p 表現・モジュラー性・レベル降下の供給は、この局所算術とは別の理論である。
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

/-- NOTE-006 §4: abc を割る奇素数では元の有理モデルが乗法的還元を持つ。
Mathlib の定義は全ての整な座標変換に対する最小性を含む。ℓ=p も許すが、
mod-p 表現の有限平坦性・不分岐性まではこの局所定理から推論しない。 -/
theorem hasMultiplicativeReduction (hp : 0 < p) {ℓ : ℕ} [Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2)
    (hd : (ℓ : ℤ) ∣ S.a * S.b * S.c) :
    WeierstrassCurve.HasMultiplicativeReduction (FreyLocalReduction.LocalRing ℓ) S.rationalCurve := by
  rw [← S.curve_map]
  have h := S.local_arithmetic hp hℓ2 hd
  exact FreyLocalReduction.hasMultiplicativeReduction_at_prime ℓ S.curve h.1 h.2.1

/-- abc を割らない奇素数では、最小性を含む正式な良還元が成立する。 -/
theorem hasGoodReduction (hp : 0 < p) {ℓ : ℕ} [Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2)
    (hd : ¬ (ℓ : ℤ) ∣ S.a * S.b * S.c) :
    WeierstrassCurve.HasGoodReduction (FreyLocalReduction.LocalRing ℓ) S.rationalCurve := by
  rw [← S.curve_map]
  exact FreyLocalReduction.hasGoodReduction_at_prime ℓ S.curve
    (fun h => hd ((prime_dvd_integral_discriminant_iff hp hℓ2
      S.normalization S.equation).mp h))

/-- 全ての奇素数で同じ有理モデルが最小。素数ごとに座標を選び直さない。 -/
theorem isMinimal_at_odd_prime (hp : 0 < p) {ℓ : ℕ} [Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2) :
    WeierstrassCurve.IsMinimal (FreyLocalReduction.LocalRing ℓ) S.rationalCurve := by
  by_cases hd : (ℓ : ℤ) ∣ S.a * S.b * S.c
  · exact (S.hasMultiplicativeReduction hp hℓ2 hd).toIsMinimal
  · exact (S.hasGoodReduction hp hℓ2 hd).toIsMinimal

/-- 奇素数での半安定性を、既存の二つの還元型の選言として明記する。 -/
theorem good_or_multiplicative (hp : 0 < p) {ℓ : ℕ} [Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2) :
    WeierstrassCurve.HasGoodReduction (FreyLocalReduction.LocalRing ℓ) S.rationalCurve ∨
      WeierstrassCurve.HasMultiplicativeReduction (FreyLocalReduction.LocalRing ℓ) S.rationalCurve := by
  by_cases hd : (ℓ : ℤ) ∣ S.a * S.b * S.c
  · exact Or.inr (S.hasMultiplicativeReduction hp hℓ2 hd)
  · exact Or.inl (S.hasGoodReduction hp hℓ2 hd)

/-- 奇素数の乗法的還元の支持は正確に abc の素因子支持である。 -/
theorem hasMultiplicativeReduction_iff (hp : 0 < p) {ℓ : ℕ} [Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2) :
    WeierstrassCurve.HasMultiplicativeReduction (FreyLocalReduction.LocalRing ℓ) S.rationalCurve ↔
      (ℓ : ℤ) ∣ S.a * S.b * S.c := by
  constructor
  · intro hm
    by_contra hd
    exact WeierstrassCurve.HasMultiplicativeReduction.not_hasGoodReduction
      (FreyLocalReduction.LocalRing ℓ) hm (S.hasGoodReduction hp hℓ2 hd)
  · exact S.hasMultiplicativeReduction hp hℓ2

/-- 既存の付値式を最小モデル上の等式として確定する。
2での分母補正を無視していないので、ℓ≠2 の前提を残す。 -/
theorem minimal_discriminant_valuation (hp : 0 < p) {ℓ : ℕ} [Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2) :
    WeierstrassCurve.IsMinimal (FreyLocalReduction.LocalRing ℓ) S.rationalCurve ∧
      padicValRat ℓ S.rationalCurve.Δ =
        (2 * p : ℕ) * (padicValInt ℓ (S.a * S.b * S.c) : ℤ) :=
  ⟨S.isMinimal_at_odd_prime hp hℓ2,
    valuation_of_solution_odd hℓ2 S.equation S.product_ne_zero⟩

/-- レベル降下への算術的入力: 最小性と p∣vℓ(Δ) を同じモデル上で束ねる。
この結論は表現の構成やレベル降下定理そのものを含まない。 -/
theorem minimal_discriminant_exponent_dvd (hp : 0 < p) {ℓ : ℕ} [Fact ℓ.Prime]
    (hℓ2 : ℓ ≠ 2) :
    WeierstrassCurve.IsMinimal (FreyLocalReduction.LocalRing ℓ) S.rationalCurve ∧
      (p : ℤ) ∣ padicValRat ℓ S.rationalCurve.Δ := by
  refine ⟨S.isMinimal_at_odd_prime hp hℓ2, ?_⟩
  rw [(S.minimal_discriminant_valuation hp hℓ2).2]
  refine ⟨2 * (padicValInt ℓ (S.a * S.b * S.c) : ℤ), ?_⟩
  push_cast
  ring

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
