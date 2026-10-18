/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
import Mathlib.Algebra.CubicDiscriminant
import Mathlib.Tactic

#print "file: DkMath.Lib.NumberTheory.FreyGapCubic"

/-!
# NOTE-005: 三根の Gap から実際の Frey モデルへ

まず A,B を独立な環の元として扱う。後から A=a^p、B=b^p を代入する。
三根 0,A,−B の差の積は AB(A+B) であり、その平方が三次多項式の判別式。
Weierstrass 方程式 y²=x(x−A)(x+B) の判別式には更に16が掛かる。
両方を Mathlib の実際の定義から計算し、二つの判別式を混同しない。

有理数上では x=4X, y=8Y+4X により係数 a₁=1 のモデルへ移る。
これは u=2,r=0,s=1,t=0 の許容座標変換であり、Δは2⁻¹²倍、c₄は2⁻⁴倍。
整係数モデルに降ろす際は4と16による可除性を明示する。
ここでの「正規化」はこの座標変換を意味し、全素数での最小性は主張しない。
-/

namespace DkMath.Lib.NumberTheory.FreyGapCubic

variable {R : Type*} [CommRing R]

/-- 三根 0,A,−B を持つ三次式。係数を保持する Mathlib の `Cubic` を使う。 -/
def cubic (A B : R) : Cubic R := ⟨1, B - A, -(A * B), 0⟩

/-- 多項式そのものが三つの線形因子の積である。 -/
theorem cubic_factorization (A B : R) :
    (cubic A B).toPoly = Polynomial.X * (Polynomial.X - Polynomial.C A) *
      (Polynomial.X + Polynomial.C B) := by
  simp only [cubic, Cubic.toPoly, Polynomial.C_sub, Polynomial.C_neg, Polynomial.C_mul,
    Polynomial.C_1, Polynomial.C_0]
  ring

/-- 三根の有向差の積。向きの選択は判別式の平方では消える。 -/
theorem root_gap_product (A B : R) :
    (A - 0) * (0 - -B) * (A - -B) = A * B * (A + B) := by ring

/-- 三次式の判別式は三つの Gap の積の平方。 -/
theorem cubic_discriminant (A B : R) :
    (cubic A B).discr = (A * B * (A + B)) ^ 2 := by
  simp only [cubic, Cubic.discr]
  ring

/-- 素朴な Frey 方程式 y²=x(x−A)(x+B) を実際の Weierstrass 係数にする。 -/
def naive (A B : R) : WeierstrassCurve R := ⟨0, B - A, 0, -(A * B), 0⟩

/-- Weierstrass 判別式と三次多項式の判別式の16倍の差を固定する。 -/
theorem naive_discriminant (A B : R) :
    (naive A B).Δ = 16 * (A * B * (A + B)) ^ 2 := by
  simp only [naive, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

/-- 素朴なモデルの c₄ は16(A²+AB+B²)。 -/
theorem naive_c4 (A B : R) : (naive A B).c₄ = 16 * (A ^ 2 + A * B + B ^ 2) := by
  simp only [naive, WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]
  ring

/-- 有理数上で u=2 の座標変換を実際に構成する。整数環では2は単元ではない。 -/
def normalizeChange : WeierstrassCurve.VariableChange ℚ :=
  ⟨Units.mk0 2 (by norm_num), 0, 1, 0⟩

/-- 正規化された有理係数モデル。まだ整係数性は仮定していない。 -/
def normalized (A B : ℚ) : WeierstrassCurve ℚ :=
  ⟨1, (B - A - 1) / 4, 0, -(A * B) / 16, 0⟩

/-- 係数の分母は形式的な置き換えではなく、許容座標変換から生じる。 -/
theorem normalized_eq_change (A B : ℚ) :
    normalized A B = normalizeChange • naive A B := by
  ext <;> norm_num [normalized, normalizeChange, WeierstrassCurve.variableChange_def, naive] <;>
    ring

/-- Δ_norm=2⁻⁸(AB(A+B))²。2⁻¹² と素朴な16の両方を残して計算する。 -/
theorem normalized_discriminant (A B : ℚ) :
    (normalized A B).Δ = (A * B * (A + B)) ^ 2 / 256 := by
  rw [normalized_eq_change, WeierstrassCurve.variableChange_Δ, naive_discriminant]
  norm_num [normalizeChange]
  ring

/-- 正規化された c₄=A²+AB+B²。 -/
theorem normalized_c4 (A B : ℚ) :
    (normalized A B).c₄ = A ^ 2 + A * B + B ^ 2 := by
  rw [normalized_eq_change, WeierstrassCurve.variableChange_c₄, naive_c4]
  norm_num [normalizeChange]
  ring

/-- 非零の三つの Gap により有理数上で本当の楕円曲線になる。
零入力を排除する前提を型クラス化して隠さず、定理の引数に保持する。 -/
theorem normalized_isElliptic (A B : ℚ) (hA : A ≠ 0) (hB : B ≠ 0)
    (hAB : A + B ≠ 0) : (normalized A B).IsElliptic := by
  constructor
  rw [isUnit_iff_ne_zero, normalized_discriminant]
  exact div_ne_zero (pow_ne_zero _ (mul_ne_zero (mul_ne_zero hA hB) hAB)) (by norm_num)

/-- 整数モデルを正当化する最小限の分母条件。原始性とは別の条件である。 -/
structure IntegralNormalization (A B : ℤ) : Prop where
  four : 4 ∣ B - A - 1
  sixteen : 16 ∣ A * B

/-- 整係数モデル。整数除算は条件付きの比較定理でだけ有理数除算と同一視する。 -/
def integral (A B : ℤ) : WeierstrassCurve ℤ :=
  ⟨1, (B - A - 1) / 4, 0, -(A * B / 16), 0⟩

/-- 分母条件の下で、整数モデルをℚへ写すと正規化モデルそのものになる。 -/
theorem integral_map (A B : ℤ) (h : IntegralNormalization A B) :
    (integral A B).map (Int.castRingHom ℚ) = normalized (A : ℚ) (B : ℚ) := by
  refine WeierstrassCurve.ext rfl ?_ rfl ?_ rfl
  · change (((B - A - 1) / 4 : ℤ) : ℚ) = ((B : ℚ) - A - 1) / 4
    rw [Int.cast_div h.four (by norm_num : (4 : ℚ) ≠ 0)]
    push_cast
    rfl
  · change ((-(A * B / 16) : ℤ) : ℚ) = -((A : ℚ) * B) / 16
    rw [Int.cast_neg, Int.cast_div h.sixteen (by norm_num : (16 : ℚ) ≠ 0)]
    push_cast
    ring

/-- 整数係数の c₄ の式。分母条件を使って実際のモデルから導く。 -/
theorem integral_c4 (A B : ℤ) (h : IntegralNormalization A B) :
    (integral A B).c₄ = A ^ 2 + A * B + B ^ 2 := by
  have hc := congrArg WeierstrassCurve.c₄ (integral_map A B h)
  rw [WeierstrassCurve.map_c₄, normalized_c4] at hc
  change ((integral A B).c₄ : ℚ) = (A : ℚ) ^ 2 + (A : ℚ) * B + (B : ℚ) ^ 2 at hc
  exact_mod_cast hc

/-- 分母を払った整数判別式の保存則。整数で256を逆元として使わない。 -/
theorem integral_discriminant (A B : ℤ) (h : IntegralNormalization A B) :
    256 * (integral A B).Δ = (A * B * (A + B)) ^ 2 := by
  have hd := congrArg WeierstrassCurve.Δ (integral_map A B h)
  rw [WeierstrassCurve.map_Δ, normalized_discriminant] at hd
  change ((integral A B).Δ : ℚ) = ((A : ℚ) * B * (A + B)) ^ 2 / 256 at hd
  have he : (256 : ℚ) * ((integral A B).Δ : ℚ) =
      ((A : ℚ) * B * (A + B)) ^ 2 := by rw [hd]; ring
  exact_mod_cast he

end DkMath.Lib.NumberTheory.FreyGapCubic
