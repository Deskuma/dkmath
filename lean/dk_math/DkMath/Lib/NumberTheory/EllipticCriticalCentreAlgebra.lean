/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Adapted from anthropics/fermats-last-theorem,
P2M/Sol/S_WeierstrassCurve_exists_criticalCentre_of_multiplicativeReduction.lean,
blob e3a454fddddd39651f2791c4a538ec90c9e926d4.
Modified: split polynomial identities from valuation geometry; retain the characteristic-three
cancellation estimates; use DkMath inertia congruence and odd-prime square-root separation
instead of the general valuation-preserving Galois-orbit argument.
-/

import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Mathlib.Tactic.LinearCombination

#print "file: DkMath.Lib.NumberTheory.EllipticCriticalCentreAlgebra"

/-!
# NOTE-031-002C2: 臨界中心の分母を払った多項式恒等式

F(x,y)=左辺−右辺を用い、Fₓ=Fᵧ=0の中心を作る。
二つの平方根±sは二つの中心候補を与えるが、一般に曲線上の点ではない。
Fの積・差と判別式の関係が、付値環でどちらの候補を選ぶかを決める。
分母12,432,864を単元と仮定しないので、次章では素数3も扱える。
-/
namespace DkMath.Lib.NumberTheory.EllipticCriticalCentreAlgebra
open WeierstrassCurve

section RingIdentities

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- 曲線方程式の左辺−右辺。臨界中心は一般に曲線上の点ではなく、このずれは非零となる。 -/
def equationDefect (x y : R) : R :=
  y ^ 2 + W.a₁ * x * y + W.a₃ * y - (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆)

/-- 平方完成後の三次式。4Fとの和がY方向の一次式の平方になる。 -/
def completedCubic (x : R) : R := 4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆

/-- X方向の臨界条件を平方完成で表す二次式。分母を消したまま扱う。 -/
def criticalQuadratic (x : R) : R := 6 * x ^ 2 + W.b₂ * x + W.b₄

/-- 平方完成の恒等式。整数環上で証明し、2の逆元を要求しない。 -/
theorem complete_square (x y : R) :
    4 * equationDefect W x y + completedCubic W x = (2 * y + W.a₁ * x + W.a₃) ^ 2 := by
  simp only [equationDefect, completedCubic, b₂, b₄, b₆]; ring

/-- 三次式と臨界二次式をc₄で結ぶ。素数3で18を単元扱いしない。 -/
theorem completedCubic_critical_relation (x : R) :
    18 * completedCubic W x = (12 * x + W.b₂) * criticalQuadratic W x - W.c₄ * x + 18 * W.b₆ - W.b₂ * W.b₄ := by
  simp only [completedCubic, criticalQuadratic, c₄]; ring

/-- 二つの偏微分と臨界二次式の関係。 -/
theorem derivative_relation (x y : R) :
    2 * (W.a₁ * y - (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄)) =
      W.a₁ * (2 * y + W.a₁ * x + W.a₃) - criticalQuadratic W x := by
  simp only [criticalQuadratic, b₂, b₄]; ring

/-- 臨界二次式が零なら、b₂+12xはc₄の平方根となる。 -/
theorem node_square_sub_c4 (x : R) : (12 * x + W.b₂) ^ 2 - W.c₄ = 24 * criticalQuadratic W x := by
  simp only [criticalQuadratic, c₄]; ring

end RingIdentities

section Field

variable {L : Type*} [Field L]

/-- c₄の平方根sから作る臨界中心のX候補。分母12の整性は後で付値比較から証明する。 -/
def centreX (W : WeierstrassCurve L) (s : L) : L := (-W.b₂ + s) / 12

/-- 同じX候補からY偏微分を零にするY候補。 -/
def centreY (W : WeierstrassCurve L) (s : L) : L := -(W.a₁ * centreX W s + W.a₃) / 2

variable [CharZero L] (W : WeierstrassCurve L)

/-- X候補の分母を払うと、節点の二次形式に対応する平方根sが戻る。 -/
theorem centreX_relation (s : L) : 12 * centreX W s + W.b₂ = s := by
  simp only [centreX]; field_simp; ring

/-- 節点の二次形式の判別式に現れる量をsと同定する。 -/
theorem node_at_centreX (s : L) : W.b₂ + 12 * centreX W s = s := by
  rw [add_comm]; exact centreX_relation W s

/-- Y方向の偏微分は候補中心で厳密に零になる。剰余体だけの等号ではない。 -/
theorem derivativeY_at_centre (s : L) : 2 * centreY W s + W.a₁ * centreX W s + W.a₃ = 0 := by
  simp only [centreY]; field_simp; ring

/-- s²=c₄なら候補中心は臨界二次式の根である。 -/
theorem criticalQuadratic_at_centre {s : L} (hs : s * s = W.c₄) : criticalQuadratic W (centreX W s) = 0 := by
  have h := node_square_sub_c4 W (centreX W s)
  rw [centreX_relation, sq, hs, sub_self] at h
  have h24 : (24 : L) ≠ 0 := by norm_num
  exact (mul_eq_zero.mp h.symm).resolve_left h24

/-- X方向の偏微分も候補中心で厳密に零になる。 -/
theorem derivativeX_at_centre {s : L} (hs : s * s = W.c₄) :
    W.a₁ * centreY W s - (3 * centreX W s ^ 2 + 2 * W.a₂ * centreX W s + W.a₄) = 0 := by
  have h := derivative_relation W (centreX W s) (centreY W s)
  rw [derivativeY_at_centre, criticalQuadratic_at_centre W hs, mul_zero, sub_zero] at h
  exact (mul_eq_zero.mp h).resolve_left two_ne_zero

/-- 中心でのずれをc₆+c₄sと結ぶ。864は素数2・3で消去せず付値を保持する。 -/
theorem defect_at_centre {s : L} (hs : s * s = W.c₄) : 864 * equationDefect W (centreX W s) (centreY W s) = W.c₆ + W.c₄ * s := by
  have h4 := complete_square W (centreX W s) (centreY W s)
  rw [derivativeY_at_centre] at h4
  have h18 := completedCubic_critical_relation W (centreX W s)
  rw [criticalQuadratic_at_centre W hs, mul_zero] at h18
  have hx : 12 * centreX W s = s - W.b₂ := by
    have := centreX_relation W s; linear_combination this
  simp only [c₄, c₆] at h18 hx ⊢
  linear_combination (216 : L) * h4 - 12 * h18 + (W.b₂ ^ 2 - 24 * W.b₄) * hx

/-- Y候補の平方を、ずれと整なX候補の多項式で表す。整性のモニック二次式に使う。 -/
theorem centreY_square (s : L) :
    centreY W s * centreY W s = -equationDefect W (centreX W s) (centreY W s)
      - (centreX W s ^ 3 + W.a₂ * centreX W s ^ 2 + W.a₄ * centreX W s + W.a₆) := by
  have h := derivativeY_at_centre W s
  simp only [equationDefect]
  linear_combination (centreY W s) * h

/-- 中心Xの整性を、単元c₄とずれの整性から証明するための分母なしの式。 -/
theorem c4_mul_centreX {s : L} (hs : s * s = W.c₄) :
    W.c₄ * centreX W s = 18 * W.b₆ - W.b₂ * W.b₄ + 72 * equationDefect W (centreX W s) (centreY W s) := by
  have h4 := complete_square W (centreX W s) (centreY W s)
  rw [derivativeY_at_centre] at h4
  have h18 := completedCubic_critical_relation W (centreX W s)
  rw [criticalQuadratic_at_centre W hs, mul_zero] at h18
  linear_combination h18 - 18 * h4

/-- 二つの候補のずれの積は−Δ/432。良い候補のずれの深さを決める。 -/
theorem defect_mul_opposite {s : L} (hs : s * s = W.c₄) :
    equationDefect W (centreX W s) (centreY W s) * equationDefect W (centreX W (-s)) (centreY W (-s)) = -W.Δ / 432 := by
  have hs' : -s * -s = W.c₄ := by rw [neg_mul_neg, hs]
  have hG := defect_at_centre W hs
  have hG' := defect_at_centre W hs'
  have hc := W.c_relation
  have hGG : (864 * equationDefect W (centreX W s) (centreY W s)) * (864 * equationDefect W (centreX W (-s)) (centreY W (-s))) =
      (W.c₆ + W.c₄ * s) * (W.c₆ + W.c₄ * -s) := by rw [hG, hG']
  linear_combination (1 / 746496 : L) * hGG + (1 / 746496 : L) * hc - (W.c₄ ^ 2 / 746496) * hs

/-- 二つの候補のずれの差はc₄s/432。積の式と合わせて候補を区別する。 -/
theorem defect_sub_opposite {s : L} (hs : s * s = W.c₄) :
    equationDefect W (centreX W s) (centreY W s) - equationDefect W (centreX W (-s)) (centreY W (-s)) = W.c₄ * s / 432 := by
  have hs' : -s * -s = W.c₄ := by rw [neg_mul_neg, hs]
  have hG := defect_at_centre W hs
  have hG' := defect_at_centre W hs'
  linear_combination (1 / 864 : L) * hG - (1 / 864 : L) * hG'

end Field

/-- 方程式のずれは係数・座標の環準同型による輸送と可換する。
付値環のずれを剰余体へ写し、剰余曲線上の点を得るために使う。 -/
theorem map_equationDefect {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (W : WeierstrassCurve R) (x y : R) :
    equationDefect (W.map f) (f x) (f y) = f (equationDefect W x y) := by
  simp [equationDefect]

/-- 両偏微分が零の中心の周りでは、一次項が消え、二次形式と−X³だけが残る。
この有限なTaylor恒等式は任意の可換環で有効である。 -/
theorem translated_defect {R : Type*} [CommRing R] (W : WeierstrassCurve R)
    (x₀ y₀ X Y : R) (hY : 2 * y₀ + W.a₁ * x₀ + W.a₃ = 0)
    (hX : W.a₁ * y₀ - (3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄) = 0) :
    equationDefect W (x₀ + X) (y₀ + Y) = equationDefect W x₀ y₀ +
      Y ^ 2 + W.a₁ * X * Y - (W.a₂ + 3 * x₀) * X ^ 2 - X ^ 3 := by
  simp only [equationDefect]
  linear_combination Y * hY + X * hX

/-- 二次形式の根α,βがあれば、中心の周りの方程式は二つの枝の積へ因数分解する。
枝の存在・整性・分離は、この環恒等式とは別に証明する。 -/
theorem translated_defect_factor {R : Type*} [CommRing R] (W : WeierstrassCurve R)
    (x₀ y₀ X Y α β : R) (hY : 2 * y₀ + W.a₁ * x₀ + W.a₃ = 0)
    (hX : W.a₁ * y₀ - (3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄) = 0)
    (hs : α + β = -W.a₁) (hp : α * β = -(W.a₂ + 3 * x₀)) :
    equationDefect W (x₀ + X) (y₀ + Y) = equationDefect W x₀ y₀ +
      (Y - α * X) * (Y - β * X) - X ^ 3 := by
  rw [translated_defect W x₀ y₀ X Y hY hX]
  linear_combination X * Y * hs - X ^ 2 * hp

end DkMath.Lib.NumberTheory.EllipticCriticalCentreAlgebra
