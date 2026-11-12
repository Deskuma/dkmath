/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Adapted from anthropics/fermats-last-theorem,
P2M/Sol/S_FreyPackage_freyCurve_rational_p_torsion_eq_zero.lean,
frey_ns00, frey_T0_T0, frey_addX_T0 and the translation in frey_shallow_of_order.
Upstream blob: fe61fd5d4f94d55b5a9da38d1541903c84397df0
Modified for DkMath: arbitrary-field reflection with a1 unrestricted,
point-group involution and doubling, then rational two-adic specialization.
-/

import DkMath.Lib.NumberTheory.EllipticFunctionField
import DkMath.Lib.NumberTheory.RationalTwoAdicBounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

#print "file: DkMath.Lib.NumberTheory.WeierstrassXReflection"

/-!
# NOTE-030-005: 有理2-torsionによるx座標の反射

a₃=a₆=0、a₄≠0のWeierstrassモデルではT=(0,0)は非零2-torsionである。
x(P)≠0なら、実際の点の加法公式からx(P+T)=a₄/x(P)が従う。
この恒等式は任意の体でa₁を制限せずに成立する。元のモデルと座標を保持し、
座標変換を通じてxの意味を変えることはしない。

Tによる平行移動は二回で元に戻り、2(P+T)=2Pを満たす。
しかし奇数nで消えるPについてn(P+T)=Tであり、平行移動はn-torsionを保存しない。
有理数の2進付値ではこの写像がe↦γ−eとなる。上界の算術は次の章で扱う。
-/
namespace DkMath.Lib.NumberTheory.WeierstrassXReflection
open WeierstrassCurve WeierstrassCurve.Affine
variable {K : Type*} [Field K] {W : Affine K}

/-- a₄≠0なら原点は非特異であり、実際の点を構成できる。 -/
theorem origin_nonsingular (h₆ : W.a₆ = 0) (ha₄ : W.a₄ ≠ 0) : W.Nonsingular 0 0 := by
  rw [nonsingular_zero]
  exact ⟨h₆, Or.inr ha₄⟩

/-- 同じモデル上の実際の有限点T=(0,0)。a₃の条件は2-torsion性で用いる。 -/
def twoTorsionPoint (h₆ : W.a₆ = 0) (ha₄ : W.a₄ ≠ 0) : W.Point :=
  Point.some 0 0 (origin_nonsingular h₆ ha₄)

/-- Tは無限遠点ではない。 -/
theorem twoTorsionPoint_ne_zero (h₆ : W.a₆ = 0) (ha₄ : W.a₄ ≠ 0) :
    twoTorsionPoint h₆ ha₄ ≠ 0 := Point.some_ne_zero _

section PointGroup
variable [DecidableEq K]

/-- a₃=0ならTの負の点もTであるため、2T=0となる。 -/
theorem two_nsmul_twoTorsionPoint (h₃ : W.a₃ = 0) (h₆ : W.a₆ = 0) (ha₄ : W.a₄ ≠ 0) :
    2 • twoTorsionPoint h₆ ha₄ = 0 := by
  rw [two_nsmul]
  apply Point.add_self_of_Y_eq
  simp [negY, h₃]

/-- 同じTによる平行移動を二回行うと元の点に戻る。全点で成立し、座標の非零性は不要。 -/
theorem add_twoTorsionPoint_twice (h₃ : W.a₃ = 0) (h₆ : W.a₆ = 0) (ha₄ : W.a₄ ≠ 0)
    (P : W.Point) : (P + twoTorsionPoint h₆ ha₄) + twoTorsionPoint h₆ ha₄ = P := by
  rw [add_assoc, ← two_nsmul, two_nsmul_twoTorsionPoint h₃, add_zero]

/-- 平行移動後の点を元の点の倍点へ戻す等式。P+T自体の奇数torsion性は要求しない。 -/
theorem double_add_twoTorsionPoint (h₃ : W.a₃ = 0) (h₆ : W.a₆ = 0) (ha₄ : W.a₄ ≠ 0)
    (P : W.Point) : 2 • (P + twoTorsionPoint h₆ ha₄) = 2 • P := by
  rw [nsmul_add, two_nsmul_twoTorsionPoint h₃, add_zero]

/-- 奇数nで消える点Pを移動すると、n倍はTになる。従ってn-torsionとは見なせない。 -/
theorem odd_nsmul_add_twoTorsionPoint (h₃ : W.a₃ = 0) (h₆ : W.a₆ = 0) (ha₄ : W.a₄ ≠ 0)
    (P : W.Point) (n : ℕ) (hn : Odd n) (hP : n • P = 0) :
    n • (P + twoTorsionPoint h₆ ha₄) = twoTorsionPoint h₆ ha₄ := by
  rw [nsmul_add, hP, zero_add]
  obtain ⟨k, hk⟩ := hn
  have hk' : n = 2 * k + 1 := by omega
  rw [hk', add_nsmul, mul_nsmul, two_nsmul_twoTorsionPoint h₃,
    nsmul_zero, one_nsmul, zero_add]

/-- 有限点から原点への割線を使い、反射の座標式を証明する。
分母x≠0を明示し、曲線方程式でy²+a₁xyを消去する。a₁=1は不要である。 -/
theorem addX_origin (h₃ : W.a₃ = 0) (h₆ : W.a₆ = 0)
    {x y : K} (h : W.Nonsingular x y) (hx : x ≠ 0) :
    W.addX x 0 (W.slope x 0 y 0) = W.a₄ / x := by
  have heq := (equation_iff x y).mp h.1
  rw [h₃, h₆] at heq
  rw [slope_of_X_ne hx]
  simp only [sub_zero, addX]
  field_simp
  linear_combination heq

/-- 座標の恒等式を、同じ点群のP+Tの実際のx座標として公開する。 -/
theorem add_twoTorsionPoint_x (h₃ : W.a₃ = 0) (h₆ : W.a₆ = 0) (ha₄ : W.a₄ ≠ 0)
    (P : W.Point) (hx : P.xc ≠ 0) :
    (P + twoTorsionPoint h₆ ha₄).xc = W.a₄ / P.xc := by
  cases P with
  | zero => exact (hx rfl).elim
  | some x y h =>
    change x ≠ 0 at hx
    change (Point.some x y h + Point.some 0 0 (origin_nonsingular h₆ ha₄)).xc = W.a₄ / x
    rw [Point.add_of_X_ne hx, Point.xc_some]
    exact addX_origin h₃ h₆ h hx

/-- 反射後のxも非零なのでP+Tは有限点である。原点や無限遠点への退化を除く。 -/
theorem add_twoTorsionPoint_ne_zero (h₃ : W.a₃ = 0) (h₆ : W.a₆ = 0) (ha₄ : W.a₄ ≠ 0)
    (P : W.Point) (hx : P.xc ≠ 0) : P + twoTorsionPoint h₆ ha₄ ≠ 0 := by
  intro hz
  have heq := add_twoTorsionPoint_x h₃ h₆ ha₄ P hx
  rw [hz] at heq
  exact div_ne_zero ha₄ hx heq.symm

end PointGroup

section RationalValuation
open RationalTwoAdicBounds
variable {W : Affine ℚ}

/-- 有理数の2進付値では反射はv₂(x)↦v₂(a₄)−v₂(x)となる。両者の非零性を保持する。 -/
theorem valuation_add_twoTorsionPoint (h₃ : W.a₃ = 0) (h₆ : W.a₆ = 0) (ha₄ : W.a₄ ≠ 0)
    (P : W.Point) (hx : P.xc ≠ 0) :
    padicValRat 2 (P + twoTorsionPoint h₆ ha₄).xc = padicValRat 2 W.a₄ - padicValRat 2 P.xc := by
  rw [add_twoTorsionPoint_x h₃ h₆ ha₄ P hx, padicValRat.div ha₄ hx]

/-- γ,eを正確な付値として与えると、反射後も非零で正確な深さγ−eを持つ。 -/
theorem exact_add_twoTorsionPoint (h₃ : W.a₃ = 0) (h₆ : W.a₆ = 0)
    {γ e : ℤ} (ha₄ : Exact γ W.a₄) (P : W.Point) (hx : Exact e P.xc) :
    Exact (γ - e) (P + twoTorsionPoint h₆ ha₄.1).xc := by
  rw [add_twoTorsionPoint_x h₃ h₆ ha₄.1 P hx.1]
  exact ha₄.div hx

end RationalValuation
end DkMath.Lib.NumberTheory.WeierstrassXReflection
