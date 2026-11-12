/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Doubling polynomial informed by S_WeierstrassCurve_slope_mem_of_shallow,
blob 0b9d8a2eb9bfd9e038a8a875189907fdafd76f58, S04_dbl_core and S04_dbl_ident.
Modified: same DkMath centre over arbitrary field; actual Point doubling witness;
valuation bounds retain the cancellation threshold instead of assuming distinct valuations.
-/

import DkMath.Lib.NumberTheory.EllipticCriticalDepth

#print "file: DkMath.Lib.NumberTheory.EllipticDoublingDepth"

/-!
# NOTE-031-002C6a: 同じ浅い点の実際の倍点の深さ

X=x−C.x、F₀=F(C.x,C.y)、Ψ=2y+a₁x+a₃とすると、
(x(2P)−C.x)Ψ²=X⁴+8F₀X+(b₂+12C.x)F₀である。
浅い点ではv(Ψ)=v(X)を既存の反対傾きの分離から供給する。
F₀とX⁴の付値が異なれば最大値則、等しければ上界だけを使う。
有限座標を仮想的に割り当てず、実際の点群で2Pが有限点である証明も返す。
これだけで奇数torsionの全倍点の有限軌道を構成したとはしない。
-/
namespace DkMath.Lib.NumberTheory.EllipticDoublingDepth
open WeierstrassCurve EllipticCriticalCentre EllipticCriticalCentreAlgebra EllipticShallowSlope EllipticCriticalDepth
variable {L : Type*} [Field L] {A : ValuationSubring L} {W : WeierstrassCurve L}

private theorem doubling_polynomial (x y x₀ y₀ a₁ a₂ a₆ : L)
    (heqn : y ^ 2 + a₁ * x * y + (-2 * y₀ - a₁ * x₀) * y =
      x ^ 3 + a₂ * x ^ 2 + (a₁ * y₀ - 3 * x₀ ^ 2 - 2 * a₂ * x₀) * x + a₆) :
    (3 * x ^ 2 + 2 * a₂ * x + (a₁ * y₀ - 3 * x₀ ^ 2 - 2 * a₂ * x₀) - a₁ * y) ^ 2
      + a₁ * (3 * x ^ 2 + 2 * a₂ * x + (a₁ * y₀ - 3 * x₀ ^ 2 - 2 * a₂ * x₀) - a₁ * y)
          * (2 * y + a₁ * x + (-2 * y₀ - a₁ * x₀))
      - (a₂ + 2 * x + x₀) * (2 * y + a₁ * x + (-2 * y₀ - a₁ * x₀)) ^ 2
    = (x - x₀) ^ 4
      + 8 * (y₀ ^ 2 + a₁ * x₀ * y₀ + (-2 * y₀ - a₁ * x₀) * y₀
          - (x₀ ^ 3 + a₂ * x₀ ^ 2 + (a₁ * y₀ - 3 * x₀ ^ 2 - 2 * a₂ * x₀) * x₀ + a₆)) * (x - x₀)
      + (a₁ ^ 2 + 4 * a₂ + 12 * x₀)
        * (y₀ ^ 2 + a₁ * x₀ * y₀ + (-2 * y₀ - a₁ * x₀) * y₀
          - (x₀ ^ 3 + a₂ * x₀ ^ 2 + (a₁ * y₀ - 3 * x₀ ^ 2 - 2 * a₂ * x₀) * x₀ + a₆)) := by
  linear_combination (-(a₁ ^ 2 + 4 * a₂ + 12 * x₀) - 8 * (x - x₀)) * heqn

/-- 同じ中心での分母を払った倍点恒等式。接線分母非零を先に要求し、零除算へ意味を与えない。 -/
theorem doubling_identity [DecidableEq L] (C : CriticalCentre A W) {x y : L}
    (h : W.toAffine.Equation x y) (hΨ : tangentDenominator W x y ≠ 0) :
    (W.toAffine.addX x x (W.toAffine.slope x x y y) - C.x) * tangentDenominator W x y ^ 2 =
      (x - C.x) ^ 4 + 8 * equationDefect W C.x C.y * (x - C.x) +
        (W.b₂ + 12 * C.x) * equationDefect W C.x C.y := by
  have ha₃ : W.a₃ = -2 * C.y - W.a₁ * C.x := by linear_combination C.derivativeY
  have ha₄ : W.a₄ = W.a₁ * C.y - 3 * C.x ^ 2 - 2 * W.a₂ * C.x := by linear_combination -C.derivativeX
  have hy : y ≠ W.toAffine.negY x y := by
    intro he
    apply hΨ
    dsimp only [tangentDenominator, Affine.negY] at *
    linear_combination he
  have hd : y - W.toAffine.negY x y = tangentDenominator W x y := by
    dsimp only [Affine.negY, tangentDenominator]
    ring
  rw [Affine.slope_of_Y_ne rfl hy, hd]
  rw [Affine.equation_iff] at h
  change y ^ 2 + W.a₁ * x * y + W.a₃ * y = x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆ at h
  simp only [Affine.addX, tangentDenominator, equationDefect, b₂] at *
  dsimp only [WeierstrassCurve.toAffine] at *
  rw [ha₃] at hΨ
  rw [ha₃, ha₄] at h ⊢
  set N := 3 * x ^ 2 + 2 * W.a₂ * x + (W.a₁ * C.y - 3 * C.x ^ 2 - 2 * W.a₂ * C.x) - W.a₁ * y
  set D := 2 * y + W.a₁ * x + (-2 * C.y - W.a₁ * C.x)
  have hND : N / D * D = N := div_mul_cancel₀ N hΨ
  have hk : ((N / D) ^ 2 + W.a₁ * (N / D) - W.a₂ - x - x - C.x) * D ^ 2 =
      N ^ 2 + W.a₁ * N * D - (W.a₂ + 2 * x + C.x) * D ^ 2 := by
    calc _ = (N / D * D) ^ 2 + W.a₁ * (N / D * D) * D - (W.a₂ + 2 * x + C.x) * D ^ 2 := by ring
      _ = _ := by rw [hND]
  rw [hk]
  exact doubling_polynomial x y C.x C.y W.a₁ W.a₂ W.a₆ h

/-- 倍点分子の付値の上界と、二主項の付値が異なる場合の等式。
等しい付値では相殺があり得るので、最大値との等号を主張しない。 -/
theorem doubling_numerator_valuation (C : CriticalCentre A W) {x : L}
    (hX : A.valuation (x - C.x) < 1) :
    A.valuation ((x - C.x) ^ 4 + 8 * equationDefect W C.x C.y * (x - C.x) +
      (W.b₂ + 12 * C.x) * equationDefect W C.x C.y) ≤
        max (A.valuation (x - C.x) ^ 4) (A.valuation (equationDefect W C.x C.y)) ∧
    (A.valuation (equationDefect W C.x C.y) ≠ A.valuation (x - C.x) ^ 4 →
      A.valuation ((x - C.x) ^ 4 + 8 * equationDefect W C.x C.y * (x - C.x) +
        (W.b₂ + 12 * C.x) * equationDefect W C.x C.y) =
          max (A.valuation (x - C.x) ^ 4) (A.valuation (equationDefect W C.x C.y))) := by
  have hsmall : A.valuation (8 * equationDefect W C.x C.y * (x - C.x)) <
      A.valuation (equationDefect W C.x C.y) := by
    rw [map_mul, map_mul]
    calc A.valuation (8 : L) * A.valuation (equationDefect W C.x C.y) * A.valuation (x - C.x)
        ≤ A.valuation (equationDefect W C.x C.y) * A.valuation (x - C.x) := by
          exact mul_le_mul' (mul_le_of_le_one_left' ((A.valuation_le_one_iff _).mpr (ofNat_mem A 8))) le_rfl
      _ < A.valuation (equationDefect W C.x C.y) * 1 :=
        mul_lt_mul_of_pos_left hX ((Valuation.pos_iff _).mpr C.defect_ne_zero)
      _ = _ := mul_one _
  have htail : A.valuation (8 * equationDefect W C.x C.y * (x - C.x) +
      (W.b₂ + 12 * C.x) * equationDefect W C.x C.y) = A.valuation (equationDefect W C.x C.y) := by
    have hn : A.valuation ((W.b₂ + 12 * C.x) * equationDefect W C.x C.y) =
        A.valuation (equationDefect W C.x C.y) := by rw [map_mul, C.node_unit, one_mul]
    rw [Valuation.map_add_eq_of_lt_right _ (hsmall.trans_eq hn.symm), hn]
  rw [add_assoc]
  constructor
  · have hb := A.valuation.map_add ((x - C.x) ^ 4)
      (8 * equationDefect W C.x C.y * (x - C.x) + (W.b₂ + 12 * C.x) * equationDefect W C.x C.y)
    rw [map_pow, htail] at hb
    exact hb
  · intro hne
    rw [Valuation.map_add_of_distinct_val _ (by rw [map_pow, htail]; exact hne.symm), map_pow, htail]

/-- 浅い実際の点の2倍は有限点であり、そのX深さは分子の最大値則に従う。
F<v(X)⁴なら深さが平方になり、v(X)⁴<FならN·v(X)²=Fとなる。
相殺の閾値F=v(X)⁴では上界だけを返す。全て同じ点の実際の2倍として構成する。 -/
theorem doubling_depth [DecidableEq L] (C : CriticalCentre A W) {x y : L}
    (h : W.toAffine.Nonsingular x y) (hX : A.valuation (x - C.x) < 1)
    (hsh : A.valuation (equationDefect W C.x C.y) < A.valuation (x - C.x) ^ 2) :
    ∃ (x₂ y₂ : L) (h₂ : W.toAffine.Nonsingular x₂ y₂),
      2 • Affine.Point.some x y h = Affine.Point.some x₂ y₂ h₂ ∧
      A.valuation (x₂ - C.x) * A.valuation (x - C.x) ^ 2 ≤
        max (A.valuation (x - C.x) ^ 4) (A.valuation (equationDefect W C.x C.y)) ∧
      (A.valuation (equationDefect W C.x C.y) < A.valuation (x - C.x) ^ 4 →
        A.valuation (x₂ - C.x) = A.valuation (x - C.x) ^ 2) ∧
      (A.valuation (x - C.x) ^ 4 < A.valuation (equationDefect W C.x C.y) →
        A.valuation (x₂ - C.x) * A.valuation (x - C.x) ^ 2 = A.valuation (equationDefect W C.x C.y)) := by
  have hvΨ := shallow_denominator_valuation C h.1 hX hsh
  have hΨ : tangentDenominator W x y ≠ 0 := by
    intro hz
    rw [hz, map_zero] at hvΨ
    exact shallow_x_ne C hsh ((Valuation.zero_iff _).mp hvΨ.symm)
  have hy : y ≠ W.toAffine.negY x y := by
    intro he
    apply hΨ
    dsimp only [tangentDenominator, Affine.negY] at *
    linear_combination he
  have hid := congrArg A.valuation (doubling_identity C h.1 hΨ)
  rw [map_mul, map_pow, hvΨ] at hid
  obtain ⟨hbound, hexact⟩ := doubling_numerator_valuation C hX
  have hxx : A.valuation (x - C.x) ^ 2 ≠ 0 :=
    pow_ne_zero 2 ((Valuation.ne_zero_iff _).mpr (shallow_x_ne C hsh))
  refine ⟨_, _, Affine.nonsingular_add h h (fun he => hy he.2), ?_, hid.trans_le hbound, ?_, ?_⟩
  · rw [two_nsmul, Affine.Point.add_self_of_Y_ne hy]
  · intro hlt
    apply mul_right_cancel₀ hxx
    rw [hid, hexact hlt.ne, max_eq_left hlt.le, ← pow_add]
  · intro hgt
    rw [hid, hexact hgt.ne.symm, max_eq_right hgt.le]

end DkMath.Lib.NumberTheory.EllipticDoublingDepth
