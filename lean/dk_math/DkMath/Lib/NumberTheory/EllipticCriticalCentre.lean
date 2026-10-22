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

import DkMath.Lib.NumberTheory.EllipticCriticalCentreAlgebra
import DkMath.Lib.NumberTheory.ValuationPrimeSupport
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic

#print "file: DkMath.Lib.NumberTheory.EllipticCriticalCentre"

/-!
# NOTE-031-002C2: 乗法的還元の臨界中心を付値環に作る

s²=c₄の二つの候補のうち、Fの付値が小さい側を選ぶ。
v(c₄)=1、v(Δ)<1のとき、積と差の恒等式からv(F)=v(Δ)が従う。
この等式で中心の座標の整性を証明するため、分母12が単元でない素数3にも通る。
中心は曲線上の点ではなく、両偏微分が零で、Fが小さい非零値となる点である。
-/
namespace DkMath.Lib.NumberTheory.EllipticCriticalCentre
open WeierstrassCurve EllipticCriticalCentreAlgebra

section Valuation

variable {L : Type*} [Field L] (A : ValuationSubring L)

private theorem val_eq_one_of_mul_self {g : A.ValueGroup} (h : g * g = 1) : g = 1 :=
  (pow_eq_one_iff_left two_ne_zero).mp (by rw [sq]; exact h)

private theorem mem_of_monic_quadratic {a b z : L} (ha : a ∈ A) (hb : b ∈ A)
    (hz : z * z + a * z + b = 0) : z ∈ A := by
  by_contra hzA
  have hz1 : 1 < A.valuation z :=
    lt_of_not_ge fun h => hzA ((A.valuation_le_one_iff z).mp h)
  have hz0 : 0 < A.valuation z := lt_trans zero_lt_one hz1
  have hzz : A.valuation z < A.valuation (z * z) := by
    rw [Valuation.map_mul]
    calc A.valuation z = A.valuation z * 1 := (mul_one _).symm
      _ < A.valuation z * A.valuation z := mul_lt_mul_of_pos_left hz1 hz0
  have h1 : A.valuation (a * z) < A.valuation (z * z) := by
    refine lt_of_le_of_lt ?_ hzz
    rw [Valuation.map_mul]
    calc A.valuation a * A.valuation z ≤ 1 * A.valuation z :=
          mul_le_mul' ((A.valuation_le_one_iff a).mpr ha) le_rfl
      _ = A.valuation z := one_mul _
  have h2 : A.valuation b < A.valuation (z * z) :=
    lt_of_le_of_lt ((A.valuation_le_one_iff b).mpr hb) (hz1.trans hzz)
  have h3 : A.valuation (z * z + (a * z + b)) = A.valuation (z * z) :=
    Valuation.map_add_eq_of_lt_left _ (Valuation.map_add_lt _ h1 h2)
  rw [← add_assoc, hz, Valuation.map_zero] at h3
  exact (ne_of_lt (lt_trans hz0 hzz)) h3

private theorem val_ofNat (n : ℕ) [n.AtLeastTwo] (hn : (OfNat.ofNat n : L) ≠ 0) :
    A.valuation (OfNat.ofNat n : L) ≤ 1 ∧ A.valuation (OfNat.ofNat n : L) ≠ 0 ∧
      0 < A.valuation (OfNat.ofNat n : L) :=
  ⟨(A.valuation_le_one_iff _).mpr (ofNat_mem A n), (Valuation.ne_zero_iff _).mpr hn,
    (Valuation.pos_iff _).mpr hn⟩

private theorem b_mem (W : WeierstrassCurve L) (h₁ : W.a₁ ∈ A) (h₂ : W.a₂ ∈ A) (h₃ : W.a₃ ∈ A)
    (h₄ : W.a₄ ∈ A) (h₆ : W.a₆ ∈ A) : W.b₂ ∈ A ∧ W.b₄ ∈ A ∧ W.b₆ ∈ A := by
  let WA : WeierstrassCurve A := ⟨⟨_, h₁⟩, ⟨_, h₂⟩, ⟨_, h₃⟩, ⟨_, h₄⟩, ⟨_, h₆⟩⟩
  have hmap : WA.map A.subtype = W := rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [← hmap, map_b₂]; exact SetLike.coe_mem _
  · rw [← hmap, map_b₄]; exact SetLike.coe_mem _
  · rw [← hmap, map_b₆]; exact SetLike.coe_mem _

end Valuation

section Main
variable {L : Type*} [Field L] [CharZero L] (A : ValuationSubring L) (W : WeierstrassCurve L)

local notation "v" => ValuationSubring.valuation A

section Core

variable (hΔ : W.Δ ≠ 0) (hvΔ : A.valuation W.Δ < 1) (hc₄ : A.valuation W.c₄ = 1)
  {s : L} (hs : s * s = W.c₄)

omit [CharZero L] in
include hc₄ hs in
private theorem val_s : v s = 1 := by
  apply val_eq_one_of_mul_self A
  rw [← Valuation.map_mul, hs, hc₄]

include hc₄ hs in
private theorem val_F_sub_F :
    v (equationDefect W (centreX W s) (centreY W s) - equationDefect W (centreX W (-s)) (centreY W (-s))) = (v (432 : L))⁻¹ := by
  rw [defect_sub_opposite W hs, map_div₀, Valuation.map_mul, hc₄, val_s A W hc₄ hs, one_mul, one_div]

include hs in
private theorem val_F_mul_F :
    v (equationDefect W (centreX W s) (centreY W s)) * v (equationDefect W (centreX W (-s)) (centreY W (-s))) = v W.Δ * (v (432 : L))⁻¹ := by
  rw [← Valuation.map_mul, defect_mul_opposite W hs, map_div₀, Valuation.map_neg, div_eq_mul_inv]

include hΔ hs in
private theorem F_ne_zero : equationDefect W (centreX W s) (centreY W s) ≠ 0 := by
  have h0 : (432 : L) ≠ 0 := by norm_num
  have h : equationDefect W (centreX W s) (centreY W s) * equationDefect W (centreX W (-s)) (centreY W (-s)) ≠ 0 := by
    rw [defect_mul_opposite W hs]; exact div_ne_zero (neg_ne_zero.mpr hΔ) h0
  exact left_ne_zero_of_mul h

variable (hle : A.valuation (equationDefect W (centreX W s) (centreY W s)) ≤ A.valuation (equationDefect W (centreX W (-s)) (centreY W (-s))))

include hc₄ hs hle in
private theorem one_le_val_F' : (v (432 : L))⁻¹ ≤ v (equationDefect W (centreX W (-s)) (centreY W (-s))) ∧
    1 ≤ v (equationDefect W (centreX W (-s)) (centreY W (-s))) := by
  obtain ⟨hle1, -, hpos⟩ := val_ofNat A 432 (by norm_num)
  have h : (v (432 : L))⁻¹ ≤ v (equationDefect W (centreX W (-s)) (centreY W (-s))) := by
    calc (v (432 : L))⁻¹ = v (equationDefect W (centreX W s) (centreY W s) - equationDefect W (centreX W (-s)) (centreY W (-s))) :=
          (val_F_sub_F A W hc₄ hs).symm
      _ ≤ max (v (equationDefect W (centreX W s) (centreY W s))) (v (equationDefect W (centreX W (-s)) (centreY W (-s)))) :=
          Valuation.map_sub _ _ _
      _ = v (equationDefect W (centreX W (-s)) (centreY W (-s))) := max_eq_right hle
  exact ⟨h, le_trans ((one_le_inv₀ hpos).mpr hle1) h⟩

include hc₄ hs hvΔ hle in
private theorem val_F_eq : v (equationDefect W (centreX W s) (centreY W s)) = v W.Δ := by
  obtain ⟨hle1, hne, hpos⟩ := val_ofNat A 432 (by norm_num)
  obtain ⟨h', -⟩ := one_le_val_F' A W hc₄ hs hle
  have hprod := val_F_mul_F A W hs
  have hle' : v (equationDefect W (centreX W s) (centreY W s)) ≤ v W.Δ := by
    have h1 : v (equationDefect W (centreX W s) (centreY W s)) * (v (432 : L))⁻¹ ≤
        v (equationDefect W (centreX W s) (centreY W s)) * v (equationDefect W (centreX W (-s)) (centreY W (-s))) := mul_le_mul' le_rfl h'
    rw [hprod] at h1
    have h2 : v (equationDefect W (centreX W s) (centreY W s)) * (v (432 : L))⁻¹ * v (432 : L) ≤
        v W.Δ * (v (432 : L))⁻¹ * v (432 : L) := mul_le_mul' h1 le_rfl
    rwa [inv_mul_cancel_right₀ hne, inv_mul_cancel_right₀ hne] at h2
  have hlt : v (equationDefect W (centreX W s) (centreY W s)) <
      v (equationDefect W (centreX W s) (centreY W s) - equationDefect W (centreX W (-s)) (centreY W (-s))) := by
    rw [val_F_sub_F A W hc₄ hs]
    exact lt_of_le_of_lt hle' (lt_of_lt_of_le hvΔ ((one_le_inv₀ hpos).mpr hle1))
  have heq : v (equationDefect W (centreX W (-s)) (centreY W (-s))) = (v (432 : L))⁻¹ := by
    have := Valuation.map_sub_eq_of_lt_right _ hlt
    rwa [sub_sub_cancel, val_F_sub_F A W hc₄ hs] at this
  rw [heq] at hprod
  exact mul_right_cancel₀ (inv_ne_zero hne) hprod

include hc₄ hs hvΔ hle in
private theorem val_F_lt_one : v (equationDefect W (centreX W s) (centreY W s)) < 1 := by
  rw [val_F_eq A W hvΔ hc₄ hs hle]; exact hvΔ

variable (h₁ : W.a₁ ∈ A) (h₂ : W.a₂ ∈ A) (h₃ : W.a₃ ∈ A) (h₄ : W.a₄ ∈ A) (h₆ : W.a₆ ∈ A)

include h₁ h₂ h₃ h₄ h₆ hvΔ hc₄ hs hle in
private theorem cx_mem : centreX W s ∈ A := by
  obtain ⟨hb₂, hb₄, hb₆⟩ := b_mem A W h₁ h₂ h₃ h₄ h₆
  have hG : equationDefect W (centreX W s) (centreY W s) ∈ A :=
    (A.valuation_le_one_iff _).mp (le_of_lt (val_F_lt_one A W hvΔ hc₄ hs hle))
  have hN : 18 * W.b₆ - W.b₂ * W.b₄ + 72 * equationDefect W (centreX W s) (centreY W s) ∈ A :=
    add_mem (sub_mem (mul_mem (ofNat_mem A 18) hb₆) (mul_mem hb₂ hb₄))
      (mul_mem (ofNat_mem A 72) hG)
  rw [← A.valuation_le_one_iff] at hN ⊢
  have h := congrArg (ValuationSubring.valuation A) (c4_mul_centreX W hs)
  rw [Valuation.map_mul, hc₄, one_mul] at h
  rw [h]; exact hN

include h₁ h₂ h₃ h₄ h₆ hvΔ hc₄ hs hle in
private theorem cy_mem : centreY W s ∈ A := by
  have hx := cx_mem A W hvΔ hc₄ hs hle h₁ h₂ h₃ h₄ h₆
  have hG : equationDefect W (centreX W s) (centreY W s) ∈ A :=
    (A.valuation_le_one_iff _).mp (le_of_lt (val_F_lt_one A W hvΔ hc₄ hs hle))
  refine mem_of_monic_quadratic A (zero_mem A)
    (b := equationDefect W (centreX W s) (centreY W s) + (centreX W s ^ 3 + W.a₂ * centreX W s ^ 2 + W.a₄ * centreX W s + W.a₆))
    (add_mem hG (add_mem (add_mem (add_mem (pow_mem hx 3) (mul_mem h₂ (pow_mem hx 2)))
      (mul_mem h₄ hx)) h₆)) ?_
  have h := centreY_square W s
  linear_combination h


end Core

omit [CharZero L] in
private theorem exists_sign [IsAlgClosed L] :
    ∃ s : L, s * s = W.c₄ ∧ v (equationDefect W (centreX W s) (centreY W s)) ≤ v (equationDefect W (centreX W (-s)) (centreY W (-s))) := by
  obtain ⟨s₀, hs₀⟩ := IsAlgClosed.exists_eq_mul_self W.c₄
  rcases le_total (v (equationDefect W (centreX W s₀) (centreY W s₀))) (v (equationDefect W (centreX W (-s₀)) (centreY W (-s₀)))) with h | h
  · exact ⟨s₀, hs₀.symm, h⟩
  · exact ⟨-s₀, by rw [neg_mul_neg, hs₀], by rw [neg_neg]; exact h⟩

end Main

/-- 同じ一般ファイバーの臨界中心。
座標の整性、両偏微分の厳密な零、非退化な二次項、非零のずれと判別式の深さを同時に保持する。
これは曲線の点ではなく、特異な剰余点に対応する付値環内の中心である。 -/
structure CriticalCentre {L : Type*} [Field L] (A : ValuationSubring L) (W : WeierstrassCurve L) where
  /-- 同じモデルのX座標。 -/
  x : L
  /-- 同じモデルのY座標。 -/
  y : L
  /-- X座標は付値環に入る。 -/
  x_mem : x ∈ A
  /-- Y座標は付値環に入る。 -/
  y_mem : y ∈ A
  /-- Y方向の偏微分は零。 -/
  derivativeY : 2 * y + W.a₁ * x + W.a₃ = 0
  /-- X方向の偏微分は零。 -/
  derivativeX : W.a₁ * y - (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄) = 0
  /-- 二次項の判別式は単元。 -/
  node_unit : A.valuation (W.b₂ + 12 * x) = 1
  /-- 中心は一般ファイバー上の点ではない。 -/
  defect_ne_zero : equationDefect W x y ≠ 0
  /-- ずれは剰余体で零となる。 -/
  defect_small : A.valuation (equationDefect W x y) < 1
  /-- ずれの深さは同じ判別式の深さと厳密に一致する。 -/
  defect_valuation : A.valuation (equationDefect W x y) = A.valuation W.Δ

/-- 整係数・非零判別式・v(Δ)<1・v(c₄)=1から臨界中心を構成する。
二候補のずれの積と差を比較するので、剰余標数2や3をここでは除外しない。
付値の離散性・完備性や、中心の存在providerを仮定しない。 -/
theorem exists_criticalCentre {L : Type*} [Field L] [CharZero L] [IsAlgClosed L]
    (A : ValuationSubring L) (W : WeierstrassCurve L)
    (h₁ : W.a₁ ∈ A) (h₂ : W.a₂ ∈ A) (h₃ : W.a₃ ∈ A) (h₄ : W.a₄ ∈ A) (h₆ : W.a₆ ∈ A)
    (hΔ : W.Δ ≠ 0) (hvΔ : A.valuation W.Δ < 1) (hc₄ : A.valuation W.c₄ = 1) :
    Nonempty (CriticalCentre A W) := by
  obtain ⟨s, hs, hle⟩ := exists_sign A W
  refine ⟨{
    x := centreX W s
    y := centreY W s
    x_mem := cx_mem A W hvΔ hc₄ hs hle h₁ h₂ h₃ h₄ h₆
    y_mem := cy_mem A W hvΔ hc₄ hs hle h₁ h₂ h₃ h₄ h₆
    derivativeY := derivativeY_at_centre W s
    derivativeX := derivativeX_at_centre W hs
    node_unit := ?_
    defect_ne_zero := F_ne_zero W hΔ hs
    defect_small := val_F_lt_one A W hvΔ hc₄ hs hle
    defect_valuation := val_F_eq A W hvΔ hc₄ hs hle }⟩
  rw [node_at_centreX]
  exact val_s A W hc₄ hs

namespace CriticalCentre
variable {L : Type*} [Field L] {A : ValuationSubring L} {W : WeierstrassCurve L}

/-- 両偏微分の零から、中心の二次項の判別式の平方はc₄と一致する。 -/
theorem node_square (C : CriticalCentre A W) : (W.b₂ + 12 * C.x) * (W.b₂ + 12 * C.x) = W.c₄ := by
  have h := derivative_relation W C.x C.y
  rw [C.derivativeX, C.derivativeY, mul_zero, mul_zero, zero_sub] at h
  have hr : criticalQuadratic W C.x = 0 := neg_eq_zero.mp h.symm
  have he := node_square_sub_c4 W C.x
  rw [hr, mul_zero, sub_eq_zero] at he
  simpa only [add_comm, sq] using he

/-- 平行移動後の方程式は、中心の同じずれと節点の二次形式・三次項へ分解する。 -/
theorem translated_equation (C : CriticalCentre A W) (X Y : L) :
    equationDefect W (C.x + X) (C.y + Y) = equationDefect W C.x C.y +
      Y ^ 2 + W.a₁ * X * Y - (W.a₂ + 3 * C.x) * X ^ 2 - X ^ 3 :=
  translated_defect W C.x C.y X Y C.derivativeY C.derivativeX

/-- 同じ整モデルの中心は、剰余曲線上の実際の特異点へ還元する。
中心自体はF≠0のため一般ファイバーの点ではないが、v(F)<1なので剰余方程式を満たす。 -/
theorem residue_singular (V : WeierstrassCurve A) (C : CriticalCentre A (V.map A.subtype)) :
    let xr := IsLocalRing.residue A (⟨C.x, C.x_mem⟩ : A)
    let yr := IsLocalRing.residue A (⟨C.y, C.y_mem⟩ : A)
    (V.map (IsLocalRing.residue A)).toAffine.Equation xr yr ∧
      ¬ (V.map (IsLocalRing.residue A)).toAffine.Nonsingular xr yr := by
  let x : A := ⟨C.x, C.x_mem⟩
  let y : A := ⟨C.y, C.y_mem⟩
  have hF : ((equationDefect V x y : A) : L) = equationDefect (V.map A.subtype) C.x C.y :=
    (map_equationDefect A.subtype V x y).symm
  have hzero : IsLocalRing.residue A (equationDefect V x y) = 0 := by
    apply (IsLocalRing.residue_eq_zero_iff _).mpr
    apply ValuationSubring.coe_mem_nonunits_iff.mp
    rw [ValuationSubring.mem_nonunits_iff, hF]
    exact C.defect_small
  have hYA : 2 * y + V.a₁ * x + V.a₃ = 0 := by
    apply Subtype.ext
    exact C.derivativeY
  have hXA : V.a₁ * y - (3 * x ^ 2 + 2 * V.a₂ * x + V.a₄) = 0 := by
    apply Subtype.ext
    exact C.derivativeX
  have hY := congrArg (IsLocalRing.residue A) hYA
  have hX := congrArg (IsLocalRing.residue A) hXA
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat, map_zero] at hY hX
  have hEq : (V.map (IsLocalRing.residue A)).toAffine.Equation
      (IsLocalRing.residue A x) (IsLocalRing.residue A y) := by
    rw [← map_equationDefect] at hzero
    exact (Affine.equation_iff _ _).mpr (sub_eq_zero.mp hzero)
  refine ⟨hEq, ?_⟩
  rw [Affine.nonsingular_iff]
  intro hns
  rcases hns.2 with h | h
  · exact h (sub_eq_zero.mp hX)
  · apply h
    change IsLocalRing.residue A y = -IsLocalRing.residue A y -
      IsLocalRing.residue A V.a₁ * IsLocalRing.residue A x - IsLocalRing.residue A V.a₃
    linear_combination hY

/-- モデル一致を明示して、同じ中心の剰余特異性を元の一般ファイバーへ輸送する。
座標や中心を選び直さず、等式による型の輸送だけを行う。 -/
theorem residue_singular_of_model (V : WeierstrassCurve A)
    (hmodel : V.map A.subtype = W) (C : CriticalCentre A W) :
    let xr := IsLocalRing.residue A (⟨C.x, C.x_mem⟩ : A)
    let yr := IsLocalRing.residue A (⟨C.y, C.y_mem⟩ : A)
    (V.map (IsLocalRing.residue A)).toAffine.Equation xr yr ∧
      ¬ (V.map (IsLocalRing.residue A)).toAffine.Nonsingular xr yr := by
  subst W
  exact C.residue_singular V

end CriticalCentre

open ValuationInertia ValuationPrimeSupport

/-- 奇素数上では、同じ有理曲線の任意の臨界中心の座標を全慣性元が固定する。
節点の単元n=b₂+12xについてn²=c₄を使う。慣性による剰余合同はnと−nを区別する。
12の逆元の整性や付値保存の一般論は要求せず、等号を得てから標数0で12,2を約分する。 -/
theorem CriticalCentre.inertia_fixed (E : WeierstrassCurve ℚ)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (C : CriticalCentre A (E.baseChange (AlgebraicClosure ℚ)))
    (h2 : A.valuation (2 : AlgebraicClosure ℚ) = 1)
    (σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) (hσ : σ ∈ inertiaSubgroupIn A ℚ) :
    σ C.x = C.x ∧ σ C.y = C.y := by
  have eb : σ (E.baseChange (AlgebraicClosure ℚ)).b₂ = (E.baseChange (AlgebraicClosure ℚ)).b₂ := by simp [baseChange]
  have ec : σ (E.baseChange (AlgebraicClosure ℚ)).c₄ = (E.baseChange (AlgebraicClosure ℚ)).c₄ := by simp [baseChange]
  have e₁ : σ (E.baseChange (AlgebraicClosure ℚ)).a₁ = (E.baseChange (AlgebraicClosure ℚ)).a₁ := by simp [baseChange]
  have e₃ : σ (E.baseChange (AlgebraicClosure ℚ)).a₃ = (E.baseChange (AlgebraicClosure ℚ)).a₃ := by simp [baseChange]
  have en := inertia_fixed_of_unit_square A ℚ h2 σ hσ C.node_unit
    (by rw [C.node_square, ec])
  have ex : σ C.x = C.x := by
    simp only [map_add, map_mul, map_ofNat, eb] at en
    linear_combination (1 / 12 : AlgebraicClosure ℚ) * en
  have hy := congrArg σ C.derivativeY
  simp only [map_add, map_mul, map_ofNat, map_zero, e₁, e₃, ex] at hy
  exact ⟨ex, by linear_combination (1 / 2 : AlgebraicClosure ℚ) * hy - (1 / 2 : AlgebraicClosure ℚ) * C.derivativeY⟩

end DkMath.Lib.NumberTheory.EllipticCriticalCentre
