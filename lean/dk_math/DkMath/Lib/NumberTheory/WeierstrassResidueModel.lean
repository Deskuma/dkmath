/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.WeierstrassVeluReduction
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

#print "file: DkMath.Lib.NumberTheory.WeierstrassResidueModel"

/-!
# 同じ剰余モデルから判別式の非単元性とc₄の単元性を運ぶ

[DkMath.Lib] 任意の延長付値環で、剰余が零であることはv<1、非零であることはv=1。
同じ剰余モデルを得たとき、これを源と標的の不変量へ適用する。
値群の正規化や付値の離散性は不要。付値そのものの数値的一致は主張しない。
-/
namespace DkMath.Lib.NumberTheory.WeierstrassResidueModel
open WeierstrassCurve IsLocalRing WeierstrassVeluPolynomial
variable {L : Type*} [Field L] (A : ValuationSubring L)

/-- [DkMath.Lib] 付値環の元の剰余が零であることと、同じ元の付値が1未満であることは同値。 -/
theorem residue_zero_iff (a : A) : residue A a = 0 ↔ A.valuation (a : L) < 1 := by
  rw [residue_eq_zero_iff, ← ValuationSubring.coe_mem_nonunits_iff, ValuationSubring.mem_nonunits_iff]

/-- [DkMath.Lib] 剰余の非零性は単元付値1と同値。整な元だけについて述べる。 -/
theorem residue_ne_zero_iff (a : A) : residue A a ≠ 0 ↔ A.valuation (a : L) = 1 := by
  rw [residue_ne_zero_iff_isUnit, A.valuation_eq_one_iff]

/-- [DkMath.Lib] 同じ剰余モデルは、Δの非単元性とc₄の単元性を両方向へ運ぶ。 -/
theorem invariant_conditions_iff (W V : WeierstrassCurve A)
    (he : W.map (residue A) = V.map (residue A)) :
    (A.valuation (W.Δ : L) < 1 ↔ A.valuation (V.Δ : L) < 1) ∧
      (A.valuation (W.c₄ : L) = 1 ↔ A.valuation (V.c₄ : L) = 1) := by
  have hd := congrArg WeierstrassCurve.Δ he
  have hc := congrArg WeierstrassCurve.c₄ he
  simp only [map_Δ] at hd
  simp only [map_c₄] at hc
  exact ⟨(residue_zero_iff A W.Δ).symm.trans (hd ▸ residue_zero_iff A V.Δ),
    (residue_ne_zero_iff A W.c₄).symm.trans (hc ▸ residue_ne_zero_iff A V.c₄)⟩

/-- [DkMath.Lib] 同じ整な代表座標から作る多項式係数モデルは、剰余の多項式構成と可換。 -/
theorem polynomialModel_residue {ι : Type*} (W : WeierstrassCurve A)
    (s : Finset ι) (x y : ι → A) :
    (polynomialModel W s x y).map (residue A) = polynomialModel (W.map (residue A)) s
      (fun i => residue A (x i)) (fun i => residue A (y i)) :=
  polynomialModel_map _ _ _ _ _

/-- [DkMath.Lib] 全代表の剰余が特異点なら、同じ整係数モデルの剰余は源と一致する。 -/
theorem polynomialModel_residue_eq_of_singular {ι : Type*} (W : WeierstrassCurve A)
    (s : Finset ι) (x y : ι → A)
    (hs : ∀ i ∈ s, (W.map (residue A)).toAffine.Equation (residue A (x i)) (residue A (y i)) ∧
      ¬ (W.map (residue A)).toAffine.Nonsingular (residue A (x i)) (residue A (y i))) :
    (polynomialModel W s x y).map (residue A) = W.map (residue A) := by
  rw [polynomialModel_residue]
  exact polynomialModel_eq_of_singular _ _ _ _ hs

/-- [DkMath.Lib] v(240)<1なら、整な座標を使う全ての多項式商でc₄の単元性を保つ。
核の滑らかさを仮定せず、2,3,5上の算術に使える。 -/
theorem polynomialModel_c4_value_one {ι : Type*} (W : WeierstrassCurve A)
    (s : Finset ι) (x y : ι → A) (h240 : A.valuation (240 : L) < 1)
    (hc : A.valuation (W.c₄ : L) = 1) :
    A.valuation ((polynomialModel W s x y).c₄ : L) = 1 := by
  have hzero : (240 : ResidueField A) = 0 := by
    have hh := (residue_zero_iff A (240 : A)).mpr h240
    simpa only [map_ofNat] using hh
  have he : residue A (polynomialModel W s x y).c₄ = residue A W.c₄ := by
    rw [← map_c₄, polynomialModel_residue]
    rw [polynomialModel_c4_eq_of_240_eq_zero _ _ _ _ hzero, map_c₄]
  apply (residue_ne_zero_iff A _).mp
  rw [he]
  exact (residue_ne_zero_iff A _).mpr hc

end DkMath.Lib.NumberTheory.WeierstrassResidueModel
