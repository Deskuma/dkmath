/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.EllipticGoodReductionSeparation
import DkMath.Lib.NumberTheory.ValuationPrimeSupport
import DkMath.Lib.NumberTheory.EllipticTorsionRepresentation

#print "file: DkMath.Lib.NumberTheory.EllipticGoodReductionInertia"

/-!
# NOTE-031-002B: 良還元で合同なprime-to-q torsion点は等しい

P,Qが同じ剰余座標を持つなら、異なると仮定した差点P−Qのx座標には極がある。
しかしnP=nQ=0なら差点もn倍零であり、nが単元なら前章からそのx座標は整である。
従ってP=Qとなる。還元写像の加法性を外部providerに要求しない。
慣性元と元の点は同じ剰余座標を持つので、この単射性から実際の表現で固定される。
-/
namespace DkMath.Lib.NumberTheory.EllipticGoodReductionInertia
open WeierstrassCurve IsLocalRing EllipticGoodReductionSeparation

/-- 同じ整モデルのn-torsion点が同じ剰余座標を持ち、第一点が滑らかに還元するなら等しい。
剰余判別式の非零性を必要とせず、悪い還元でも当該点が滑らかなら適用できる。
差点の極と実際の差点のtorsion整性を衝突させる。 -/
theorem torsion_eq_of_coordinate_congruence_of_smooth {L : Type*} [Field L] [CharZero L] [DecidableEq L]
    {A : ValuationSubring L} (W : WeierstrassCurve A)
    {n : ℕ} (hn : A.valuation (n : L) = 1)
    {x₁ y₁ x₂ y₂ : L} (hs : SmoothCoordinates W x₁ y₁) (h₁ : (W.map A.subtype).toAffine.Nonsingular x₁ y₁)
    (h₂ : (W.map A.subtype).toAffine.Nonsingular x₂ y₂)
    (ht₁ : n • Affine.Point.some x₁ y₁ h₁ = 0) (ht₂ : n • Affine.Point.some x₂ y₂ h₂ = 0)
    (hxx : x₁ - x₂ ∈ A.nonunits) (hyy : y₁ - y₂ ∈ A.nonunits) :
    Affine.Point.some x₁ y₁ h₁ = Affine.Point.some x₂ y₂ h₂ := by
  have hx₁ := EllipticTorsionValuationIntegrality.torsion_x_mem A W _ rfl hn h₁ ht₁
  have hx₂ := EllipticTorsionValuationIntegrality.torsion_x_mem A W _ rfl hn h₂ ht₂
  by_contra hne
  have hneg := (Affine.nonsingular_neg ..).mpr h₂
  have hPQ : ¬ (x₁ = x₂ ∧ y₁ = (W.map A.subtype).toAffine.negY x₂
      ((W.map A.subtype).toAffine.negY x₂ y₂)) := by
    rw [Affine.negY_negY]
    exact fun he => hne (by simp only [Affine.Point.some.injEq]; exact he)
  have hd : Affine.Point.some x₁ y₁ h₁ - Affine.Point.some x₂ y₂ h₂ =
      Affine.Point.some _ _ (Affine.nonsingular_add h₁ hneg hPQ) := by
    rw [sub_eq_add_neg, Affine.Point.neg_some, Affine.Point.add_some hPQ]
  have hdt : n • (Affine.Point.some x₁ y₁ h₁ - Affine.Point.some x₂ y₂ h₂) = 0 := by
    rw [nsmul_sub, ht₁, ht₂, sub_zero]
  have hint := EllipticTorsionValuationIntegrality.torsion_x_mem A W _ rfl hn
    (Affine.nonsingular_add h₁ hneg hPQ) (hd ▸ hdt)
  exact addX_notMem_of_sub_mem_nonunits_of_smooth W hs h₁.1 hneg.1 hx₁ hx₂ hPQ hxx
    (by rwa [Affine.negY_negY]) hint

/-- 良還元の座標単射性は、一点での滑らかな還元による単射性の特殊化である。 -/
theorem torsion_eq_of_coordinate_congruence {L : Type*} [Field L] [CharZero L] [DecidableEq L]
    {A : ValuationSubring L} (W : WeierstrassCurve A)
    (hgood : (W.map (residue A)).Δ ≠ 0) {n : ℕ} (hn : A.valuation (n : L) = 1)
    {x₁ y₁ x₂ y₂ : L} (h₁ : (W.map A.subtype).toAffine.Nonsingular x₁ y₁)
    (h₂ : (W.map A.subtype).toAffine.Nonsingular x₂ y₂)
    (ht₁ : n • Affine.Point.some x₁ y₁ h₁ = 0) (ht₂ : n • Affine.Point.some x₂ y₂ h₂ = 0)
    (hxx : x₁ - x₂ ∈ A.nonunits) (hyy : y₁ - y₂ ∈ A.nonunits) :
    Affine.Point.some x₁ y₁ h₁ = Affine.Point.some x₂ y₂ h₂ :=
  torsion_eq_of_coordinate_congruence_of_smooth W hn (fun _ _ => nonsingular_residue W hgood h₁.1)
    h₁ h₂ ht₁ ht₂ hxx hyy

private theorem eq_of_model_congruence {L : Type*} [Field L] [CharZero L] [DecidableEq L]
    {A : ValuationSubring L} (W : WeierstrassCurve A) (V : WeierstrassCurve L)
    (hm : W.map A.subtype = V) (hg : (W.map (residue A)).Δ ≠ 0)
    {n : ℕ} (hn : A.valuation (n : L) = 1) {x₁ y₁ x₂ y₂ : L}
    (h₁ : V.toAffine.Nonsingular x₁ y₁) (h₂ : V.toAffine.Nonsingular x₂ y₂)
    (ht₁ : n • Affine.Point.some x₁ y₁ h₁ = 0) (ht₂ : n • Affine.Point.some x₂ y₂ h₂ = 0)
    (hx : x₁ - x₂ ∈ A.nonunits) (hy : y₁ - y₂ ∈ A.nonunits) :
    Affine.Point.some x₁ y₁ h₁ = Affine.Point.some x₂ y₂ h₂ := by
  subst V
  exact torsion_eq_of_coordinate_congruence W hg hn h₁ h₂ ht₁ ht₂ hx hy

open EllipticTorsionRepresentation

/-- 良い剰余モデルを持つ同じ実際のE[n]では、nが単元なら慣性元が全点を固定する。
曲線の基底変換とモデルの一致を明示し、同じ座標作用のn倍零性を使う。 -/
theorem fixed_of_inertia_of_good_model (E : WeierstrassCurve ℚ) (n : ℕ)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (W : WeierstrassCurve A)
    (hmodel : W.map A.subtype = E.baseChange (AlgebraicClosure ℚ))
    (hgood : (W.map (residue A)).Δ ≠ 0) (hn : A.valuation (n : AlgebraicClosure ℚ) = 1)
    (σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) (hσ : σ ∈ ValuationInertia.inertiaSubgroupIn A ℚ)
    (P : Torsion E n) : representation E n σ P = P := by
  classical
  apply Subtype.ext
  change pointAction E σ P.val = P.val
  obtain ⟨P, hP⟩ := P
  change n • P = 0 at hP
  cases P with
  | zero => rfl
  | some x y h =>
    change n • (Affine.Point.some x y h : (E.baseChange (AlgebraicClosure ℚ)).toAffine.Point) = 0 at hP
    change Affine.Point.map σ.toAlgHom (Affine.Point.some x y h) = _
    rw [Affine.Point.map_some]
    have ht : n • Affine.Point.map σ.toAlgHom (Affine.Point.some x y h) = 0 := by
      rw [← map_nsmul]
      exact (congrArg (Affine.Point.map σ.toAlgHom) hP).trans (map_zero _)
    rw [Affine.Point.map_some] at ht
    obtain ⟨hx, hy⟩ := EllipticTorsionValuationIntegrality.torsion_coordinates_mem A W _ hmodel hn h hP
    have hxx := ValuationPrimeSupport.inertia_apply_sub_mem_nonunits A ℚ σ hσ hx
    have hyy := ValuationPrimeSupport.inertia_apply_sub_mem_nonunits A ℚ σ hσ hy
    exact eq_of_model_congruence W _ hmodel hgood hn _ h ht hP hxx hyy

end DkMath.Lib.NumberTheory.EllipticGoodReductionInertia
