/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.EllipticGoodReductionInertia

#print "file: DkMath.Lib.NumberTheory.EllipticSmoothReductionInertia"

/-!
# NOTE-031-002C1: 悪い還元でも滑らかな点へ還元するtorsion点は慣性固定

非特異性は曲線全体でなく一点にだけ必要だった。PとσPの座標は合同である。
Pの剰余点が滑らかなら、異なる二点の差の極とprime-to-q torsionの整性が衝突する。
この証明は剰余判別式が零でも通る。零成分外の特異な剰余点へは適用しない。

HasSmoothReductionは無限遠点や非整座標の枝も保持するが、ここでは有限torsion点の
整性を先に証明するので、実際に使う枝は整座標の非特異性である。
全点群の還元準同型・零成分部分加群の加法閉性は今回の主張に含めない。
-/
namespace DkMath.Lib.NumberTheory.EllipticSmoothReductionInertia
open WeierstrassCurve EllipticGoodReductionSeparation EllipticTorsionRepresentation

private theorem eq_of_model_congruence {L : Type*} [Field L] [CharZero L] [DecidableEq L]
    {A : ValuationSubring L} (W : WeierstrassCurve A) (V : WeierstrassCurve L)
    (hm : W.map A.subtype = V) {n : ℕ} (hn : A.valuation (n : L) = 1)
    {x₁ y₁ x₂ y₂ : L} (hs : SmoothCoordinates W x₁ y₁)
    (h₁ : V.toAffine.Nonsingular x₁ y₁) (h₂ : V.toAffine.Nonsingular x₂ y₂)
    (ht₁ : n • Affine.Point.some x₁ y₁ h₁ = 0) (ht₂ : n • Affine.Point.some x₂ y₂ h₂ = 0)
    (hx : x₁ - x₂ ∈ A.nonunits) (hy : y₁ - y₂ ∈ A.nonunits) :
    Affine.Point.some x₁ y₁ h₁ = Affine.Point.some x₂ y₂ h₂ := by
  subst V
  exact EllipticGoodReductionInertia.torsion_eq_of_coordinate_congruence_of_smooth W hn hs
    h₁ h₂ ht₁ ht₂ hx hy

/-- 同じモデルの滑らかな還元を持つ実際のE[n]の点は、nが単元なら全慣性元に固定される。
一点Pの滑らかさだけを要求し、σPの滑らかさや零成分の群構造を別途仮定しない。
曲線・モデル・点・慣性の所在を同じまま保ち、差点の座標整性から等号を証明する。 -/
theorem fixed_of_inertia_of_smooth_reduction (E : WeierstrassCurve ℚ) (n : ℕ)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (W : WeierstrassCurve A)
    (hmodel : W.map A.subtype = E.baseChange (AlgebraicClosure ℚ))
    (hn : A.valuation (n : AlgebraicClosure ℚ) = 1)
    (σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) (hσ : σ ∈ ValuationInertia.inertiaSubgroupIn A ℚ)
    (P : Torsion E n) (hs : HasSmoothReduction W P.val) : representation E n σ P = P := by
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
    have hs' : SmoothCoordinates W x y := hs x y h rfl
    exact (eq_of_model_congruence W _ hmodel hn hs' h _ hP ht
      (by change x - σ x ∈ A.nonunits; simpa only [neg_sub] using neg_mem hxx)
      (by change y - σ y ∈ A.nonunits; simpa only [neg_sub] using neg_mem hyy)).symm

end DkMath.Lib.NumberTheory.EllipticSmoothReductionInertia
