/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Adapted from S_FreyPackage_frey_wild_inertia_at_two_trivial.lean,
blob 0131af47435077971efee94c10fe2363fbfa1eb8.
Modified: general rational curve and odd unit-order torsion; no FreyPackage dependency.
-/

import DkMath.Lib.NumberTheory.EllipticDyadicSeparation
import DkMath.Lib.NumberTheory.EllipticTorsionRepresentation

#print "file: DkMath.Lib.NumberTheory.EllipticDyadicWildInertia"

/-!
# NOTE-031-003C: 野生合同は実際の奇数位数捩れ点を固定する

全非零zでσ(z)/zが1に合同なら、整元の差σ(z)-zは小さい。
有限捩れ点のxが単元なら滑らかな差、非単元ならxの比と整元y/xの差を使う。
どちらもσP-Pが無限遠か極を持つことを与える。一方この差は同じ単元位数の捩れ点
なので座標は整であり、極の枝は除かれてσP=Pとなる。
曲線係数の条件と位数の単元性は明示し、後のFrey特殊化で実際に供給する。
-/
namespace DkMath.Lib.NumberTheory.EllipticDyadicWildInertia
open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point
open EllipticDyadicSeparation EllipticTorsionRepresentation

/-- 2上の節点モデルで、全ての乗法的野生合同を満たす自己同型は奇数単元位数の点を固定する。
点の還元合同だけを結論とせず、実際のtorsion表現の等号を証明する。 -/
theorem fixed_of_wild (E : WeierstrassCurve ℚ) [E.IsElliptic] (n : ℕ)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (hW : Integral A (E.baseChange (AlgebraicClosure ℚ)))
    (ha₁ : (E.baseChange (AlgebraicClosure ℚ)).a₁ = 1)
    (ha₃ : (E.baseChange (AlgebraicClosure ℚ)).a₃ = 0)
    (ha₆ : (E.baseChange (AlgebraicClosure ℚ)).a₆ = 0)
    (ha₄0 : (E.baseChange (AlgebraicClosure ℚ)).a₄ ≠ 0)
    (h2 : A.valuation (2 : AlgebraicClosure ℚ) < 1) (hn : Odd n)
    (hpA : (n : AlgebraicClosure ℚ) ∉ A.nonunits)
    (σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ))
    (hwild : ∀ z : AlgebraicClosure ℚ, z ≠ 0 → σ z * z⁻¹ - 1 ∈ A.nonunits)
    (T : Torsion E n) : representation E n σ T = T := by
  classical
  have : (E⁄(AlgebraicClosure ℚ)).IsElliptic := by
    change (E.map (algebraMap ℚ (AlgebraicClosure ℚ))).IsElliptic
    infer_instance
  have small : ∀ z : AlgebraicClosure ℚ, A.valuation z ≤ 1 → A.valuation (σ z - z) < 1 := by
    intro z hz
    by_cases hz0 : z = 0
    · rw [hz0, _root_.map_zero, sub_zero, Valuation.map_zero]; exact zero_lt_one
    · have : σ z - z = z * (σ z * z⁻¹ - 1) := by field_simp
      rw [this, map_mul]
      calc A.valuation z * A.valuation (σ z * z⁻¹ - 1) ≤ 1 * A.valuation (σ z * z⁻¹ - 1) := by
            gcongr
        _ < 1 := by rw [one_mul]; exact (A.mem_nonunits_iff).mp (hwild z hz0)
  apply Subtype.ext
  change Point.map σ.toAlgHom T.val = T.val
  have hTp : n • (T.val : (E⁄(AlgebraicClosure ℚ)).Point) = 0 := by
    exact T.property
  rcases hT : (T.val : (E⁄(AlgebraicClosure ℚ)).Point) with _ | ⟨x, y, h⟩
  · rfl
  · rw [hT] at hTp
    change n • (Point.some x y h : (E⁄(AlgebraicClosure ℚ)).Point) = 0 at hTp
    have hD : n • (Point.map σ.toAlgHom (Point.some x y h) - Point.some x y h) = 0 := by
      rw [nsmul_sub, hTp, sub_zero, ← map_nsmul, hTp, (Point.map _).map_zero]
    suffices key : PoleOrZero A (E⁄(AlgebraicClosure ℚ))
        (Point.map σ.toAlgHom (Point.some x y h) - Point.some x y h) by
      exact sub_eq_zero.mp (eq_zero_of_poleOrZero hW hn hpA hD key)
    obtain ⟨h', hsm⟩ : ∃ h', Point.map σ.toAlgHom (Point.some x y h) =
        (Point.some (σ x) (σ y) h' : (E⁄(AlgebraicClosure ℚ)).Point) := ⟨_, rfl⟩
    rw [hsm]
    have hxA : x ∈ A :=
      torsion_x_mem hW hpA h hTp
    have hvx : A.valuation x ≤ 1 := (A.valuation_le_one_iff x).mpr hxA
    have hxa : A.valuation (E⁄(AlgebraicClosure ℚ)).a₄ ≤ A.valuation x :=
      v_a₄_le_of_torsion hW ha₃ ha₆ ha₄0 h2 hn hpA hTp
    rcases eq_or_lt_of_le hvx with hx1 | hx1
    · exact poleOrZero_sub_of_unit hW ha₁ ha₃ h2 hx1 (small x hvx)
        (small y (v_y_le_one hW h.left hvx))
    · have hx0 : x ≠ 0 := by
        intro hx0
        rw [hx0, Valuation.map_zero, le_zero_iff, Valuation.zero_iff] at hxa
        exact ha₄0 hxa
      refine poleOrZero_sub_of_node hW ha₁ ha₃ ha₆ h2 hxa hx1 hx0
        ((A.mem_nonunits_iff).mp (hwild x hx0)) ?_
      have : σ y * (σ x)⁻¹ - y * x⁻¹ = σ (y * x⁻¹) - y * x⁻¹ := by rw [map_mul, map_inv₀]
      rw [this]
      exact small _ (v_ratio_le_one hW ha₁ ha₃ ha₆ h.left hxa hx1 hx0)


end DkMath.Lib.NumberTheory.EllipticDyadicWildInertia
