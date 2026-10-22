/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyNodalReduction
import DkMathTest.FLT.FreyCriticalCentre
import DkMathTest.FLT.FreySmoothReductionInertia

#print "file: DkMathTest.FLT.FreyNodalReduction"

/-!
# NOTE-031-002C3: 同じ曲線の滑らかな点と特異点へ落ちる点を中心の深さで分ける

前章のΔ=225,c₄=241の曲線で、既存の中心に二つの接線方向を構成する。
実際の非零2-torsion点(−4,2)は中心へ近づき、滑らかな非零2-torsion点(0,0)は近づかない。
どちらも同じ中心・同じ付値環を用いる。接線方向の慣性固定を、近づく点自体の固定には読み替えない。
-/
namespace FreyNodalReductionTest
open DkMath.Lib.NumberTheory ValuationInertia ValuationPrimeSupport
open EllipticCriticalCentre EllipticCriticalCentreAlgebra EllipticTangentDirections
open EllipticGoodReductionSeparation EllipticNodalReduction WeierstrassCurve
open FreyValuationArithmeticTest
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩
local instance : Fact (Nat.Prime 37) := ⟨by decide⟩

private theorem model_map (A : ValuationSubring (AlgebraicClosure ℚ)) :
    (curveInt.map (Int.castRingHom A)).map A.subtype = curve.baseChange (AlgebraicClosure ℚ) := by
  simp only [curve, baseChange, map_map]
  congr 1

/-- 既存の任意の中心に二方向が存在し、剰余値も分離し、各方向が慣性固定となる。 -/
theorem directions_at_three (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 3)
    (C : CriticalCentre A (curve.baseChange (AlgebraicClosure ℚ))) :
    ∃ D : TangentDirections C,
      IsLocalRing.residue A (⟨D.α, D.α_mem⟩ : A) ≠ IsLocalRing.residue A (⟨D.β, D.β_mem⟩ : A) ∧
      ∀ (σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)), σ ∈ inertiaSubgroupIn A ℚ →
        σ D.α = D.α ∧ σ D.β = D.β := by
  have h2 : A.valuation (2 : AlgebraicClosure ℚ) = 1 :=
    valuation_intCast_eq_one_of_not_dvd A (by decide)
      ((ValuationSubring.mem_nonunits_iff _).mp hA) (z := 2) (by norm_num)
  have ha₁ : (curve.baseChange (AlgebraicClosure ℚ)).a₁ ∈ A := by
    norm_num [curve, curveInt, baseChange]
  obtain ⟨D⟩ := exists_tangentDirections A _ C ha₁ h2
  exact ⟨D, D.residue_ne, fun σ hσ => D.inertia_fixed curve A h2 σ hσ⟩

/-- 前章の実在する中心から、実際に相異なる方向を持つ組を構成する。条件付き中心だけの回帰ではない。 -/
theorem exists_nodal_data_at_three (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 3) :
    ∃ C : CriticalCentre A (curve.baseChange (AlgebraicClosure ℚ)), ∃ D : TangentDirections C,
      D.α ≠ D.β ∧ A.valuation (equationDefect (curve.baseChange (AlgebraicClosure ℚ)) C.x C.y) =
        A.valuation (3 : AlgebraicClosure ℚ) ^ 2 := by
  obtain ⟨C, hv, _⟩ := FreyCriticalCentreTest.exists_centre_at_three A hA
  obtain ⟨D, _, _⟩ := directions_at_three A hA C
  exact ⟨C, D, D.ne, hv⟩

/-- 前章の特異点へ落ちる実際の2-torsion点(−4,2)の、代数閉包上での非特異性。 -/
theorem bad_point_nonsingular : (curve.baseChange (AlgebraicClosure ℚ)).toAffine.Nonsingular (-4) 2 := by
  norm_num [curve, curveInt, baseChange, Affine.nonsingular_iff, Affine.equation_iff]

/-- 実際の点(−4,2)は、同じ任意の中心へX,Yの両方向で近づく。
これはその点を慣性が動かすという主張ではなく、零成分外の座標的な分類である。 -/
theorem bad_point_depth (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 3)
    (C : CriticalCentre A (curve.baseChange (AlgebraicClosure ℚ))) :
    A.valuation ((-4 : AlgebraicClosure ℚ) - C.x) < 1 ∧ A.valuation ((2 : AlgebraicClosure ℚ) - C.y) < 1 := by
  have hn : ¬ HasSmoothReduction (curveInt.map (Int.castRingHom A)) (.some (-4) 2 bad_point_nonsingular) := by
    rw [hasSmoothReduction_some_iff]
    exact FreySmoothReductionInertiaTest.singular_coordinates_excluded A hA
  have hx := (not_hasSmoothReduction_some_iff_of_model _ _ (model_map A) C bad_point_nonsingular).mp hn
  exact ⟨hx, y_small_of_x_small_of_model _ _ (model_map A) C bad_point_nonsingular hx⟩

/-- 滑らかな実際の非零2-torsion点(0,0)は、同じ中心のX座標へ近づかない。 -/
theorem smooth_point_not_depth (A : ValuationSubring (AlgebraicClosure ℚ))
    (C : CriticalCentre A (curve.baseChange (AlgebraicClosure ℚ))) :
    FreySmoothReductionInertiaTest.smoothTorsion ≠ 0 ∧ ¬ A.valuation ((0 : AlgebraicClosure ℚ) - C.x) < 1 := by
  refine ⟨FreySmoothReductionInertiaTest.smoothTorsion_ne_zero, ?_⟩
  intro hv
  have hn := (not_hasSmoothReduction_some_iff_of_model _ _ (model_map A) C
    FreySmoothReductionInertiaTest.origin_nonsingular).mpr hv
  exact hn (FreySmoothReductionInertiaTest.smoothTorsion_hasSmoothReduction A)

/-- 同じ実際の点の枝座標の積には、非零のずれF₀が残る。接錐の二直線そのものとは区別する。 -/
theorem bad_point_branch_equation (A : ValuationSubring (AlgebraicClosure ℚ))
    {C : CriticalCentre A (curve.baseChange (AlgebraicClosure ℚ))} (D : TangentDirections C) :
    ((2 - C.y) - D.α * (-4 - C.x)) * ((2 - C.y) - D.β * (-4 - C.x)) =
      (-4 - C.x) ^ 3 - equationDefect (curve.baseChange (AlgebraicClosure ℚ)) C.x C.y :=
  D.point_equation bad_point_nonsingular.1

/-- 非退化性を失った尖点の二次式では方向が衝突する。分離の仮定を除かない。 -/
theorem cuspidal_directions_collide : ∀ α β : ZMod 3, α + β = 0 → α * β = 0 → α = β := by
  decide

/-- 同じSource 37の悪い素数3で、中心を保持した二方向と、同じずれの37乗の深さを供給する。 -/
theorem source37_directions (S : DkMath.FLT.Frey.Source 37) (hd : (3 : ℤ) ∣ S.a * S.b * S.c)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 3) :
    ∃ C : CriticalCentre A (S.rationalCurve.baseChange (AlgebraicClosure ℚ)), ∃ D : TangentDirections C,
      (∀ (σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)), σ ∈ inertiaSubgroupIn A ℚ →
        (σ C.x = C.x ∧ σ C.y = C.y) ∧ (σ D.α = D.α ∧ σ D.β = D.β)) ∧
      A.valuation (equationDefect (S.rationalCurve.baseChange (AlgebraicClosure ℚ)) C.x C.y) =
        (A.valuation (3 : AlgebraicClosure ℚ) ^ (2 * padicValInt 3 (S.a * S.b * S.c))) ^ 37 :=
  S.exists_criticalCentre_directions_at_bad_prime (by decide) (by decide) hd A hA

/-- 同じSource 37の同じ有限残余点で、中心へ近づかない枝を実際の慣性固定へ接続する。 -/
theorem source37_nonclose_fixed (S : DkMath.FLT.Frey.Source 37)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 3)
    (C : CriticalCentre A (S.rationalCurve.baseChange (AlgebraicClosure ℚ)))
    (σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) (hσ : σ ∈ inertiaSubgroupIn A ℚ)
    {x y : AlgebraicClosure ℚ} (h : (S.rationalCurve.baseChange (AlgebraicClosure ℚ)).toAffine.Nonsingular x y)
    (P : S.ResidualSpace) (hP : P.val = .some x y h) (hdepth : ¬ A.valuation (x - C.x) < 1) :
    S.residualRepresentation σ P = P :=
  S.residual_fixed_of_not_close_to_centre (by decide) (by decide) A hA C σ hσ h P hP hdepth

end FreyNodalReductionTest
