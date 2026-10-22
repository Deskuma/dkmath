/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyCriticalCentre
import DkMath.FLT.FreySmoothReductionInertia
import DkMath.Lib.NumberTheory.EllipticTangentDirections
import DkMath.Lib.NumberTheory.EllipticNodalReduction

#print "file: DkMath.FLT.FreyNodalReduction"

/-!
# NOTE-031-002C3: 同じFrey中心の方向・深さ・滑らかな還元

同じSourceから得た中心に二つの方向を付け、中心・方向の慣性固定とp乗の深さを保持する。
滑らかに還元しない有限点をv(x−x₀)<1で分類する。中心へ近づかない点の固定はC1へ接続する。
中心へ近づく零成分外の点の固定は、浅さ・枝・torsion深さの比較を必要とする次の境界である。
-/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory ValuationInertia ValuationPrimeSupport
open EllipticCriticalCentre EllipticCriticalCentreAlgebra EllipticTangentDirections
open EllipticGoodReductionSeparation WeierstrassCurve
variable {p : ℕ} (S : Source p)

/-- 悪い奇素数上で、同じ中心Cに接線方向Dを構成し、全ての座標・方向の慣性固定とp乗の深さを返す。
中心を方向の構成で選び直さず、前章の同じCを型の添字に保持する。 -/
theorem exists_criticalCentre_directions_at_bad_prime (hp : 0 < p) {q : ℕ} [Fact q.Prime]
    (hq2 : q ≠ 2) (hd : (q : ℤ) ∣ S.a * S.b * S.c)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q) :
    ∃ C : CriticalCentre A (S.rationalCurve.baseChange (AlgebraicClosure ℚ)),
      ∃ D : TangentDirections C,
        (∀ (σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)), σ ∈ inertiaSubgroupIn A ℚ →
          (σ C.x = C.x ∧ σ C.y = C.y) ∧ (σ D.α = D.α ∧ σ D.β = D.β)) ∧
        A.valuation (equationDefect (S.rationalCurve.baseChange (AlgebraicClosure ℚ)) C.x C.y) =
          (A.valuation (q : AlgebraicClosure ℚ) ^ (2 * padicValInt q (S.a * S.b * S.c))) ^ p := by
  obtain ⟨C, hfix, hv⟩ := S.exists_criticalCentre_at_bad_prime hp hq2 hd A hA
  have h2 : A.valuation (2 : AlgebraicClosure ℚ) = 1 :=
    valuation_intCast_eq_one_of_not_dvd A Fact.out ((ValuationSubring.mem_nonunits_iff _).mp hA)
      (z := 2) (by intro h; exact hq2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp (by exact_mod_cast h)))
  have ha₁ : (S.rationalCurve.baseChange (AlgebraicClosure ℚ)).a₁ ∈ A := by
    rw [← S.valuationModel_map A, map_a₁]
    exact SetLike.coe_mem _
  obtain ⟨D⟩ := exists_tangentDirections A _ C ha₁ h2
  exact ⟨C, D, fun σ hσ => ⟨hfix σ hσ, D.inertia_fixed S.rationalCurve A h2 σ hσ⟩, hv⟩

/-- 同じSourceの任意の有限点が滑らかに還元しないことを、同じ中心からのX方向の深さへ翻訳する。
この座標分類自体は点のp倍零性やq≠pを必要としない。 -/
theorem not_smooth_reduction_iff_depth (A : ValuationSubring (AlgebraicClosure ℚ))
    (C : CriticalCentre A (S.rationalCurve.baseChange (AlgebraicClosure ℚ)))
    {x y : AlgebraicClosure ℚ} (h : (S.rationalCurve.baseChange (AlgebraicClosure ℚ)).toAffine.Nonsingular x y) :
    ¬ HasSmoothReduction (S.valuationModel A) (.some x y h) ↔ A.valuation (x - C.x) < 1 :=
  EllipticNodalReduction.not_hasSmoothReduction_some_iff_of_model (S.valuationModel A) _
    (S.valuationModel_map A) C h

/-- 中心へ近づかない同じ実際の有限残余点は、q≠pで慣性固定となる。
座標分類から滑らかな還元を供給してC1へ渡す。無限遠点に便宜的な座標を付けず、
Pの値が指定された有限点に等しいことを明示する。 -/
theorem residual_fixed_of_not_close_to_centre [Fact p.Prime] {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (C : CriticalCentre A (S.rationalCurve.baseChange (AlgebraicClosure ℚ)))
    (σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) (hσ : σ ∈ inertiaSubgroupIn A ℚ)
    {x y : AlgebraicClosure ℚ} (h : (S.rationalCurve.baseChange (AlgebraicClosure ℚ)).toAffine.Nonsingular x y)
    (P : S.ResidualSpace) (hP : P.val = .some x y h) (hdepth : ¬ A.valuation (x - C.x) < 1) :
    S.residualRepresentation σ P = P := by
  classical
  have hs : HasSmoothReduction (S.valuationModel A) (.some x y h) := by
    by_contra hn
    exact hdepth ((S.not_smooth_reduction_iff_depth A C h).mp hn)
  apply S.residual_fixed_of_smooth_reduction hq hqp A hA σ hσ P
  rw [hP]
  exact hs

end DkMath.FLT.Frey.Source
