/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyValuationArithmetic
import DkMath.Lib.NumberTheory.EllipticCriticalCentre

#print "file: DkMath.FLT.FreyCriticalCentre"

/-!
# NOTE-031-002C2: 同じFreyモデルの臨界中心とpで割れる深さ

qがabcを割る奇素数なら、同じモデルでv(Δ)<1、v(c₄)=1が成立する。
臨界中心の存在をこれらから証明し、そのずれの付値を同じΔのp乗の式へ結ぶ。
中心の座標は慣性固定だが、これは全ての残余点の固定ではない。
次章では中心からの距離と枝を比較して、零成分外の実際のtorsion点を扱う。
-/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory ValuationInertia ValuationPrimeSupport
open EllipticCriticalCentre EllipticCriticalCentreAlgebra WeierstrassCurve
variable {p : ℕ} (S : Source p)

/-- abcを割る奇素数上に、同じ有理曲線の臨界中心が存在する。
中心座標の慣性固定と、同じずれの付値がp乗であることも同じ中心について供給する。
q=pでも中心と算術等式は有効であり、q≠pを必要とするtorsion整性とは区別する。 -/
theorem exists_criticalCentre_at_bad_prime (hp : 0 < p) {q : ℕ} [Fact q.Prime]
    (hq2 : q ≠ 2) (hd : (q : ℤ) ∣ S.a * S.b * S.c)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q) :
    ∃ C : CriticalCentre A (S.rationalCurve.baseChange (AlgebraicClosure ℚ)),
      (∀ (σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)), σ ∈ inertiaSubgroupIn A ℚ →
        σ C.x = C.x ∧ σ C.y = C.y) ∧
      A.valuation (equationDefect (S.rationalCurve.baseChange (AlgebraicClosure ℚ)) C.x C.y) =
        (A.valuation (q : AlgebraicClosure ℚ) ^ (2 * padicValInt q (S.a * S.b * S.c))) ^ p := by
  let W := S.rationalCurve.baseChange (AlgebraicClosure ℚ)
  have hW : W = S.curve.map (Int.castRingHom (AlgebraicClosure ℚ)) := by
    dsimp only [W]
    rw [← S.curve_map, baseChange, map_map]
    congr 1
  have hdelta : W.Δ = (S.curve.Δ : AlgebraicClosure ℚ) := by simp [hW, eq_intCast]
  have hc4 : W.c₄ = (S.curve.c₄ : AlgebraicClosure ℚ) := by simp [hW, eq_intCast]
  have hΔ : W.Δ ≠ 0 := by rw [hdelta]; exact Int.cast_ne_zero.mpr S.curve_discriminant_ne_zero
  have hvΔ : A.valuation W.Δ < 1 := by
    rw [hdelta]
    exact valuation_intCast_lt_one_of_dvd A ((ValuationSubring.mem_nonunits_iff _).mp hA)
      (S.local_arithmetic hp hq2 hd).1
  have hc : A.valuation W.c₄ = 1 := by rw [hc4]; exact S.valuation_c4_eq_one hp hq2 hd A hA
  obtain ⟨C⟩ := EllipticCriticalCentre.exists_criticalCentre A W
    (by rw [hW, map_a₁]; exact intCast_mem A _)
    (by rw [hW, map_a₂]; exact intCast_mem A _)
    (by rw [hW, map_a₃]; exact intCast_mem A _)
    (by rw [hW, map_a₄]; exact intCast_mem A _)
    (by rw [hW, map_a₆]; exact intCast_mem A _) hΔ hvΔ hc
  have h2 : A.valuation (2 : AlgebraicClosure ℚ) = 1 :=
    valuation_intCast_eq_one_of_not_dvd A Fact.out ((ValuationSubring.mem_nonunits_iff _).mp hA)
      (z := 2) (by intro h; exact hq2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp (by exact_mod_cast h)))
  refine ⟨C, fun σ hσ => C.inertia_fixed S.rationalCurve A h2 σ hσ, ?_⟩
  rw [C.defect_valuation, hdelta]
  exact S.valuation_discriminant_pth_power hq2 A hA

end DkMath.FLT.Frey.Source
