/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyDoublingDepth
import DkMath.FLT.FreyGoodReductionInertia
import DkMath.Lib.NumberTheory.EllipticDepthInertia

#print "file: DkMath.FLT.FreyUnramifiedAway"

/-!
# NOTE-031-002: q≠2,pで同じFrey残余表現の全点が慣性固定

良い還元の枝は既存の固定性へ接続する。悪い奇素数の枝では同じC,Dに対し、
奇数torsionの深さv(X)^p=v(F₀)^jと判別式のp乗構造から、v(X)=v(q^k)を得る。
有理尺度q^kは慣性固定なので、正規化したXの合同と鋭いX差の評価が点の固定を強制する。
中心や方向の固定を点の固定に読み替えるのではなく、全倍点の帰納と差点の整性を通す。
-/
namespace DkMath.FLT.Frey.Source
open WeierstrassCurve DkMath.Lib.NumberTheory ValuationInertia ValuationPrimeSupport
open EllipticCriticalCentre EllipticCriticalCentreAlgebra EllipticTangentDirections EllipticShallowSlope
open EllipticTorsionDepth EllipticDepthInertia EllipticGoodReductionSeparation EllipticTorsionRepresentation
open DkMath.Lib.RepresentationTheory LocalFixedCofixed
variable {p : ℕ} [Fact p.Prime] (S : Source p)

/-- 悪い奇素数で、p≠2の同じ実際の残余点は慣性固定となる。
有限点の浅さ・冪の深さ・有理尺度・差点の整性を実装済みの定理から供給する。 -/
theorem residual_fixed_at_bad_prime (hp2 : p ≠ 2) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hqp : q ≠ p)
    (hd : (q : ℤ) ∣ S.a * S.b * S.c) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) (hσ : σ ∈ inertiaSubgroupIn A ℚ)
    (P : S.ResidualSpace) : S.residualRepresentation σ P = P := by
  classical
  have : Fact q.Prime := ⟨hq⟩
  have hp : p.Prime := Fact.out
  have hp3 : 3 ≤ p := by have hh := hp.two_le; omega
  have hn : A.valuation (p : AlgebraicClosure ℚ) = 1 := by
    apply valuation_intCast_eq_one_of_not_dvd A hq ((ValuationSubring.mem_nonunits_iff _).mp hA) (z := (p : ℤ))
    intro hdiv
    exact hqp ((Nat.prime_dvd_prime_iff_eq hq hp).mp (by exact_mod_cast hdiv))
  obtain ⟨C, D, hfix, hF⟩ := S.exists_criticalCentre_directions_at_bad_prime hp.pos hq2 hd A hA
  apply Subtype.ext
  change pointAction S.rationalCurve σ P.val = P.val
  obtain ⟨Q, hQ⟩ := P
  change p • Q = 0 at hQ
  cases Q with
  | zero => rfl
  | some x y h =>
    change p • (Affine.Point.some x y h : (S.rationalCurve.baseChange (AlgebraicClosure ℚ)).toAffine.Point) = 0 at hQ
    change Affine.Point.map σ.toAlgHom (Affine.Point.some x y h) = Affine.Point.some x y h
    by_cases hX : A.valuation (x - C.x) < 1
    · obtain ⟨hsh, j, _, _, hpow⟩ := odd_torsion_depth_of_model (S.valuationModel A)
        (S.rationalCurve.baseChange (AlgebraicClosure ℚ)) (S.valuationModel_map A) C D (hp.odd_of_ne_two hp2) hp3 hn h hQ hX
      let k := 2 * padicValInt q (S.a * S.b * S.c)
      have hdepth : A.valuation (x - C.x) = A.valuation (q : AlgebraicClosure ℚ) ^ (k * j) := by
        apply (pow_left_inj₀ zero_le zero_le hp.ne_zero).mp
        rw [hpow, hF]
        dsimp only [k]
        simp only [← pow_mul]
        congr 1
        ring
      have ha : (q : ℚ) ^ (k * j) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hq.ne_zero)
      have hscale : A.valuation (x - C.x) =
          A.valuation (algebraMap ℚ (AlgebraicClosure ℚ) ((q : ℚ) ^ (k * j))) := by
        have he : algebraMap ℚ (AlgebraicClosure ℚ) ((q : ℚ) ^ (k * j)) =
            (q : AlgebraicClosure ℚ) ^ (k * j) := by simp only [map_pow, map_natCast]
        rw [he, map_pow]
        exact hdepth
      exact finite_point_fixed_of_rational_depth S.rationalCurve p A (S.valuationModel A) (S.valuationModel_map A)
        hn C D σ hσ (hfix σ hσ).1 h hQ hX hsh _ ha hscale
    · have hs : HasSmoothReduction (S.valuationModel A) (Affine.Point.some x y h) := by
        by_contra hb
        exact hX ((S.not_smooth_reduction_iff_depth A C h).mp hb)
      have hh := EllipticSmoothReductionInertia.fixed_of_inertia_of_smooth_reduction S.rationalCurve p A
        (S.valuationModel A) (S.valuationModel_map A) hn σ hσ (⟨Affine.Point.some x y h, hQ⟩ : Torsion S.rationalCurve p) hs
      exact congrArg Subtype.val hh

/-- p≠2、q≠2,pで同じFrey残余表現の全点が全てのq上の絶対慣性元に固定される。
qがabcを割るかで分岐し、良い還元と悪い還元の両方を実装済みの証明で閉じる。 -/
theorem residual_fixed_away_two_self (hp2 : p ≠ 2) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hqp : q ≠ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) (hσ : σ ∈ inertiaSubgroupIn A ℚ)
    (P : S.ResidualSpace) : S.residualRepresentation σ P = P := by
  by_cases hd : (q : ℤ) ∣ S.a * S.b * S.c
  · exact S.residual_fixed_at_bad_prime hp2 hq hq2 hqp hd A hA σ hσ P
  · exact S.residual_fixed_at_good_prime hq hq2 hqp hd A hA σ hσ P

/-- q≠2,pでは同じ部分加群と同じ商の両方が慣性固定となる。
側の二択を選び直さず、全点固定からFixedOnとCofixedOnを同時に供給する。 -/
theorem residual_fixed_and_cofixed_away_two_self (hp2 : p ≠ 2) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hqp : q ≠ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (N : Submodule (ZMod p) S.ResidualSpace) :
    FixedOn S.residualRepresentation N (inertiaSubgroupIn A ℚ) ∧ CofixedOn S.residualRepresentation N (inertiaSubgroupIn A ℚ) := by
  constructor
  · intro σ hσ P _
    exact S.residual_fixed_away_two_self hp2 hq hq2 hqp A hA σ hσ P
  · intro σ hσ P
    rw [S.residual_fixed_away_two_self hp2 hq hq2 hqp A hA σ hσ P, sub_self]
    exact N.zero_mem

end DkMath.FLT.Frey.Source
