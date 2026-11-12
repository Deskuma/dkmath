/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyNonresonantInertia
import DkMath.Lib.NumberTheory.EllipticFrobeniusFixedReduction
import Mathlib.Data.Nat.Prime.Infinite

#print "file: DkMath.FLT.FreyGoodReductionTowerObstruction"

/-!
# 実際の良還元点数を塔の指数に固定した最終矛盾

`N=#E(F_ell)` とした同じ巡回段 `#K=p^N` を用いる。
局所吸収から全 Galois 差の吸収を得ると、実際の Frobenius 固定捩れ点は
少なくとも `p^N` 個。一方、その点は `E(F_ell)` へ単射に還元されるので `p^N≤N`。
この経路は未実装の Frobenius 特性方程式を使わない。
同じ長さの大域巡回段と、共鳴する悪い住所の吸収は依然入力である。
-/

namespace DkMath.FLT.Frey.Source

open DkMath.Lib.Algebra DkMath.Lib.NumberTheory
open EllipticTorsionRepresentation EllipticFrobeniusFixedReduction ValuationInertia ValuationFrobenius
open DkMath.Lib.RepresentationTheory

noncomputable section
variable {p : ℕ} [Fact p.Prime] (S : Source p)
local instance instIsEllipticGoodReductionTowerObstruction : S.rationalCurve.IsElliptic := S.rationalCurve_isElliptic

/-- 同じ整数曲線の、指定素数での実際の有限体点数。 -/
def goodReductionPointCount (ell : ℕ) : ℕ :=
  Nat.card (S.curve.baseChange (ZMod ell)).toAffine.Point

omit [Fact p.Prime] in
/-- 良還元点数は有限かつ正。無限遠点を必ず含む。 -/
theorem goodReductionPointCount_pos {ell : ℕ} (hell : ell.Prime) (hgood : ¬ (ell : ℤ) ∣ S.curve.Δ) :
    0 < S.goodReductionPointCount ell := by
  let : Fact ell.Prime := ⟨hell⟩
  let W := S.curve.baseChange (ZMod ell)
  let : W.IsElliptic := (WeierstrassCurve.isElliptic_iff W).mpr (isUnit_iff_ne_zero.mpr (by
    simpa only [W, WeierstrassCurve.baseChange, WeierstrassCurve.map_Δ, eq_intCast,
      ne_eq, CharP.intCast_eq_zero_iff (ZMod ell) ell] using hgood))
  let : Finite W.toAffine.Point := finite_points W
  exact Nat.card_pos

omit [Fact p.Prime] in
/-- 捩れ素数と判別式の支持を避ける実際の良還元素数は存在する。 -/
theorem exists_good_prime_ne : ∃ ell : ℕ, ell.Prime ∧ ell ≠ p ∧ ¬ (ell : ℤ) ∣ S.curve.Δ := by
  obtain ⟨ell, hbound, hell⟩ := Nat.exists_infinite_primes (p + S.curve.Δ.natAbs + 1)
  refine ⟨ell, hell, by omega, ?_⟩
  intro hd
  have hle := Int.natAbs_le_of_dvd_ne_zero hd S.curve_discriminant_ne_zero
  simp only [Int.natAbs_natCast] at hle
  omega

/-- 前章の局所吸収を、同じ指数で全 Galois 元の差の吸収へ接続する。 -/
theorem prime_power_pointAction_sub_mem_of_resonant_inertia (hp5 : 5 ≤ p)
    (L : Submodule (ZMod p) S.ResidualSpace) (hline : Module.finrank (ZMod p) L = 1)
    (hcofixed : IsCofixedOn S.residualRepresentation L)
    (K : AddSubgroup (Points S.rationalCurve)) [Finite K] [IsAddCyclic K]
    (hstable : ∀ σ : Field.absoluteGaloisGroup ℚ, ∀ x ∈ K, pointAction S.rationalCurve σ x ∈ K)
    {N : ℕ} (hN : 0 < N) (hcard : Nat.card K = p ^ N)
    (hbase : pointSubgroup S.rationalCurve p L ≤ K)
    (hbad : ∀ q : ℕ, q.Prime → q ≠ p → 5 ≤ q → (q : ℤ) ∣ S.a * S.b * S.c →
      ((q : ZMod p) = 1 ∨ (q : ZMod p) = -1) →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), LiesOverPrime A q →
        ∀ τ ∈ inertiaSubgroupIn A ℚ, ∀ y : Points S.rationalCurve,
          p ^ N • y = 0 → pointAction S.rationalCurve τ y - y ∈ K)
    (σ : Field.absoluteGaloisGroup ℚ) {y : Points S.rationalCurve} (hy : p ^ N • y = 0) :
    pointAction S.rationalCurve σ y - y ∈ K := by
  apply S.prime_power_pointAction_sub_mem_of_bad_inertia N K ?_ σ hy
  intro q hq hsupport A hA τ hτ z hz
  by_cases hqp : q = p
  · subst q
    exact S.prime_power_pointAction_sub_mem_cyclic_tower_at_p hp5 L hline hcofixed K hstable
      hN hcard hbase A hA τ hτ hz
  · have hb : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c :=
      hsupport.elim Or.inl (fun h => h.elim (fun he => (hqp he).elim) Or.inr)
    by_cases hres : (q : ZMod p) = 1 ∨ (q : ZMod p) = -1
    · have hq5 := five_le_of_prime_sign_resonance hp5 hq hres
      exact hbad q hq hqp hq5 (hb.resolve_left (by omega)) hres A hA τ hτ z hz
    · exact S.prime_power_pointAction_sub_mem_of_nonresonant_bad hp5 L hline hcofixed K hstable
        hN hcard hbase hq hqp hb (fun h => hres (Or.inl h)) (fun h => hres (Or.inr h)) A hA τ hτ hz

/-- `N=#E(F_ell)` の同じ段で、最終矛盾から `hCH` を除去する。
Frobenius 元は指定した良還元素数から内部構成し、固定点を実際の有限体へ還元する。 -/
theorem residual_cofixed_point_count_tower_resonant_inertia_impossible (hp5 : 5 ≤ p)
    {ell : ℕ} (hell : ell.Prime) (hellp : ell ≠ p) (hgood : ¬ (ell : ℤ) ∣ S.curve.Δ)
    (L : Submodule (ZMod p) S.ResidualSpace) (hline : Module.finrank (ZMod p) L = 1)
    (hcofixed : IsCofixedOn S.residualRepresentation L)
    (K : AddSubgroup (Points S.rationalCurve)) [Finite K] [IsAddCyclic K]
    (hstable : ∀ σ : Field.absoluteGaloisGroup ℚ, ∀ x ∈ K, pointAction S.rationalCurve σ x ∈ K)
    (hcard : Nat.card K = p ^ S.goodReductionPointCount ell)
    (hbase : pointSubgroup S.rationalCurve p L ≤ K)
    (hbad : ∀ q : ℕ, q.Prime → q ≠ p → 5 ≤ q → (q : ℤ) ∣ S.a * S.b * S.c →
      ((q : ZMod p) = 1 ∨ (q : ZMod p) = -1) →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), LiesOverPrime A q →
        ∀ τ ∈ inertiaSubgroupIn A ℚ, ∀ y : Points S.rationalCurve,
          p ^ S.goodReductionPointCount ell • y = 0 → pointAction S.rationalCurve τ y - y ∈ K) : False := by
  let N := S.goodReductionPointCount ell
  have hN : 0 < N := S.goodReductionPointCount_pos hell hgood
  obtain ⟨A, hA⟩ := ValuationPrimeExistence.exists_liesOverPrime (L := AlgebraicClosure ℚ) hell
  obtain ⟨σ, hσ⟩ := exists_isFrobeniusAt_of_liesOverPrime hell A hA
  have hcop : ¬ ell ∣ p ^ N := fun hd =>
    hellp ((Nat.prime_dvd_prime_iff_eq hell (Fact.out : p.Prime)).mp (hell.dvd_of_dvd_pow hd))
  have hle : p ^ N ≤ N := torsion_index_le_finite_point_count_of_absorbing S.rationalCurve S.curve
    S.curve_map hell (pow_pos (Fact.out : p.Prime).pos _) hgood hcop A hA σ hσ K hcard
    (fun y hy => S.prime_power_pointAction_sub_mem_of_resonant_inertia hp5 L hline hcofixed K hstable
      hN hcard hbase hbad σ hy)
  exact (not_le_of_gt (Nat.lt_pow_self (Fact.out : p.Prime).one_lt)) hle

end
end DkMath.FLT.Frey.Source
