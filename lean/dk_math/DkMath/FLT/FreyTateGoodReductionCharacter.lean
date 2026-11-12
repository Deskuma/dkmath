/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyTateInertiaQuotient
import DkMath.FLT.FreyGoodReductionTowerObstruction

#print "file: DkMath.FLT.FreyTateGoodReductionCharacter"

/-!
# 良還元点数が第二指標の高位自明性を排除する

同じ有限商上で Frobenius が自明なら、実際の固定点還元により p^(n+1)≤#E(Fq)。
十分高い一段で第二指標は非自明。トレース・点数同定は用いない。
-/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.Algebra DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory
open EllipticTorsionRepresentation PrimePowerTateSequence
noncomputable section

open CyclotomicKernelField CyclotomicKummerWeight
variable {p : ℕ} [Fact p.Prime] (S : Source p)
local instance : S.rationalCurve.IsElliptic := S.rationalCurve_isElliptic
variable (L : Submodule (ZMod p) S.ResidualSpace)
    (hline : Module.finrank (ZMod p) L = 1)
    (hcofixed : IsCofixedOn S.residualRepresentation L)
    {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ p) (hp5 : 5 ≤ p)
local instance : NumberField (rootField ζ) := rootField_numberField ζ
variable
    (hclass : ∀ a : CyclotomicClassVanishing.ClassModP (rootField ζ) p,
      (∀ γ : (rootField ζ) ≃ₐ[ℚ] (rootField ζ),
        CyclotomicClassVanishing.classModPAction p γ a =
          (baseCharacter hζ γ : ZMod p) ^ 2 • a) → a = 0)
    (hbad : ∀ (n : ℕ) (T : S.ResidualCyclicStage L n), S.ResonantAbsorptionAt T.carrier)
local notation "tower" => S.residualCyclicTower L hline hcofixed hζ hp5 hclass hbad
local notation "fb" => S.residualTateFiniteBasis L hline hcofixed hζ hp5 hclass hbad
local notation "d" => S.residualTateSecondCharacter L hline hcofixed hζ hp5 hclass hbad
local notation "gen" => S.residualTateGenerators L hline hcofixed hζ hp5 hclass hbad

open EllipticFrobeniusFixedReduction ValuationInertia ValuationFrobenius

/-- 同じ良還元 Frobenius の第二指標が一段で1なら、その段の次数は実際の点数以下。 -/
theorem residualSecond_frobenius_bound (n : ℕ) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (hgood : ¬ (q : ℤ) ∣ S.curve.Δ)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    {σ : Field.absoluteGaloisGroup ℚ} (hσ : IsFrobeniusAt A σ q)
    (hd : PadicInt.toZModPow (n + 1) (d σ : ℤ_[p]) = 1) :
    p ^ (n + 1) ≤ S.goodReductionPointCount q := by
  let T := tower n
  let := T.finite
  exact torsion_index_le_finite_point_count_of_absorbing S.rationalCurve S.curve S.curve_map
    hq (pow_pos (Fact.out : p.Prime).pos _) hgood
    (fun h => hqp ((Nat.prime_dvd_prime_iff_eq hq (Fact.out : p.Prime)).mp (hq.dvd_of_dvd_pow h)))
    A hA σ hσ T.carrier T.card
    ((S.residualFinite_absorption_iff L hline hcofixed hζ hp5 hclass hbad n σ).mpr hd)

/-- 一段の次数が点数を越えれば、その同じ有限剰余は1ではない。 -/
theorem residualSecond_frobenius_ne_one_at (n : ℕ) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (hgood : ¬ (q : ℤ) ∣ S.curve.Δ)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    {σ : Field.absoluteGaloisGroup ℚ} (hσ : IsFrobeniusAt A σ q)
    (hbound : S.goodReductionPointCount q < p ^ (n + 1)) :
    PadicInt.toZModPow (n + 1) (d σ : ℤ_[p]) ≠ 1 := by
  intro hd
  exact (not_le_of_gt hbound)
    (S.residualSecond_frobenius_bound L hline hcofixed hζ hp5 hclass hbad n hq hqp hgood A hA hσ hd)

/-- 高さ N=#E(Fq) の段（添字 N-1）で、同じ第二指標は必ず非自明。 -/
theorem residualSecond_frobenius_ne_one {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (hgood : ¬ (q : ℤ) ∣ S.curve.Δ)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    {σ : Field.absoluteGaloisGroup ℚ} (hσ : IsFrobeniusAt A σ q) : d σ ≠ 1 := by
  intro hd
  have hN := S.goodReductionPointCount_pos hq hgood
  have he : S.goodReductionPointCount q - 1 + 1 = S.goodReductionPointCount q := by omega
  apply S.residualSecond_frobenius_ne_one_at L hline hcofixed hζ hp5 hclass hbad
    (S.goodReductionPointCount q - 1) hq hqp hgood A hA hσ
  · rw [he]
    exact Nat.lt_pow_self (Fact.out : p.Prime).one_lt
  · rw [hd, Units.val_one, map_one]

end
end DkMath.FLT.Frey.Source
