/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyTateGoodReductionCharacter

#print "file: DkMath.FLT.FreyTateResonantWitness"

/-!
# 点数矛盾から実際の共鳴慣性の失敗点へ

条件付き塔を保持し、高位吸収の失敗を具体的な素点・慣性元・捩れ点として取り出す。
従来の狭い hbad と新しい失敗点は異なる領域の条件。一般 hno の矛盾ではない。
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

open ValuationInertia

/-- 実際の良還元点数の高さでは、共鳴する悪い住所に高位吸収の失敗点が存在する。
狭い hbad は保持するが、高位吸収を入力にはしない。 -/
theorem residual_resonant_high_absorption_failure {ell : ℕ}
    (hell : ell.Prime) (hellp : ell ≠ p) (hgood : ¬ (ell : ℤ) ∣ S.curve.Δ) :
    ∃ q : ℕ, q.Prime ∧ q ≠ p ∧ 5 ≤ q ∧ (q : ℤ) ∣ S.a * S.b * S.c ∧
      ((q : ZMod p) = 1 ∨ (q : ZMod p) = -1) ∧
      ∃ A : ValuationSubring (AlgebraicClosure ℚ), LiesOverPrime A q ∧
      ∃ τ : Field.absoluteGaloisGroup ℚ, τ ∈ inertiaSubgroupIn A ℚ ∧
      ∃ y : Points S.rationalCurve, p ^ S.goodReductionPointCount ell • y = 0 ∧
        pointAction S.rationalCurve τ y - y ∉ (tower (S.goodReductionPointCount ell - 1)).carrier := by
  classical
  by_contra hf
  push Not at hf
  have hN := S.goodReductionPointCount_pos hell hgood
  have he : S.goodReductionPointCount ell - 1 + 1 = S.goodReductionPointCount ell := by omega
  let T := tower (S.goodReductionPointCount ell - 1)
  let := T.finite
  let := T.cyclic
  apply S.residual_cofixed_point_count_tower_resonant_inertia_impossible hp5 hell hellp hgood
    L hline hcofixed T.carrier T.stable (by simpa only [T, he] using T.card) T.base
  exact hf

/-- 同じ失敗点は、同じ第二指標の同じ有限剰余の非自明性を検出する。 -/
theorem residual_resonant_second_witness {ell : ℕ}
    (hell : ell.Prime) (hellp : ell ≠ p) (hgood : ¬ (ell : ℤ) ∣ S.curve.Δ) :
    ∃ q : ℕ, q.Prime ∧ q ≠ p ∧ 5 ≤ q ∧ (q : ℤ) ∣ S.a * S.b * S.c ∧
      ((q : ZMod p) = 1 ∨ (q : ZMod p) = -1) ∧
      ∃ A : ValuationSubring (AlgebraicClosure ℚ), LiesOverPrime A q ∧
      ∃ τ : Field.absoluteGaloisGroup ℚ, τ ∈ inertiaSubgroupIn A ℚ ∧
      ∃ y : Points S.rationalCurve, p ^ S.goodReductionPointCount ell • y = 0 ∧
        pointAction S.rationalCurve τ y - y ∉ (tower (S.goodReductionPointCount ell - 1)).carrier ∧
        p • y ∉ (tower (S.goodReductionPointCount ell - 1)).carrier ∧
        PadicInt.toZModPow (S.goodReductionPointCount ell) (d τ : ℤ_[p]) ≠ 1 := by
  obtain ⟨q, hq, hqp, hq5, hs, hr, A, hA, τ, hτ, y, hy, hfail⟩ :=
    S.residual_resonant_high_absorption_failure L hline hcofixed hζ hp5 hclass hbad hell hellp hgood
  refine ⟨q, hq, hqp, hq5, hs, hr, A, hA, τ, hτ, y, hy, hfail, ?_, ?_⟩
  · intro hpy
    exact hfail (hbad _ (tower (S.goodReductionPointCount ell - 1)) q hq hqp hq5 hs hr A hA τ hτ y hpy)
  intro hd
  have hN := S.goodReductionPointCount_pos hell hgood
  have he : S.goodReductionPointCount ell - 1 + 1 = S.goodReductionPointCount ell := by omega
  apply hfail
  apply (S.residualFinite_absorption_iff L hline hcofixed hζ hp5 hclass hbad
    (S.goodReductionPointCount ell - 1) τ).mpr
  · rwa [he]
  · rwa [he]

/-- 良還元素数の存在も内部供給し、実際の局所慣性上で第二指標が非自明となる。 -/
theorem residualSecond_nontrivial_resonant_inertia :
    ∃ q : ℕ, q.Prime ∧ q ≠ p ∧ 5 ≤ q ∧ (q : ℤ) ∣ S.a * S.b * S.c ∧
      ((q : ZMod p) = 1 ∨ (q : ZMod p) = -1) ∧
      ∃ A : ValuationSubring (AlgebraicClosure ℚ), LiesOverPrime A q ∧
      ∃ τ : Field.absoluteGaloisGroup ℚ, τ ∈ inertiaSubgroupIn A ℚ ∧ d τ ≠ 1 := by
  obtain ⟨ell, hell, hellp, hgood⟩ := S.exists_good_prime_ne
  obtain ⟨q, hq, hqp, hq5, hs, hr, A, hA, τ, hτ, y, hy, hfail, hpy, hd⟩ :=
    S.residual_resonant_second_witness L hline hcofixed hζ hp5 hclass hbad hell hellp hgood
  refine ⟨q, hq, hqp, hq5, hs, hr, A, hA, τ, hτ, ?_⟩
  intro h
  apply hd
  rw [h, Units.val_one, map_one]

end
end DkMath.FLT.Frey.Source
