/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyTateInertiaUnipotent
import DkMath.FLT.FreyTateInertiaQuotient

#print "file: DkMath.FLT.FreyTateInertiaCharacters"

/-!
# 同じ第二 Tate 指標の悪い住所での慣性自明性

有限環の冪零元を消去しない。全 Tate 作用の二次冪零性を同じ基底へ写し、
整域 ℤp で第二対角成分を1と同定してから有限剰余へ戻す。
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
local notation "basis" => S.residualTateBasis L hline hcofixed hζ hp5 hclass hbad
local notation "mat" => S.residualTateActionMatrix L hline hcofixed hζ hp5 hclass hbad
local notation "d" => S.residualTateSecondCharacter L hline hcofixed hζ hp5 hclass hbad
local notation "tower" => S.residualCyclicTower L hline hcofixed hζ hp5 hclass hbad

open ValuationInertia

/-- 同じ全 Tate 行列の慣性差分が二次冪零。 -/
theorem residualTateActionMatrix_inertia_square_zero {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (haddr : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (τ : Field.absoluteGaloisGroup ℚ) (hτ : τ ∈ inertiaSubgroupIn A ℚ) :
    (mat τ - 1) ^ 2 = 0 := by
  have h := congrArg (LinearMap.toMatrixAlgEquiv basis)
    (S.tate_inertia_difference_square_zero hp5 hq hqp haddr A hA τ hτ)
  simp only [map_pow, map_sub, map_one, map_zero] at h
  exact h

/-- 整域 ℤp の第二対角成分により、同じ第二指標は同じ慣性元で1。 -/
theorem residualTateSecondCharacter_inertia_eq_one {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (haddr : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (τ : Field.absoluteGaloisGroup ℚ) (hτ : τ ∈ inertiaSubgroupIn A ℚ) : d τ = 1 := by
  have hm := S.residualTateActionMatrix_inertia_square_zero L hline hcofixed hζ hp5 hclass hbad
    hq hqp haddr A hA τ hτ
  have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ_[p] => M 1 1) hm
  have hz := (S.residualTateActionMatrix_first_column L hline hcofixed hζ hp5 hclass hbad τ).2
  have hd : (mat τ 1 1 - 1) * (mat τ 1 1 - 1) = 0 := by
    simpa [pow_two, Matrix.mul_apply, Fin.sum_univ_two, hz] using he
  apply Units.ext
  change mat τ 1 1 = 1
  exact sub_eq_zero.mp ((mul_eq_zero.mp hd).elim id id)

/-- 同じ指標の実際の自明性から、全有限段の高位吸収を内部供給する。 -/
theorem residualFinite_inertia_absorbs_at_bad (n : ℕ) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (haddr : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (τ : Field.absoluteGaloisGroup ℚ) (hτ : τ ∈ inertiaSubgroupIn A ℚ)
    {y : Points S.rationalCurve} (hy : p ^ (n + 1) • y = 0) :
    pointAction S.rationalCurve τ y - y ∈ (tower n).carrier := by
  apply (S.residualFinite_absorption_iff L hline hcofixed hζ hp5 hclass hbad n τ).mpr
  · rw [S.residualTateSecondCharacter_inertia_eq_one L hline hcofixed hζ hp5 hclass hbad
      hq hqp haddr A hA τ hτ, Units.val_one, map_one]
  · exact hy

end
end DkMath.FLT.Frey.Source
