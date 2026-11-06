/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyTateFiniteQuotient

#print "file: DkMath.FLT.FreyTateInertiaQuotient"

/-!
# 同じ有限商作用と第二指標の正確な同値

全 p^(n+1) 捩れ上の吸収と d mod p^(n+1)=1 を同値にする。
従来の p•y∈K という狭い hbad を高位吸収へ拡張しない。
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

local notation "second" => S.residualFiniteSecond L hline hcofixed hζ hp5 hclass hbad

/-- 同じ有限商への実際の作用は、同じ第二指標の標準剰余。 -/
theorem residualFiniteSecond_action (n : ℕ) (σ : Field.absoluteGaloisGroup ℚ)
    (x : Torsion S.rationalCurve (p ^ (n + 1))) :
    second n (representation S.rationalCurve (p ^ (n + 1)) σ x) =
      PadicInt.toZModPow (n + 1) (d σ : ℤ_[p]) * second n x := by
  have h := congrArg (fun z => z 1)
    (LinearMap.toMatrix_mulVec_repr (fb n) (fb n) (representation S.rationalCurve (p ^ (n + 1)) σ) x)
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h
  rw [← S.residualTate_matrix_reduction L hline hcofixed hζ hp5 hclass hbad,
    ← S.residualTate_matrix_reduction L hline hcofixed hζ hp5 hclass hbad] at h
  have hz := (S.residualTateActionMatrix_first_column L hline hcofixed hζ hp5 hclass hbad σ).2
  rw [hz, map_zero, zero_mul, zero_add] at h
  exact h.symm

/-- 全有限捩れ点の作用差の吸収は、同じ第二指標の同じ剰余が1であることと同値。 -/
theorem residualFinite_absorption_iff (n : ℕ) (σ : Field.absoluteGaloisGroup ℚ) :
    (∀ y : Points S.rationalCurve, p ^ (n + 1) • y = 0 →
      pointAction S.rationalCurve σ y - y ∈ (tower n).carrier) ↔
      PadicInt.toZModPow (n + 1) (d σ : ℤ_[p]) = 1 := by
  constructor
  · intro ha
    obtain ⟨x, hx⟩ := S.residualFiniteSecond_surjective L hline hcofixed hζ hp5 hclass hbad n 1
    have hy := ha x.val x.property
    have hz := (S.residualFiniteSecond_eq_zero_iff L hline hcofixed hζ hp5 hclass hbad n
      (representation S.rationalCurve (p ^ (n + 1)) σ x - x)).mpr hy
    rw [map_sub, S.residualFiniteSecond_action L hline hcofixed hζ hp5 hclass hbad, hx, mul_one] at hz
    exact sub_eq_zero.mp hz
  · intro hd y hy
    let x : Torsion S.rationalCurve (p ^ (n + 1)) := ⟨y, hy⟩
    apply (S.residualFiniteSecond_eq_zero_iff L hline hcofixed hζ hp5 hclass hbad n
      (representation S.rationalCurve (p ^ (n + 1)) σ x - x)).mp
    rw [map_sub, S.residualFiniteSecond_action L hline hcofixed hζ hp5 hclass hbad, hd, one_mul, sub_self]

/-- 同じ慣性群の各元についての高位吸収も、同じ指標の剰余条件に正確に置き換わる。 -/
theorem residualFinite_inertia_absorption_iff (n : ℕ)
    (A : ValuationSubring (AlgebraicClosure ℚ)) :
    (∀ τ ∈ ValuationInertia.inertiaSubgroupIn A ℚ, ∀ y : Points S.rationalCurve,
      p ^ (n + 1) • y = 0 → pointAction S.rationalCurve τ y - y ∈ (tower n).carrier) ↔
    (∀ τ ∈ ValuationInertia.inertiaSubgroupIn A ℚ,
      PadicInt.toZModPow (n + 1) (d τ : ℤ_[p]) = 1) := by
  exact forall₂_congr (fun τ _ => S.residualFinite_absorption_iff L hline hcofixed hζ hp5 hclass hbad n τ)

end
end DkMath.FLT.Frey.Source
