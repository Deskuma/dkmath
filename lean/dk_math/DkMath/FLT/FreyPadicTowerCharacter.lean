/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyCyclicTowerCharacter
import DkMath.Lib.Algebra.PadicCharacterLimit

#print "file: DkMath.FLT.FreyPadicTowerCharacter"

/-!
# 同じ巡回塔の連続 p 進単元値指標と良還元での非自明性

有限指標の両立性から実際の ℤₚˣ 値指標を構成する。
hclass と全段 hbad は従来のまま保持する。良還元では大きい有限段の
Frobenius 指標が非自明となる。非自明性自体は矛盾ではない。
-/

namespace DkMath.FLT.Frey.Source

open DkMath.Lib.Algebra DkMath.Lib.NumberTheory
open EllipticTorsionRepresentation DkMath.Lib.RepresentationTheory
noncomputable section

variable {p : ℕ} [Fact p.Prime] {S : Source p}
local instance : S.rationalCurve.IsElliptic := S.rationalCurve_isElliptic
variable {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ}

/-- 良還元の有限点数より大きい同じ段は Frobenius に全点固定されない。 -/
theorem ResidualCyclicStage.character_ne_one_of_good_bound (T : S.ResidualCyclicStage L n)
    {ell : ℕ} (hell : ell.Prime) (hellp : ell ≠ p) (hgood : ¬ (ell : ℤ) ∣ S.curve.Δ)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : ValuationInertia.LiesOverPrime A ell)
    (σ : Field.absoluteGaloisGroup ℚ) (hσ : ValuationFrobenius.IsFrobeniusAt A σ ell)
    (hlarge : S.goodReductionPointCount ell < p ^ (n + 1)) : T.character σ ≠ 1 := by
  intro h
  exact (not_le_of_gt hlarge) (T.card_le_good_points_of_character_one hell hellp hgood A hA σ hσ h)

/-- 点数 N 以下でない段 n≥N なら、素数 p の増大から非自明性が従う。 -/
theorem ResidualCyclicStage.character_ne_one_of_good_count (T : S.ResidualCyclicStage L n)
    {ell : ℕ} (hell : ell.Prime) (hellp : ell ≠ p) (hgood : ¬ (ell : ℤ) ∣ S.curve.Δ)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : ValuationInertia.LiesOverPrime A ell)
    (σ : Field.absoluteGaloisGroup ℚ) (hσ : ValuationFrobenius.IsFrobeniusAt A σ ell)
    (hn : S.goodReductionPointCount ell ≤ n) : T.character σ ≠ 1 := by
  apply T.character_ne_one_of_good_bound hell hellp hgood A hA σ hσ
  exact lt_of_le_of_lt hn (lt_trans (Nat.lt_succ_self n) (Nat.lt_pow_self (Fact.out : p.Prime).one_lt))

end

section Tower
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
local notation "chars" => S.residualCyclicTowerCharacter L hline hcofixed hζ hp5 hclass hbad
local notation "compat" => S.residualCyclicTowerCharacter_compatible L hline hcofixed hζ hp5 hclass hbad
local notation "towerUnion" => S.residualCyclicTowerUnion L hline hcofixed hζ hp5 hclass hbad

/-- 同じ条件付き塔の有限指標から構成した実際の p 進単元値指標。 -/
def residualPadicTowerCharacter : Field.absoluteGaloisGroup ℚ →* ℤ_[p]ˣ :=
  PadicCharacterLimit.character chars compat

local notation "padicChar" => S.residualPadicTowerCharacter L hline hcofixed hζ hp5 hclass hbad

/-- 元の有限指標を、標準剰余写像で正確に回収する。 -/
theorem residualPadicTowerCharacter_mod (n : ℕ) (σ : Field.absoluteGaloisGroup ℚ) :
    Units.map (PadicInt.toZModPow (n + 1)).toMonoidHom (padicChar σ) = chars n σ :=
  PadicCharacterLimit.character_mod chars compat n σ

/-- 有限段の実際の開核から、構成した極限指標は連続となる。 -/
theorem residualPadicTowerCharacter_continuous : Continuous padicChar :=
  PadicCharacterLimit.character_continuous chars compat (fun n => (tower n).character_kernel_isOpen)

/-- 正確な mod p 成分は同じ元の円分指標。高位成分が円分指標とは主張しない。 -/
theorem residualPadicTowerCharacter_mod_prime (σ : Field.absoluteGaloisGroup ℚ) :
    Units.map ((ZMod.castHom (dvd_pow_self p (by omega : 0 + 1 ≠ 0)) (ZMod p)).comp
      (PadicInt.toZModPow 1)).toMonoidHom (padicChar σ) =
      CyclotomicRootModule.cyclotomicCharacter p σ := by
  change Units.map (ZMod.castHom (dvd_pow_self p (by omega : 0 + 1 ≠ 0)) (ZMod p)).toMonoidHom
    (Units.map (PadicInt.toZModPow (0 + 1)).toMonoidHom (padicChar σ)) = _
  rw [S.residualPadicTowerCharacter_mod L hline hcofixed hζ hp5 hclass hbad]
  exact (tower 0).character_mod_prime hline hcofixed σ

/-- 極限指標値1は、同じ実際の合併の全点固定と正確に同値。 -/
theorem residualPadicTowerCharacter_eq_one_iff (σ : Field.absoluteGaloisGroup ℚ) :
    padicChar σ = 1 ↔ ∀ x ∈ towerUnion, pointAction S.rationalCurve σ x = x := by
  change PadicCharacterLimit.character chars compat σ = 1 ↔ _
  rw [PadicCharacterLimit.character_eq_one_iff]
  constructor
  · intro h x hx
    obtain ⟨n, hn⟩ := (S.mem_residualCyclicTowerUnion L hline hcofixed hζ hp5 hclass hbad x).mp hx
    exact ((tower n).character_eq_one_iff σ).mp (h n) x hn
  · intro h n
    apply ((tower n).character_eq_one_iff σ).mpr
    intro x hx
    exact h x ((S.mem_residualCyclicTowerUnion L hline hcofixed hζ hp5 hclass hbad x).mpr ⟨n, hx⟩)

/-- 同じ良還元 Frobenius の極限指標は非自明。これは矛盾を与える定理ではない。 -/
theorem residualPadicTowerCharacter_frobenius_ne_one
    {ell : ℕ} (hell : ell.Prime) (hellp : ell ≠ p) (hgood : ¬ (ell : ℤ) ∣ S.curve.Δ)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : ValuationInertia.LiesOverPrime A ell)
    (σ : Field.absoluteGaloisGroup ℚ) (hσ : ValuationFrobenius.IsFrobeniusAt A σ ell) :
    padicChar σ ≠ 1 := by
  intro h
  have hn := (tower (S.goodReductionPointCount ell)).character_ne_one_of_good_count
    hell hellp hgood A hA σ hσ le_rfl
  apply hn
  have hm := S.residualPadicTowerCharacter_mod L hline hcofixed hζ hp5 hclass hbad
    (S.goodReductionPointCount ell) σ
  rw [h, map_one] at hm
  exact hm.symm

end
end Tower
end DkMath.FLT.Frey.Source
