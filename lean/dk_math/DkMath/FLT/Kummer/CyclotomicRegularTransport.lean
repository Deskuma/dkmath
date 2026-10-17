/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Kummer.RegularStateTransport
import DkMath.Lib.NumberTheory.CyclotomicRamifiedPhase
import DkMath.FLT.Kummer.ThreeEisensteinBridge
import DkMath.FLT.Kummer.FiveKummerUnit

#print "file: DkMath.FLT.Kummer.CyclotomicRegularTransport"

/-!
# Cyclotomic providers for the general descent

Class-group p-torsion-freeness and the Kummer unit criterion are the two remaining
arithmetic inputs for an arbitrary odd prime. Both are supplied here for 3 and 5
using existing arithmetic lemmas, without either completed FLT theorem. The
endpoint is positive-depth State nonexistence, not an integer FLT entrance.
-/

namespace DkMath.FLT.Kummer.RegularDescent

open DkMath.Lib.NumberTheory
open scoped NumberField

variable {K : Type*} [Field K] [NumberField K]

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- The general cyclotomic conditions, with the two genuine arithmetic hypotheses. -/
theorem cyclotomic_conditions {p : ℕ} [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) (hodd : Odd p) (hp3 : 3 ≤ p)
    (hfree : classGroupPTorsionFreeAt (𝓞 K) p) (hunit : KummerUnitPowerCriterion (𝓞 K) p) :
    Conditions (cyclotomicRamifiedPhase hζ hodd) where
  odd := hodd
  three_le := hp3
  ramification := cyclotomicRamifiedPhase_prime_dvd hζ hodd
  class_group := hfree
  unit_power := hunit

/-- Threefold positive-depth states, via the general reconstruction. -/
theorem no_cubic_state [IsCyclotomicExtension {3} ℚ K] {ζ : K}
    (hζ : IsPrimitiveRoot ζ 3) (m : ℕ) (hm : 1 ≤ m) :
    ¬ Nonempty (State (cyclotomicRamifiedPhase hζ (by decide)) m) := by
  have hfree : classGroupPTorsionFreeAt (𝓞 K) 3 :=
    classGroupPTorsionFreeAt_of_coprime_card (by rw [cubic_classGroup_card_eq_one hζ]; decide)
  exact no_state (cyclotomic_conditions hζ (by decide) (by decide) hfree
    (cubic_kummer_unit_power_criterion hζ)) m hm

/-- Fivefold positive-depth states, via the same general reconstruction. -/
theorem no_quintic_state [IsCyclotomicExtension {5} ℚ K] {ζ : K}
    (hζ : IsPrimitiveRoot ζ 5) (m : ℕ) (hm : 1 ≤ m) :
    ¬ Nonempty (State (cyclotomicRamifiedPhase hζ (by decide)) m) := by
  have hfree : classGroupPTorsionFreeAt (𝓞 K) 5 :=
    classGroupPTorsionFreeAt_of_coprime_card (by rw [quintic_classGroup_card_eq_one]; decide)
  exact no_state (cyclotomic_conditions hζ (by decide) (by decide) hfree
    (quintic_kummer_unit_power_criterion hζ)) m hm

end DkMath.FLT.Kummer.RegularDescent
