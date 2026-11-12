/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Kummer.ElevenRegularTransport
import DkMath.FLT.Kummer.ThirteenRegularTransport

#print "file: DkMathTest.FLT.Kummer.ElevenThirteenRegularTransport"

/-! The public endpoints must require no arithmetic provider, only a genuine
cyclotomic field and a primitive root. All the descent logic remains shared. -/

namespace ElevenThirteenRegularTransportRegression

universe u

open DkMath.Lib.NumberTheory DkMath.FLT.Kummer DkMath.FLT.Kummer.RegularDescent
open scoped NumberField

local instance : Fact (Nat.Prime 11) := ⟨by decide⟩
local instance : Fact (Nat.Prime 13) := ⟨by decide⟩
local instance (p : ℕ) [NeZero p] : IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ) :=
  CyclotomicField.isCyclotomicExtension p ℚ

example {K : Type u} [Field K] [NumberField K] [IsCyclotomicExtension {11} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ 11) (m : ℕ) (hm : 1 ≤ m) :
    ¬ Nonempty (State (cyclotomicRamifiedPhase hζ (by decide)) m) :=
  no_eleven_state hζ m hm

example {K : Type u} [Field K] [NumberField K] [IsCyclotomicExtension {13} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ 13) (m : ℕ) (hm : 1 ≤ m) :
    ¬ Nonempty (State (cyclotomicRamifiedPhase hζ (by decide)) m) :=
  no_thirteen_state hζ m hm

-- Both tests use actual fields, not hypothetical providers or already impossible states.
example (m : ℕ) (hm : 1 ≤ m) : ¬ Nonempty (State
    (cyclotomicRamifiedPhase
      (IsCyclotomicExtension.zeta_spec 11 ℚ (CyclotomicField 11 ℚ)) (by decide)) m) :=
  no_eleven_state _ m hm

example (m : ℕ) (hm : 1 ≤ m) : ¬ Nonempty (State
    (cyclotomicRamifiedPhase
      (IsCyclotomicExtension.zeta_spec 13 ℚ (CyclotomicField 13 ℚ)) (by decide)) m) :=
  no_thirteen_state _ m hm

example : classGroupPTorsionFreeAt (𝓞 (CyclotomicField 11 ℚ)) 11 :=
  eleven_classGroup_torsion_free
example : classGroupPTorsionFreeAt (𝓞 (CyclotomicField 13 ℚ)) 13 :=
  thirteen_classGroup_torsion_free
example : KummerUnitPowerCriterion (𝓞 (CyclotomicField 11 ℚ)) 11 :=
  eleven_kummer_unit_power_criterion
example : KummerUnitPowerCriterion (𝓞 (CyclotomicField 13 ℚ)) 13 :=
  thirteen_kummer_unit_power_criterion

-- Depth zero remains inhabited; the positive-depth hypothesis has not been erased.
example : Nonempty (State
    (cyclotomicRamifiedPhase
      (IsCyclotomicExtension.zeta_spec 11 ℚ (CyclotomicField 11 ℚ)) (by decide)) 0) := by
  let P := cyclotomicRamifiedPhase
    (IsCyclotomicExtension.zeta_spec 11 ℚ (CyclotomicField 11 ℚ)) (by decide)
  exact ⟨{
    x := 0, y := 1, z := 1, epsilon := 1
    coprime := isCoprime_one_right
    y_away := P.lambda_prime.not_dvd_one
    z_away := P.lambda_prime.not_dvd_one
    equation := by simp }⟩

#print axioms CyclotomicElevenPID.eleven_pid
#print axioms CyclotomicThirteenPID.thirteen_pid
#print axioms regular_kummer_unit_power_criterion
#print axioms no_eleven_state
#print axioms no_thirteen_state

end ElevenThirteenRegularTransportRegression
