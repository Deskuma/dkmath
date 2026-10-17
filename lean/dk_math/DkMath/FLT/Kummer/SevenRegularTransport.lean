/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Kummer.RegularStateTransport
import DkMath.FLT.Kummer.SevenDescentPhases
import DkMath.FLT.Kummer.SevenKummerUnit

#print "file: DkMath.FLT.Kummer.SevenRegularTransport"

/-!
# Independent sevenfold regression of general state transport

This uses the old sevenfold state carrier and arithmetic providers, but neither
the old descent step nor a completed FLT theorem. The two slope definitions
agree by their ramified-factor witnesses. R1 is first exposed on the old phase
quotients, independently of the proof that positive-depth states are impossible.
-/

namespace DkMath.FLT.Kummer.SevenDescent

open DkMath.Lib.NumberTheory
open DkMath.FLT.Seven DkMath.FLT.Kummer.SevenPrimaryNorm
open DkMath.FLT.Kummer.SevenRealGN SevenCyclotomicDegreeSixInt

noncomputable section

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩
local notation "CC" => SevenCyclotomicDegreeSixInt.Ring

/-- Existing degree-six integer ring, with its genuine residue map. -/
def regularPhasePacket : RamifiedPhasePacket CC 7 where
  zeta := zeta
  primitive := zeta_isPrimitiveRoot
  lambda := ramifiedUniformizer
  lambda_eq := rfl
  lambda_prime := by
    apply (Ideal.span_singleton_prime ramifiedUniformizer_ne_zero).mp
    rw [← ramifiedPrime_eq_span_uniformizer]
    exact ramifiedPrime_isMaximal.isPrime
  residue := ramifiedEval
  residue_zero_iff := ramifiedEval_eq_zero_iff_dvd
  residue_zeta := by
    have h := ramifiedEval_uniformizer
    change ramifiedEval (1 - zeta) = 0 at h
    rw [map_sub, map_one, sub_eq_zero] at h
    exact h.symm

/-- New geometric-sum slopes recover the existing sevenfold slopes exactly. -/
theorem regular_slope_eq (i : Fin 7) : regularPhasePacket.slope i = phaseSlope i := by
  apply mul_right_cancel₀ ramifiedUniformizer_ne_zero
  exact (regularPhasePacket.slope_spec i).trans (phaseSlope_spec i).symm

/-- New and old normalized factors agree for any shared center, without a State. -/
theorem regular_quotient_eq (q y : CC) (i : Fin 7) :
    regularPhasePacket.quotient q y i = q + phaseSlope i * y := by
  rw [RamifiedPhasePacket.quotient, regular_slope_eq]

/-- Preserve all sevenfold state data when entering the general mechanism. -/
def State.toRegular {m : ℕ} (E : State m) : RegularDescent.State regularPhasePacket m where
  x := E.x
  y := E.y
  z := E.z
  epsilon := E.epsilon
  coprime := E.coprime
  y_away := E.y_away
  z_away := E.z_away
  equation := E.equation

/-- Return every invariant of the general successor to the old carrier. -/
def ofRegular {m : ℕ} (E : RegularDescent.State regularPhasePacket m) : State m where
  x := E.x
  y := E.y
  z := E.z
  epsilon := E.epsilon
  coprime := E.coprime
  y_away := E.y_away
  z_away := E.z_away
  equation := E.equation

/-- The general distinguished phase agrees with the old residue-coordinate choice. -/
theorem State.regular_distinguished_eq {m : ℕ} (E : State m) (hm : 1 ≤ m) :
    regularPhasePacket.distinguished (E.center hm) E.y = E.distinguishedPhase hm := rfl

/-- NST-003: arbitrary ramified depth is concentrated in the actual old quotient. -/
theorem State.ramified_depth_dvd_iff {m : ℕ} (E : State m) (hm : 1 ≤ m) (k : ℕ) :
    ramifiedUniformizer ^ (7 + k) ∣ E.x ^ 7 + E.y ^ 7 ↔
      ramifiedUniformizer ^ k ∣ E.quotient hm (E.distinguishedPhase hm) := by
  have h := regularPhasePacket.sum_dvd_iff (by decide) E.x E.y (E.center hm)
    (E.center_spec hm) E.y_away k
  simpa only [State.regular_distinguished_eq, regular_quotient_eq, State.quotient,
    show regularPhasePacket.lambda = ramifiedUniformizer from rfl] using h

/-- Genuine arithmetic providers; this does not assume a transition or an FLT endpoint. -/
theorem regularConditions : RegularDescent.Conditions regularPhasePacket where
  odd := by decide
  three_le := by decide
  ramification := seven_dvd_uniformizer_six
  class_group := classGroupPTorsionFreeAt_of_isPrincipalIdealRing 7
  unit_power := concrete_kummer_unit_power_criterion

/-- Recover sevenfold descent from the new general reconstruction, independently. -/
theorem descent_step_via_regular (m : ℕ) (hm : 1 ≤ m) :
    Nonempty (State (m + 1)) → Nonempty (State m) := by
  rintro ⟨E⟩
  obtain ⟨E'⟩ := RegularDescent.descent_step regularConditions m hm ⟨E.toRegular⟩
  exact ⟨ofRegular E'⟩

/-- Positive sevenfold states are excluded by the general mechanism. -/
theorem no_state_via_regular (m : ℕ) (hm : 1 ≤ m) : ¬ Nonempty (State m) := by
  rintro ⟨E⟩
  exact RegularDescent.no_state regularConditions m hm ⟨E.toRegular⟩

end
end DkMath.FLT.Kummer.SevenDescent
