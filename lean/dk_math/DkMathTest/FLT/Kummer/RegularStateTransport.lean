/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Kummer.CyclotomicRegularTransport
import DkMath.FLT.Kummer.SevenRegularTransport
import DkMathTest.Lib.Cosmic.CoreNested

#print "file: DkMathTest.FLT.Kummer.RegularStateTransport"

namespace RegularStateTransportRegression

open DkMath.Lib.NumberTheory DkMath.FLT.Kummer
open scoped NumberField

section PhaseTests

variable {R : Type*} [CommRing R] [IsDomain R]
variable {p : ℕ} [hp : Fact p.Prime] (P : RamifiedPhasePacket R p)

-- Two actual nonzero centers distinguish Gap storage from GN storage.
theorem distinguished_zero : P.distinguished P.lambda 1 = ⟨0, hp.out.pos⟩ := by
  have hlam : P.residue P.lambda = 0 := (P.residue_zero_iff _).mpr dvd_rfl
  apply Fin.ext
  simp [RamifiedPhasePacket.distinguished, hlam]

theorem distinguished_one : P.distinguished (1 + P.lambda) 1 = ⟨1, hp.out.one_lt⟩ := by
  have hlam : P.residue P.lambda = 0 := (P.residue_zero_iff _).mpr dvd_rfl
  apply Fin.ext
  simp [RamifiedPhasePacket.distinguished, hlam, ZMod.val_one]

theorem gap_holds_extra_depth :
    ¬ P.lambda ^ p ∣ DkMath.CosmicFormula.GTail p 1 (P.lambda * P.lambda) (-1) :=
  P.not_dvd_gtail_of_distinguished_zero P.lambda 1 P.lambda_prime.not_dvd_one
    (distinguished_zero P)

theorem gn_holds_extra_depth :
    P.lambda ^ p ∣ DkMath.CosmicFormula.GTail p 1 (P.lambda * (1 + P.lambda)) (-1) := by
  have hi : P.distinguished (1 + P.lambda) 1 ≠ ⟨0, hp.out.pos⟩ := by
    rw [distinguished_one]
    simp only [ne_eq, Fin.ext_iff]
    decide
  have h := P.gtail_dvd_iff_of_distinguished_ne_zero (1 + P.lambda) 1
    P.lambda_prime.not_dvd_one hi 1
  have he : p - 1 + 1 = p := by have := hp.out.pos; omega
  have hd : P.lambda ^ 1 ∣ P.quotient (1 + P.lambda) 1 (P.distinguished (1 + P.lambda) 1) := by
    rw [distinguished_one]
    simp [RamifiedPhasePacket.quotient, RamifiedPhasePacket.slope]
  simpa only [he] using h.mpr hd

-- Zero Core is allowed: every ramified power divides it.
example (k : ℕ) :
    P.lambda ^ (p + k) ∣ DkMath.Lib.Cosmic.powerCore p (-1) (P.lambda * 0) := by simp

end PhaseTests

noncomputable section

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
local instance : Fact (Nat.Prime 11) := ⟨by decide⟩
local instance : Fact (Nat.Prime 13) := ⟨by decide⟩

local instance (n : ℕ) [NeZero n] : IsCyclotomicExtension {n} ℚ (CyclotomicField n ℚ) :=
  CyclotomicField.isCyclotomicExtension n ℚ

-- Concrete carriers ensure phase-zero handling works beyond the three old degrees.
def eleven : RamifiedPhasePacket (𝓞 (CyclotomicField 11 ℚ)) 11 :=
  cyclotomicRamifiedPhase (IsCyclotomicExtension.zeta_spec 11 ℚ (CyclotomicField 11 ℚ)) (by decide)

def thirteen : RamifiedPhasePacket (𝓞 (CyclotomicField 13 ℚ)) 13 :=
  cyclotomicRamifiedPhase (IsCyclotomicExtension.zeta_spec 13 ℚ (CyclotomicField 13 ℚ)) (by decide)

example : eleven.distinguished eleven.lambda 1 = ⟨0, by decide⟩ := distinguished_zero eleven
example : thirteen.distinguished thirteen.lambda 1 = ⟨0, by decide⟩ := distinguished_zero thirteen
example : ¬ eleven.lambda ^ 11 ∣ DkMath.CosmicFormula.GTail 11 1
    (eleven.lambda * eleven.lambda) (-1) := gap_holds_extra_depth eleven
example : thirteen.lambda ^ 13 ∣ DkMath.CosmicFormula.GTail 13 1
    (thirteen.lambda * (1 + thirteen.lambda)) (-1) := gn_holds_extra_depth thirteen

-- No unit/class-number provider is asserted for degrees 11 and 13 here.
example : ¬ Nonempty (RegularDescent.State eleven 1) := RegularDescent.no_state_one (by decide)
example : ¬ Nonempty (RegularDescent.State thirteen 1) := RegularDescent.no_state_one (by decide)

example (m : ℕ) (hm : 1 ≤ m) : ¬ Nonempty (RegularDescent.State
    (cyclotomicRamifiedPhase
      (IsCyclotomicExtension.zeta_spec 3 ℚ (CyclotomicField 3 ℚ)) (by decide)) m) :=
  RegularDescent.no_cubic_state _ m hm
example (m : ℕ) (hm : 1 ≤ m) : ¬ Nonempty (RegularDescent.State
    (cyclotomicRamifiedPhase
      (IsCyclotomicExtension.zeta_spec 5 ℚ (CyclotomicField 5 ℚ)) (by decide)) m) :=
  RegularDescent.no_quintic_state _ m hm
example (m : ℕ) (hm : 1 ≤ m) : ¬ Nonempty (SevenDescent.State m) :=
  SevenDescent.no_state_via_regular m hm

-- Depth zero really is inhabited, so the positive-depth guard is essential.
example : Nonempty (RegularDescent.State eleven 0) := by
  exact ⟨{
    x := 0, y := 1, z := 1, epsilon := 1
    coprime := isCoprime_one_right
    y_away := eleven.lambda_prime.not_dvd_one
    z_away := eleven.lambda_prime.not_dvd_one
    equation := by simp }⟩

#print axioms RamifiedPhasePacket.powerCore_dvd_iff
#print axioms RamifiedPhasePacket.gtail_eq_product
#print axioms RegularDescent.State.exists_quotient_roots
#print axioms RegularDescent.descent_step
#print axioms RegularDescent.no_state
#print axioms RegularDescent.no_cubic_state
#print axioms RegularDescent.no_quintic_state
#print axioms SevenDescent.descent_step_via_regular
#print axioms SevenDescent.State.ramified_depth_dvd_iff

end
end RegularStateTransportRegression
