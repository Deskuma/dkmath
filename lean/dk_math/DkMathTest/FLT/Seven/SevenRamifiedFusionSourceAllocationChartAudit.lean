/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenRamifiedFusionModFortyTwoCheapBoundaryAudit

#print "file: DkMathTest.FLT.Seven.SevenRamifiedFusionSourceAllocationChartAudit"

namespace DkMathTest.FLT.Seven

open DkMath.FLT.Seven

/-- Negative model for a bare abstract ledger, not for an actual source packet.
Even adding the cheap and modulus-one sixth-power filters does not force a
literal perfect-sixth complementary factor. -/
theorem abstractLedger_cheap_not_force_perfectSixth :
    ∃ M N V C : ℕ, 0 < M ∧ ¬ 7 ∣ M ∧ 0 < N ∧ ¬ 7 ∣ N ∧
      M * N = V * C ∧ Nat.Coprime M N ∧
      ModFortyTwoCheapAllocation M 1 ∧ SixthPowerAllocationSieve 1 (M / 1) ∧
      ¬ ∃ t : ℕ, M / 1 = t ^ 6 := by
  refine ⟨631, 1, 631, 1, by decide, by decide, by decide, by decide,
    rfl, by decide, mod42Cheap_family 0, mod42Cheap_family_sixthPower 0, ?_⟩
  rintro ⟨t, ht⟩
  norm_num only [Nat.div_one] at ht
  by_cases h : t ≤ 2
  · have hp := Nat.pow_le_pow_left h 6
    norm_num at hp
    omega
  · have hp := Nat.pow_le_pow_left (by omega : 3 ≤ t) 6
    norm_num at hp
    omega

example : ¬ (∀ M N V C : ℕ,
    0 < M → ¬ 7 ∣ M → 0 < N → ¬ 7 ∣ N →
    M * N = V * C → Nat.Coprime M N → ModFortyTwoCheapAllocation M 1 →
    SixthPowerAllocationSieve 1 (M / 1) → ∃ t : ℕ, M / 1 = t ^ 6) := by
  intro h
  rcases abstractLedger_cheap_not_force_perfectSixth with
    ⟨M, N, V, C, hM, hM7, hN, hN7, hprod, hcop, hcheap, hsix, hbad⟩
  exact hbad (h M N V C hM hM7 hN hN7 hprod hcop hcheap hsix)

example (q : ℕ) (hq : Nat.Prime q) : ¬ q ∣ (1 : ℕ) := hq.not_dvd_one

#print axioms DkMathTest.FLT.Seven.abstractLedger_cheap_not_force_perfectSixth

end DkMathTest.FLT.Seven
