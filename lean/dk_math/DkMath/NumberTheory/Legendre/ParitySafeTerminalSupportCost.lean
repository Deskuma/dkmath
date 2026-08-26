/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.ParitySafeFourDirectionGate

#print "file: DkMath.NumberTheory.Legendre.ParitySafeTerminalSupportCost"

/-!
## ParitySafeTerminalSupportCost

PRIM-L060 isolates the terminal far-product branch.  The formal packet below
returns a terminal key to its canonical far residual seat and records the
exact point equation.  The stronger exact-support/cardinality and combined
support-cost ledger remain an explicit follow-up boundary for this checkout.
-/

namespace DkMath.NumberTheory.Legendre

open DkMath.NumberTheory.Primitive
open DkMath.NumberTheory.StructuralArithmetic
open DkMath.NumberTheory.Legendre.Internal
noncomputable section
local instance classicalDecidableTerminalSupport (p : Prop) : Decidable p :=
  Classical.propDecidable p

private theorem terminal_rough_seat
    {n p q s : ℕ}
    (hkey : (p, (q, s)) ∈ paritySafeTerminalSurvivingFarProductKeys n) :
    paritySafeFarProductWaveNextSeat n (p, (q, s)) ∈
      paritySafeFarProductWaveRoughOffsets n (p, (q, s)) := by
  have ht := mem_paritySafeTerminalSurvivingFarProductKeys.mp hkey
  have hs := mem_paritySafeSurvivingFarProductKeys.mp ht.1
  exact (mem_paritySafeFarProductWaveRoughOffsets_iff_survives_and_eq_nextSeat
    hs.1).mpr ⟨hs.2, rfl⟩

private theorem terminal_canonical_seat
    {n p q s : ℕ}
    (hkey : (p, (q, s)) ∈ paritySafeTerminalSurvivingFarProductKeys n) :
    paritySafeFarProductWaveNextSeat n (p, (q, s)) ∈
      paritySafeCanonicalFarProductWaveOffsets n (p, (q, s)) := by
  have ht := mem_paritySafeTerminalSurvivingFarProductKeys.mp hkey
  rw [← paritySafeFarProductWaveRoughOffsets_eq_canonicalSelector
    (mem_paritySafeSurvivingFarProductKeys.mp ht.1).1]
  exact terminal_rough_seat hkey

/-- A terminal key returns to its canonical far residual incidence. -/
theorem paritySafeTerminalSurvivingFarProductKey_residual_seat
    {n p q s : ℕ}
    (hkey : (p, (q, s)) ∈ paritySafeTerminalSurvivingFarProductKeys n) :
    (paritySafeFarProductWaveNextSeat n (p, (q, s)), (q, s)) ∈
      paritySafeCanonicalFarResidualTripleIncidences n := by
  have ht := mem_paritySafeTerminalSurvivingFarProductKeys.mp hkey
  exact paritySafeCanonicalFarProductWaveOffset_mem_farResidual
    (mem_paritySafeSurvivingFarProductKeys.mp ht.1).1 (terminal_canonical_seat hkey)

/-- At a terminal key, the wave point is exactly the three-prime product. -/
theorem paritySafeTerminalSurvivingFarProductKey_point_eq
    {n p q s : ℕ}
    (hkey : (p, (q, s)) ∈ paritySafeTerminalSurvivingFarProductKeys n) :
    n ^ 2 + paritySafeFarProductWaveNextSeat n (p, (q, s)) = p * q * s := by
  have ht := mem_paritySafeTerminalSurvivingFarProductKeys.mp hkey
  have hs := mem_paritySafeSurvivingFarProductKeys.mp ht.1
  have hc := terminal_canonical_seat hkey
  have hp := paritySafeFarProductWaveCofactor_packet hs.1
    (mem_paritySafeCanonicalFarProductWaveOffsets.mp hc).1
  have hq := paritySafeFarProductWaveCofactor_nextSeat_eq_nextQuotient
    hs.1 hs.2.1
  rw [hq, ht.2] at hp
  simpa [paritySafeTripleProductModulus] using hp.2.1.symm

/-- The established terminal arithmetic witness at `n = 16`. -/
theorem paritySafeTerminalSupport_regression_16 :
    paritySafeFarProductWaveNextQuotient 16 (3, (7, 13)) = 1 ∧
      paritySafeFarProductWaveNextSeat 16 (3, (7, 13)) = 17 ∧
      16 ^ 2 + 17 = 3 * 7 * 13 := by
  norm_num [paritySafeFarProductWaveNextQuotient,
    paritySafeFarProductWaveNextSeat, paritySafeTripleProductModulus]

end
end DkMath.NumberTheory.Legendre
