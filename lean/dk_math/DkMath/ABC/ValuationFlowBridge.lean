/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.ABC.MassBridge
import DkMath.ABC.PadicValNat
import DkMath.NumberTheory.ValuationFlow.Primitive

#print "file: DkMath.ABC.ValuationFlowBridge"

namespace DkMath.ABC

open DkMath.NumberTheory.ValuationFlow

/--
Primitive witness viewed as a prime channel on the diff side.

This is the minimal adapter from valuation-flow witnesses to the ABC
support-mass/channel vocabulary.
-/
theorem primitive_witness_gives_prime_channel_on_diff
    {q a b d : ℕ}
    (hq : PrimitivePrimeFlowWitness q a b d) :
    Nat.Prime q ∧ q ∣ a ^ d - b ^ d := by
  exact ⟨primitivePrimeFlow_prime hq, primitivePrimeFlow_dvd_diff hq⟩

/--
Two distinct primitive witnesses provide two distinct prime channels on the diff
side.
-/
theorem distinct_primitive_witnesses_give_distinct_prime_channels
    {q₁ q₂ a b d : ℕ}
    (hq₁ : PrimitivePrimeFlowWitness q₁ a b d)
    (hq₂ : PrimitivePrimeFlowWitness q₂ a b d)
    (hneq : q₁ ≠ q₂) :
    q₁ ≠ q₂ ∧ Nat.Prime q₁ ∧ Nat.Prime q₂ ∧
      q₁ ∣ a ^ d - b ^ d ∧ q₂ ∣ a ^ d - b ^ d := by
  exact ⟨hneq, primitivePrimeFlow_prime hq₁, primitivePrimeFlow_prime hq₂,
    primitivePrimeFlow_dvd_diff hq₁, primitivePrimeFlow_dvd_diff hq₂⟩

/--
Two distinct primitive channels force a support-mass lower bound on the diff.

This is the primitive-flow shadow of the two-channel lower bound on `rad`.
-/
theorem primitive_channels_force_supportMass_lower_bound
    {q₁ q₂ a b d : ℕ}
    (hq₁ : PrimitivePrimeFlowWitness q₁ a b d)
    (hq₂ : PrimitivePrimeFlowWitness q₂ a b d)
    (hneq : q₁ ≠ q₂)
    (hdiff_ne : a ^ d - b ^ d ≠ 0) :
    q₁ * q₂ ≤ supportMass (a ^ d - b ^ d) := by
  exact supportMass_ge_of_two_distinct_prime_channels
    (n := a ^ d - b ^ d)
    (p := q₁)
    (q := q₂)
    hdiff_ne
    (primitivePrimeFlow_prime hq₁)
    (primitivePrimeFlow_prime hq₂)
    hneq
    (primitivePrimeFlow_dvd_diff hq₁)
    (primitivePrimeFlow_dvd_diff hq₂)

/-- Primitive primes contribute no boundary load. -/
theorem primitive_prime_gives_zero_boundary_load
    {q a b d : ℕ}
    (hq : PrimitivePrimeFlowWitness q a b d)
    (hd1 : 1 < d) :
    boundaryMass q a b = 0 := by
  exact primitivePrimeFlow_boundaryMass_eq_zero hq hd1

/-- Primitive primes transfer all diff load to the beam factor. -/
theorem primitive_prime_transfers_diff_load_to_beam
    {q a b d : ℕ}
    (hq : PrimitivePrimeFlowWitness q a b d)
    (hd : 0 < d) (hd1 : 1 < d)
    (hab_lt : b < a) :
    diffMass q a b d = beamMass q a b d := by
  exact primitivePrimeFlow_diffMass_eq_beamMass hq hd hd1 hab_lt

/--
Under a squarefree beam hypothesis, the local diff load is bounded by `1`.
-/
theorem squarefree_beam_bounds_local_load
    {q a b d : ℕ}
    (hd_prime : Nat.Prime d) (hd_ge : 3 ≤ d)
    (hab_lt : b < a) (hb : 0 < b) (hab : Nat.Coprime a b)
    (hpnd : ¬ d ∣ a - b)
    (hq : PrimitivePrimeFlowWitness q a b d)
    (hG_sq : Squarefree (DkMath.CosmicFormulaBinom.GN d (a - b) b)) :
    diffMass q a b d ≤ 1 := by
  exact primitivePrimeFlow_diffMass_le_one_of_squarefree_beam
    hd_prime hd_ge hab_lt hb hab hpnd hq hG_sq

end DkMath.ABC
