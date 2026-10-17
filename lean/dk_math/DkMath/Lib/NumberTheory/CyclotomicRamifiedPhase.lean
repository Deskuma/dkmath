/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.RamifiedGNPhaseBridge
import DkMath.Lib.NumberTheory.CosmicRamifiedResidue

#print "file: DkMath.Lib.NumberTheory.CyclotomicRamifiedPhase"

/-!
# Cyclotomic provider for the ramified phase packet

This constructs the packet for every odd prime cyclotomic number field.
It uses `λ = 1 - ζ`, reversing the sign of the older `ζ - 1` residue API.
No regularity, unit-power criterion, or FLT theorem is required.
-/

namespace DkMath.Lib.NumberTheory

open scoped NumberField

/-- The genuine cyclotomic provider, uniform in the odd prime degree. -/
noncomputable def cyclotomicRamifiedPhase
    {K : Type*} [Field K] [NumberField K]
    {p : ℕ} [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) (hodd : Odd p) :
    RamifiedPhasePacket (𝓞 K) p where
  zeta := hζ.toInteger
  primitive := hζ.toInteger_isPrimitiveRoot
  lambda := 1 - hζ.toInteger
  lambda_eq := rfl
  lambda_prime := by
    simpa only [neg_sub] using (hζ.zeta_sub_one_prime').neg
  residue := ramifiedReduction hζ hodd
  residue_zero_iff := by
    intro a
    rw [ramifiedReduction_eq_zero_iff]
    rw [← neg_sub hζ.toInteger 1, neg_dvd]
  residue_zeta := ramifiedReduction_zeta hζ hodd

/-- Ramification supplies the modulus needed by weighted-state normalization. -/
theorem cyclotomicRamifiedPhase_prime_dvd
    {K : Type*} [Field K] [NumberField K]
    {p : ℕ} [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) (hodd : Odd p) :
    (p : 𝓞 K) ∣ (cyclotomicRamifiedPhase hζ hodd).lambda ^ (p - 1) := by
  change (p : 𝓞 K) ∣ (1 - hζ.toInteger) ^ (p - 1)
  have h := (IsCyclotomicExtension.Rat.associated_zeta_sub_one_pow_prime p hζ).dvd'
  rw [← neg_sub hζ.toInteger 1, neg_pow]
  exact dvd_mul_of_dvd_right h _

end DkMath.Lib.NumberTheory
