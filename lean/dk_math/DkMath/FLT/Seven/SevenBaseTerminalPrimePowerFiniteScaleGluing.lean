/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenBaseTerminalPrimeScaleFamily
import Mathlib.Data.Nat.GCD.BigOperators

#print "file: DkMath.FLT.Seven.SevenBaseTerminalPrimePowerFiniteScaleGluing"

namespace DkMath.FLT.Seven

namespace AwaySevenBaseTerminalPrimeScaleFamily

/-- The product of the complete local prime-power moduli over the canonical
terminal prime support. -/
def combinedModulus
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {packet : AwaySevenBaseTerminalRoutingPacket (source := source) p}
    (family : AwaySevenBaseTerminalPrimeScaleFamily packet) : ℕ :=
  ∏ q : AwaySevenBaseTerminalPrimeIndex r, family.localModulus q

/-- The product of the complete local moduli over a finite subfamily. -/
def accumulatedModulus
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {packet : AwaySevenBaseTerminalRoutingPacket (source := source) p}
    (family : AwaySevenBaseTerminalPrimeScaleFamily packet)
    (support : Finset (AwaySevenBaseTerminalPrimeIndex r)) : ℕ :=
  ∏ q ∈ support, family.localModulus q

/-- The complete local moduli form a pairwise coprime family on the canonical
terminal prime support. -/
theorem localModuli_pairwise_coprime
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {packet : AwaySevenBaseTerminalRoutingPacket (source := source) p}
    (family : AwaySevenBaseTerminalPrimeScaleFamily packet) :
    Pairwise (fun q₁ q₂ =>
      Nat.Coprime (family.localModulus q₁) (family.localModulus q₂)) := by
  intro q₁ q₂ hneq
  exact family.localModulus_coprime q₁ q₂ hneq

/-- Every complete local modulus divides the product modulus over the full
canonical support. -/
theorem localModulus_dvd_combinedModulus
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {packet : AwaySevenBaseTerminalRoutingPacket (source := source) p}
    (family : AwaySevenBaseTerminalPrimeScaleFamily packet)
    (q : AwaySevenBaseTerminalPrimeIndex r) :
    family.localModulus q ∣ family.combinedModulus := by
  rw [combinedModulus]
  exact Finset.dvd_prod_of_mem family.localModulus (Finset.mem_univ q)

/-- Every modulus already inserted into a finite subfamily divides its
accumulated product. -/
theorem localModulus_dvd_accumulatedModulus
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {packet : AwaySevenBaseTerminalRoutingPacket (source := source) p}
    (family : AwaySevenBaseTerminalPrimeScaleFamily packet)
    {support : Finset (AwaySevenBaseTerminalPrimeIndex r)}
    {q : AwaySevenBaseTerminalPrimeIndex r} (hq : q ∈ support) :
    family.localModulus q ∣ family.accumulatedModulus support := by
  rw [accumulatedModulus]
  exact Finset.dvd_prod_of_mem family.localModulus hq

/-- A complete local modulus not yet inserted into a finite subfamily is
coprime to the accumulated product.  This is the induction-step arithmetic
needed by finite CRT gluing. -/
theorem accumulatedModulus_coprime_localModulus
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {packet : AwaySevenBaseTerminalRoutingPacket (source := source) p}
    (family : AwaySevenBaseTerminalPrimeScaleFamily packet)
    (support : Finset (AwaySevenBaseTerminalPrimeIndex r))
    (q : AwaySevenBaseTerminalPrimeIndex r) (hq : q ∉ support) :
    Nat.Coprime (family.accumulatedModulus support)
      (family.localModulus q) := by
  rw [accumulatedModulus, Nat.coprime_prod_left_iff]
  intro i hi
  apply family.localModulus_coprime i q
  intro hiq
  apply hq
  simpa [hiq] using hi

/-- The full product with one index removed is coprime to that index's complete
local modulus. -/
theorem combinedModulus_erase_coprime_localModulus
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {packet : AwaySevenBaseTerminalRoutingPacket (source := source) p}
    (family : AwaySevenBaseTerminalPrimeScaleFamily packet)
    (q : AwaySevenBaseTerminalPrimeIndex r) :
    Nat.Coprime
      (family.accumulatedModulus
        (Finset.univ.erase q))
      (family.localModulus q) :=
  family.accumulatedModulus_coprime_localModulus
    (Finset.univ.erase q) q (by simp)

end AwaySevenBaseTerminalPrimeScaleFamily

end DkMath.FLT.Seven
