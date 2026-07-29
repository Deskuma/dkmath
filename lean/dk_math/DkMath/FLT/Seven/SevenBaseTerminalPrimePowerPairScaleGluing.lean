/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenBaseTerminalPrimePowerScaleProjection
import Mathlib.Data.ZMod.Basic

#print "file: DkMath.FLT.Seven.SevenBaseTerminalPrimePowerPairScaleGluing"

namespace DkMath.FLT.Seven

/-- Two distinct terminal prime scales glued by the binary Chinese remainder
isomorphism at the product of their complete prime-power moduli. -/
structure AwaySevenBaseTerminalPrimePowerPairScaleGluingPacket
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    (packet : AwaySevenBaseTerminalRoutingPacket (source := source) p)
    (q₁ q₂ : ℕ) : Type where
  first : AwaySevenBaseTerminalPrimePowerScaleProjectionPacket packet q₁
  second : AwaySevenBaseTerminalPrimePowerScaleProjectionPacket packet q₂
  primes_ne : q₁ ≠ q₂
  moduli_coprime : Nat.Coprime first.orbitPacket.depthPacket.depth.modulus
    second.orbitPacket.depthPacket.depth.modulus
  combinedScale : ZMod (first.orbitPacket.depthPacket.depth.modulus *
    second.orbitPacket.depthPacket.depth.modulus)
  reductions : ZMod.chineseRemainder moduli_coprime combinedScale =
    (first.localScale, second.localScale)

/-- Complete prime-power moduli attached to two distinct terminal primes are
coprime. -/
theorem AwaySevenBaseTerminalPrimePowerScaleProjectionPacket.modulus_coprime_of_prime_ne
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {packet : AwaySevenBaseTerminalRoutingPacket (source := source) p}
    {q₁ q₂ : ℕ}
    (first : AwaySevenBaseTerminalPrimePowerScaleProjectionPacket packet q₁)
    (second : AwaySevenBaseTerminalPrimePowerScaleProjectionPacket packet q₂)
    (hneq : q₁ ≠ q₂) :
    Nat.Coprime first.orbitPacket.depthPacket.depth.modulus
      second.orbitPacket.depthPacket.depth.modulus := by
  have hdepth_ne : first.orbitPacket.depthPacket.depth.q ≠
      second.orbitPacket.depthPacket.depth.q := by
    intro h
    apply hneq
    calc
      q₁ = first.orbitPacket.depthPacket.depth.q :=
        first.orbitPacket.depthPacket.depth_q_eq.symm
      _ = second.orbitPacket.depthPacket.depth.q := h
      _ = q₂ := second.orbitPacket.depthPacket.depth_q_eq
  simpa [AwayNonSevenPrimeDepthPacket.modulus] using
    Nat.coprime_pow_primes
      first.orbitPacket.depthPacket.depth.exponent
      second.orbitPacket.depthPacket.depth.exponent
      first.orbitPacket.depthPacket.depth.q_prime
      second.orbitPacket.depthPacket.depth.q_prime hdepth_ne

/-- Glue two distinct terminal local scales into one residue class modulo the
product of their complete prime-power moduli. -/
noncomputable def AwaySevenBaseTerminalPrimePowerScaleProjectionPacket.pairScaleGluingPacket
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {packet : AwaySevenBaseTerminalRoutingPacket (source := source) p}
    {q₁ q₂ : ℕ}
    (first : AwaySevenBaseTerminalPrimePowerScaleProjectionPacket packet q₁)
    (second : AwaySevenBaseTerminalPrimePowerScaleProjectionPacket packet q₂)
    (hneq : q₁ ≠ q₂) :
    AwaySevenBaseTerminalPrimePowerPairScaleGluingPacket packet q₁ q₂ := by
  let hcoprime := first.modulus_coprime_of_prime_ne second hneq
  let combined := (ZMod.chineseRemainder hcoprime).symm
    (first.localScale, second.localScale)
  exact {
    first := first
    second := second
    primes_ne := hneq
    moduli_coprime := hcoprime
    combinedScale := combined
    reductions := (ZMod.chineseRemainder hcoprime).apply_symm_apply
      (first.localScale, second.localScale) }

/-- Every pair of distinct primes dividing the terminal cubic root load admits
one simultaneous CRT scale modulo the product of their exact local moduli. -/
theorem AwaySevenBaseTerminalRoutingPacket.nonempty_pairScaleGluingPacket_of_dvd_cubicRootLoad
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    (packet : AwaySevenBaseTerminalRoutingPacket (source := source) p)
    {q₁ q₂ : ℕ} (hq₁ : Nat.Prime q₁) (hq₂ : Nat.Prime q₂)
    (hneq : q₁ ≠ q₂)
    (hq₁Load : q₁ ∣ awaySevenBaseTerminalCubicRootLoad r)
    (hq₂Load : q₂ ∣ awaySevenBaseTerminalCubicRootLoad r) :
    Nonempty (AwaySevenBaseTerminalPrimePowerPairScaleGluingPacket packet q₁ q₂) := by
  rcases packet.nonempty_primePowerScaleProjectionPacket_of_dvd_cubicRootLoad hq₁ hq₁Load with
    ⟨first⟩
  rcases packet.nonempty_primePowerScaleProjectionPacket_of_dvd_cubicRootLoad hq₂ hq₂Load with
    ⟨second⟩
  exact ⟨first.pairScaleGluingPacket second hneq⟩

/-- The first CRT reduction recovers the first terminal local scale. -/
theorem AwaySevenBaseTerminalPrimePowerPairScaleGluingPacket.first_reduction
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {packet : AwaySevenBaseTerminalRoutingPacket (source := source) p}
    {q₁ q₂ : ℕ}
    (a : AwaySevenBaseTerminalPrimePowerPairScaleGluingPacket packet q₁ q₂) :
    (ZMod.chineseRemainder a.moduli_coprime a.combinedScale).1 =
      a.first.localScale :=
  congrArg Prod.fst a.reductions

/-- The second CRT reduction recovers the second terminal local scale. -/
theorem AwaySevenBaseTerminalPrimePowerPairScaleGluingPacket.second_reduction
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {packet : AwaySevenBaseTerminalRoutingPacket (source := source) p}
    {q₁ q₂ : ℕ}
    (a : AwaySevenBaseTerminalPrimePowerPairScaleGluingPacket packet q₁ q₂) :
    (ZMod.chineseRemainder a.moduli_coprime a.combinedScale).2 =
      a.second.localScale :=
  congrArg Prod.snd a.reductions

end DkMath.FLT.Seven
