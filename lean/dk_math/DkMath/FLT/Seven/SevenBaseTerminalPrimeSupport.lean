/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenBaseTerminalRootLoadAddress

#print "file: DkMath.FLT.Seven.SevenBaseTerminalPrimeSupport"

namespace DkMath.FLT.Seven

/-- The terminal cubic-root load is positive. -/
theorem awaySevenBaseTerminalCubicRootLoad_pos
    {x y z : ℕ} (r : AwayCubicRoutingPacket x y z) :
    0 < awaySevenBaseTerminalCubicRootLoad r := by
  exact Nat.mul_pos
    (Nat.mul_pos r.cubic.rootTriple.vPart_pos r.cubic.rootTriple.leftPart_pos)
    r.cubic.rootTriple.rightPart_pos

/-- The terminal cubic-root load is nonzero. -/
theorem awaySevenBaseTerminalCubicRootLoad_ne_zero
    {x y z : ℕ} (r : AwayCubicRoutingPacket x y z) :
    awaySevenBaseTerminalCubicRootLoad r ≠ 0 :=
  (awaySevenBaseTerminalCubicRootLoad_pos r).ne'

/-- The canonical finite support of primes dividing the terminal cubic-root
load. -/
def awaySevenBaseTerminalPrimeSupport
    {x y z : ℕ} (r : AwayCubicRoutingPacket x y z) : Finset ℕ :=
  Nat.primeFactors (awaySevenBaseTerminalCubicRootLoad r)

/-- Membership in the canonical terminal support is exactly primality together
with divisibility of the terminal cubic-root load. -/
theorem mem_awaySevenBaseTerminalPrimeSupport_iff
    {x y z q : ℕ} {r : AwayCubicRoutingPacket x y z} :
    q ∈ awaySevenBaseTerminalPrimeSupport r ↔
      Nat.Prime q ∧ q ∣ awaySevenBaseTerminalCubicRootLoad r := by
  rw [awaySevenBaseTerminalPrimeSupport, Nat.mem_primeFactors]
  constructor
  · rintro ⟨hq, hqLoad, _⟩
    exact ⟨hq, hqLoad⟩
  · rintro ⟨hq, hqLoad⟩
    exact ⟨hq, hqLoad, awaySevenBaseTerminalCubicRootLoad_ne_zero r⟩

/-- Every prime in the canonical terminal support is different from seven. -/
theorem AwaySevenBaseTerminalRoutingPacket.primeSupport_ne_seven
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    (packet : AwaySevenBaseTerminalRoutingPacket (source := source) p)
    {q : ℕ} (hq : q ∈ awaySevenBaseTerminalPrimeSupport r) :
    q ≠ 7 := by
  rw [mem_awaySevenBaseTerminalPrimeSupport_iff] at hq
  exact (packet.prime_dvd_cubicRootLoad_unique_global_address hq.1 hq.2).1

/-- A canonical index for a prime in the terminal cubic-root support. -/
abbrev AwaySevenBaseTerminalPrimeIndex
    {x y z : ℕ} (r : AwayCubicRoutingPacket x y z) :=
  {q : ℕ // q ∈ awaySevenBaseTerminalPrimeSupport r}

namespace AwaySevenBaseTerminalPrimeIndex

/-- The natural number underlying a terminal prime index is prime. -/
theorem prime
    {x y z : ℕ} {r : AwayCubicRoutingPacket x y z}
    (q : AwaySevenBaseTerminalPrimeIndex r) :
    Nat.Prime q.1 :=
  (mem_awaySevenBaseTerminalPrimeSupport_iff.mp q.2).1

/-- A terminal prime index divides the complete terminal cubic-root load. -/
theorem dvd_cubicRootLoad
    {x y z : ℕ} {r : AwayCubicRoutingPacket x y z}
    (q : AwaySevenBaseTerminalPrimeIndex r) :
    q.1 ∣ awaySevenBaseTerminalCubicRootLoad r :=
  (mem_awaySevenBaseTerminalPrimeSupport_iff.mp q.2).2

/-- A terminal prime index attached to a fixed terminal routing packet is not
seven. -/
theorem ne_seven
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    (packet : AwaySevenBaseTerminalRoutingPacket (source := source) p)
    (q : AwaySevenBaseTerminalPrimeIndex r) :
    q.1 ≠ 7 :=
  packet.primeSupport_ne_seven q.2

end AwaySevenBaseTerminalPrimeIndex

end DkMath.FLT.Seven
