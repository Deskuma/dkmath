/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenBaseTerminalPrimeSupport
import DkMath.FLT.Seven.SevenBaseTerminalPrimePowerPairScaleGluing

#print "file: DkMath.FLT.Seven.SevenBaseTerminalPrimeScaleFamily"

namespace DkMath.FLT.Seven

/-- One complete local scale projection packet chosen for every prime in the
canonical terminal cubic-root support. -/
structure AwaySevenBaseTerminalPrimeScaleFamily
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    (packet : AwaySevenBaseTerminalRoutingPacket (source := source) p) : Type where
  localPacket :
    (q : AwaySevenBaseTerminalPrimeIndex r) →
      AwaySevenBaseTerminalPrimePowerScaleProjectionPacket packet q.1

/-- Choose a complete local scale projection packet over every prime in the
canonical terminal support. -/
noncomputable def AwaySevenBaseTerminalRoutingPacket.primeScaleFamily
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    (packet : AwaySevenBaseTerminalRoutingPacket (source := source) p) :
    AwaySevenBaseTerminalPrimeScaleFamily packet where
  localPacket q :=
    Classical.choice
      (packet.nonempty_primePowerScaleProjectionPacket_of_dvd_cubicRootLoad
        q.prime q.dvd_cubicRootLoad)

namespace AwaySevenBaseTerminalPrimeScaleFamily

/-- The complete original routing-cell depth attached to a supported prime. -/
def localDepth
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {packet : AwaySevenBaseTerminalRoutingPacket (source := source) p}
    (family : AwaySevenBaseTerminalPrimeScaleFamily packet)
    (q : AwaySevenBaseTerminalPrimeIndex r) :
    AwayNonSevenPrimeDepthPacket r :=
  (family.localPacket q).orbitPacket.depthPacket.depth

/-- The exact complete prime-power modulus attached to a supported prime. -/
def localModulus
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {packet : AwaySevenBaseTerminalRoutingPacket (source := source) p}
    (family : AwaySevenBaseTerminalPrimeScaleFamily packet)
    (q : AwaySevenBaseTerminalPrimeIndex r) : ℕ :=
  family.localDepth q |>.modulus

/-- The local unit scale at the complete modulus of a supported prime. -/
def localScale
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {packet : AwaySevenBaseTerminalRoutingPacket (source := source) p}
    (family : AwaySevenBaseTerminalPrimeScaleFamily packet)
    (q : AwaySevenBaseTerminalPrimeIndex r) :
    ZMod (family.localModulus q) :=
  (family.localPacket q).localScale

/-- The chosen local scale is a unit at its complete prime-power modulus. -/
theorem localScale_isUnit
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {packet : AwaySevenBaseTerminalRoutingPacket (source := source) p}
    (family : AwaySevenBaseTerminalPrimeScaleFamily packet)
    (q : AwaySevenBaseTerminalPrimeIndex r) :
    IsUnit (family.localScale q) :=
  (family.localPacket q).localScale_isUnit

/-- The actual local prime-power solution chosen at a supported prime. -/
def localActual
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {packet : AwaySevenBaseTerminalRoutingPacket (source := source) p}
    (family : AwaySevenBaseTerminalPrimeScaleFamily packet)
    (q : AwaySevenBaseTerminalPrimeIndex r) :
    AwayRoutingPrimePowerSolution (family.localModulus q)
      (family.localDepth q).row (family.localDepth q).column :=
  (family.localPacket q).projection.actual

/-- The canonical local model chosen at a supported prime. -/
def localModel
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {packet : AwaySevenBaseTerminalRoutingPacket (source := source) p}
    (family : AwaySevenBaseTerminalPrimeScaleFamily packet)
    (q : AwaySevenBaseTerminalPrimeIndex r) :
    AwayRoutingPrimePowerSolution (family.localModulus q)
      (family.localDepth q).row (family.localDepth q).column :=
  (family.localPacket q).projection.model

/-- The chosen actual solution is the weight-(3,7) scaling of the chosen local
model by the chosen local unit scale. -/
theorem localActual_eq_weightedScale
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {packet : AwaySevenBaseTerminalRoutingPacket (source := source) p}
    (family : AwaySevenBaseTerminalPrimeScaleFamily packet)
    (q : AwaySevenBaseTerminalPrimeIndex r) :
    family.localActual q = scalePrimePowerSolution (family.localModel q)
      (family.localScale q) (family.localScale_isUnit q) :=
  (family.localPacket q).actual_eq_weightedScale

/-- Complete local moduli attached to distinct canonical prime indices are
coprime. -/
theorem localModulus_coprime
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {packet : AwaySevenBaseTerminalRoutingPacket (source := source) p}
    (family : AwaySevenBaseTerminalPrimeScaleFamily packet)
    (q₁ q₂ : AwaySevenBaseTerminalPrimeIndex r) (hneq : q₁ ≠ q₂) :
    Nat.Coprime (family.localModulus q₁) (family.localModulus q₂) := by
  have hvalue_ne : q₁.1 ≠ q₂.1 := by
    intro h
    apply hneq
    exact Subtype.ext h
  exact (family.localPacket q₁).modulus_coprime_of_prime_ne
    (family.localPacket q₂) hvalue_ne

end AwaySevenBaseTerminalPrimeScaleFamily

end DkMath.FLT.Seven
