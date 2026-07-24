/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenBaseTerminalPrimePowerFiniteScaleGluing

#print "file: DkMath.FLT.Seven.SevenBaseTerminalPrimePowerFiniteScaleReduction"

namespace DkMath.FLT.Seven

/-- The canonical ring homomorphism reducing the combined product-modulus ring
to the complete local modulus at one terminal prime index. -/
noncomputable def AwaySevenBaseTerminalPrimeScaleFamily.reductionHom
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {packet : AwaySevenBaseTerminalRoutingPacket (source := source) p}
    (family : AwaySevenBaseTerminalPrimeScaleFamily packet)
    (q : AwaySevenBaseTerminalPrimeIndex r) :
    ZMod family.combinedModulus →+* ZMod (family.localModulus q) :=
  (Pi.evalRingHom
    (fun q : AwaySevenBaseTerminalPrimeIndex r =>
      ZMod (family.localModulus q)) q).comp
    (ZMod.prodEquivPi family.localModulus
      family.localModuli_pairwise_coprime).toRingHom

namespace AwaySevenBaseTerminalPrimePowerFiniteScaleGluingPacket

/-- Reduction of the combined scale at any supported prime recovers exactly
the chosen local scale. -/
theorem reduces_to_localScale
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {packet : AwaySevenBaseTerminalRoutingPacket (source := source) p}
    {family : AwaySevenBaseTerminalPrimeScaleFamily packet}
    (gluing :
      AwaySevenBaseTerminalPrimePowerFiniteScaleGluingPacket family)
    (q : AwaySevenBaseTerminalPrimeIndex r) :
    family.reductionHom q gluing.combinedScale = family.localScale q :=
  congrFun gluing.reductions q

/-- Every local scale recovered from the combined scale remains a unit. -/
theorem localScale_isUnit
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {packet : AwaySevenBaseTerminalRoutingPacket (source := source) p}
    {family : AwaySevenBaseTerminalPrimeScaleFamily packet}
    (_gluing :
      AwaySevenBaseTerminalPrimePowerFiniteScaleGluingPacket family)
    (q : AwaySevenBaseTerminalPrimeIndex r) :
    IsUnit (family.localScale q) :=
  family.localScale_isUnit q

/-- Reduction commutes with the cubic root-coordinate weight. -/
theorem reduction_pow_three
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {packet : AwaySevenBaseTerminalRoutingPacket (source := source) p}
    {family : AwaySevenBaseTerminalPrimeScaleFamily packet}
    (_gluing :
      AwaySevenBaseTerminalPrimePowerFiniteScaleGluingPacket family)
    (q : AwaySevenBaseTerminalPrimeIndex r)
    (a : ZMod family.combinedModulus) :
    family.reductionHom q (a ^ 3) = (family.reductionHom q a) ^ 3 :=
  map_pow (family.reductionHom q) a 3

/-- Reduction commutes with the seventh-power endpoint-coordinate weight. -/
theorem reduction_pow_seven
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {packet : AwaySevenBaseTerminalRoutingPacket (source := source) p}
    {family : AwaySevenBaseTerminalPrimeScaleFamily packet}
    (_gluing :
      AwaySevenBaseTerminalPrimePowerFiniteScaleGluingPacket family)
    (q : AwaySevenBaseTerminalPrimeIndex r)
    (a : ZMod family.combinedModulus) :
    family.reductionHom q (a ^ 7) = (family.reductionHom q a) ^ 7 :=
  map_pow (family.reductionHom q) a 7

/-- A product-modulus root coordinate weighted by the combined scale reduces
to the local coordinate weighted by the local scale cubed. -/
theorem reduction_weighted_root_coordinate
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {packet : AwaySevenBaseTerminalRoutingPacket (source := source) p}
    {family : AwaySevenBaseTerminalPrimeScaleFamily packet}
    (gluing :
      AwaySevenBaseTerminalPrimePowerFiniteScaleGluingPacket family)
    (q : AwaySevenBaseTerminalPrimeIndex r)
    (a : ZMod family.combinedModulus) :
    family.reductionHom q (a * gluing.combinedScale ^ 3) =
      family.reductionHom q a * family.localScale q ^ 3 := by
  rw [map_mul, map_pow, gluing.reduces_to_localScale q]

/-- A product-modulus endpoint coordinate weighted by the combined scale
reduces to the local coordinate weighted by the local scale to the seventh
power. -/
theorem reduction_weighted_endpoint_coordinate
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {packet : AwaySevenBaseTerminalRoutingPacket (source := source) p}
    {family : AwaySevenBaseTerminalPrimeScaleFamily packet}
    (gluing :
      AwaySevenBaseTerminalPrimePowerFiniteScaleGluingPacket family)
    (q : AwaySevenBaseTerminalPrimeIndex r)
    (a : ZMod family.combinedModulus) :
    family.reductionHom q (a * gluing.combinedScale ^ 7) =
      family.reductionHom q a * family.localScale q ^ 7 := by
  rw [map_mul, map_pow, gluing.reduces_to_localScale q]

/-- The local actual/model weighted-scale identity remains available from one
finite gluing packet without asserting a product-modulus global model. -/
theorem localActual_eq_weightedScale
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {packet : AwaySevenBaseTerminalRoutingPacket (source := source) p}
    {family : AwaySevenBaseTerminalPrimeScaleFamily packet}
    (_gluing :
      AwaySevenBaseTerminalPrimePowerFiniteScaleGluingPacket family)
    (q : AwaySevenBaseTerminalPrimeIndex r) :
    family.localActual q = scalePrimePowerSolution (family.localModel q)
      (family.localScale q) (family.localScale_isUnit q) :=
  family.localActual_eq_weightedScale q

end AwaySevenBaseTerminalPrimePowerFiniteScaleGluingPacket

end DkMath.FLT.Seven
