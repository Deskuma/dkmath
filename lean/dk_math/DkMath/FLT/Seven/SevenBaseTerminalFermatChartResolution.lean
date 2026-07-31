/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenBaseTerminalExclusion
import DkMath.FLT.Seven.ModSevenSectors

#print "file: DkMath.FLT.Seven.SevenBaseTerminalFermatChartResolution"

namespace DkMath.FLT.Seven

open DkMath.NumberTheory.TraceOneQuadratic

local instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

namespace CounterexamplePack

/-- Exchange the two positive summands of a Fermat-seven counterexample. -/
theorem swapXY {x y z : ℕ} (source : CounterexamplePack x y z) :
    CounterexamplePack y x z where
  hx := source.hy
  hy := source.hx
  hz := source.hz
  hxy := source.hxy.symm
  hEq := by
    simpa [Fermat7Equation, add_comm] using source.hEq

end CounterexamplePack

/-- TERM-009-B: a terminal `Y` row, viewed after exchanging the two
positive summands, belongs to the ramified coordinate chart. -/
theorem AwaySevenBaseTerminalRowYProfile.to_swapped_ramified
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {terminal : AwaySevenBaseTerminalUnitSectorPacket source r p}
    (hy : AwaySevenBaseTerminalRowYProfile terminal) :
    Nonempty (RamifiedCoordinateNormalForm y x z) := by
  have hy7 : 7 ∣ y := by
    rw [hy.2.1]
    exact dvd_mul_right 7 terminal.core.carrier.carrierUnit
  have hy0 : (y : ModSeven) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).2 hy7
  have hlin := fermat7Equation_modSeven_linear source.hEq
  have hxz : (x : ModSeven) = (z : ModSeven) := by
    rw [hy0] at hlin
    simpa using hlin
  have hxle : x ≤ z :=
    (right_lt_of_fermat7Equation source.swapXY.hx source.swapXY.hEq).le
  have hgap : 7 ∣ z - x := by
    apply (Nat.modEq_iff_dvd' hxle).1
    exact (ZMod.natCast_eq_natCast_iff _ _ _).1 hxz
  rcases coordinateCounterexampleRoute_of_pack source.swapXY with ⟨route⟩
  cases route with
  | away packet => exact (packet.seven_not_dvd_gap hgap).elim
  | ramified packet => exact ⟨packet⟩

/-- TERM-009-C: a terminal `Sum` row cannot survive exchanging the two
positive summands.  The exchanged chart is away, but all three of its
endpoint factors are seven-units, contrary to the universal away endpoint
divisibility theorem. -/
theorem AwaySevenBaseTerminalRowSumProfile.false_of_swapped_away
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {terminal : AwaySevenBaseTerminalUnitSectorPacket source r p}
    (hs : AwaySevenBaseTerminalRowSumProfile terminal) : False := by
  have hsum7 : 7 ∣ y + z := by
    rw [hs.2.1]
    exact dvd_mul_right 7 terminal.core.carrier.carrierUnit
  have hsum0 : (y : ModSeven) + (z : ModSeven) = 0 := by
    rw [← Nat.cast_add]
    exact (ZMod.natCast_eq_zero_iff _ _).2 hsum7
  rcases sevenEndpointResidueSector_of_counterexample source with
      ⟨t, ht, hx, hy, hz⟩ |
      ⟨t, ht, hx, hy, hz⟩ |
      ⟨t, ht, hx, hy, hz⟩ |
      ⟨t, ht, hx, hy, hz⟩
  · rw [hy, hz] at hsum0
    have htwo : (2 : ModSeven) ≠ 0 := by decide
    have hprod : (2 : ModSeven) * t = 0 := by
      linear_combination hsum0
    exact ht ((mul_eq_zero.mp hprod).resolve_left htwo)
  · rw [hy, hz] at hsum0
    exact ht (by linear_combination hsum0)
  · rw [hy, hz] at hsum0
    exact ht (by simpa using hsum0)
  · have hx7 : ¬ 7 ∣ x := by
      intro h
      have hx0 : (x : ModSeven) = 0 :=
        (ZMod.natCast_eq_zero_iff _ _).2 h
      rw [hx] at hx0
      have htwo : (-2 : ModSeven) ≠ 0 := by decide
      exact ht ((mul_eq_zero.mp hx0).resolve_left htwo)
    have hz7 : ¬ 7 ∣ z := by
      intro h
      have hz0 : (z : ModSeven) = 0 :=
        (ZMod.natCast_eq_zero_iff _ _).2 h
      rw [hz] at hz0
      exact ht (neg_eq_zero.mp hz0)
    have hxz7 : ¬ 7 ∣ x + z := by
      intro h
      have hxz0 : (x : ModSeven) + (z : ModSeven) = 0 := by
        rw [← Nat.cast_add]
        exact (ZMod.natCast_eq_zero_iff _ _).2 h
      rw [hx, hz] at hxz0
      have hthree : (-3 : ModSeven) ≠ 0 := by decide
      have hprod : (-3 : ModSeven) * t = 0 := by
        linear_combination hxz0
      exact ht ((mul_eq_zero.mp hprod).resolve_left hthree)
    have hxle : x ≤ z :=
      (right_lt_of_fermat7Equation source.swapXY.hx source.swapXY.hEq).le
    have hgap7 : ¬ 7 ∣ z - x := by
      intro hgap
      have hzx : (z : ModSeven) = (x : ModSeven) :=
        (ZMod.natCast_eq_natCast_iff _ _ _).2
          ((Nat.modEq_iff_dvd' hxle).2 hgap).symm
      rw [hz, hx] at hzx
      have ht' : t = 0 := by linear_combination hzx
      exact ht ht'
    rcases coordinateCounterexampleRoute_of_pack source.swapXY with ⟨route⟩
    cases route with
    | ramified packet =>
        exact hgap7
          packet.seventhPower.residual.powerSplit.sevenAdic.seven_dvd_gap
    | away packet =>
        have hprod := seven_dvd_endpoint_product_of_away packet
        rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 7)).mp hprod with
          hxz | hxzsum
        · rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 7)).mp hxz with
            hx' | hz'
          · exact hx7 hx'
          · exact hz7 hz'
        · exact hxz7 hxzsum

/-- A primitive nonzero exponent-seven Fermat chart over the integers.

Unlike `CounterexamplePack`, this façade deliberately permits negative
coordinates.  It records only the algebra needed by an odd-power signed
permutation; no positivity or integer quadratic extraction is claimed. -/
structure SignedFermatSevenChart (a b c : ℤ) : Prop where
  a_ne_zero : a ≠ 0
  b_ne_zero : b ≠ 0
  c_ne_zero : c ≠ 0
  primitive : IsCoprime a b
  equation : a ^ 7 + b ^ 7 = c ^ 7

/-- TERM-009-D: the odd-power signed permutation
`(x,y,z) ↦ (z,-y,x)` of a natural Fermat-seven counterexample. -/
theorem CounterexamplePack.signedOddPermutation
    {x y z : ℕ} (source : CounterexamplePack x y z) :
    SignedFermatSevenChart (z : ℤ) (-(y : ℤ)) (x : ℤ) where
  a_ne_zero := by exact_mod_cast (Nat.ne_of_gt source.hz)
  b_ne_zero := by
    simp only [neg_ne_zero]
    exact_mod_cast (Nat.ne_of_gt source.hy)
  c_ne_zero := by exact_mod_cast (Nat.ne_of_gt source.hx)
  primitive :=
    (coprime_y_z_of_counterexamplePack source).symm.isCoprime.neg_right
  equation := by
    have hEq :
        (x : ℤ) ^ 7 + (y : ℤ) ^ 7 = (z : ℤ) ^ 7 := by
      exact_mod_cast source.hEq
    rw [neg_pow]
    norm_num
    linear_combination -hEq

/-- In a terminal `Z` row the signed odd-power chart has a
seven-divisible gap `x - (-y) = x + y`. -/
theorem AwaySevenBaseTerminalRowZProfile.seven_dvd_signed_gap
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {terminal : AwaySevenBaseTerminalUnitSectorPacket source r p}
    (hz : AwaySevenBaseTerminalRowZProfile terminal) :
    (7 : ℤ) ∣ (x : ℤ) - (-(y : ℤ)) := by
  have hz7 : 7 ∣ z := by
    rw [hz.2.1]
    exact dvd_mul_right 7 terminal.core.carrier.carrierUnit
  have hz0 : (z : ModSeven) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).2 hz7
  have hlin := fermat7Equation_modSeven_linear source.hEq
  rw [hz0] at hlin
  have hxy7 : 7 ∣ x + y := by
    apply (ZMod.natCast_eq_zero_iff _ _).1
    push_cast
    exact hlin
  rcases hxy7 with ⟨k, hk⟩
  refine ⟨(k : ℤ), ?_⟩
  rw [sub_neg_eq_add]
  exact_mod_cast hk

/-- The exact signed analogue of the ramified quadratic coordinate conclusion.
The chart and its ramified gap are retained explicitly; the substantive
arithmetic field is the seventh-power coordinate extraction. -/
structure SignedRamifiedCoordinateNormalForm (a b c : ℤ) : Type where
  chart : SignedFermatSevenChart a b c
  seven_dvd_gap : (7 : ℤ) ∣ c - b
  root : DkMath.NumberTheory.TraceOneQuadratic.TraceOneInt (-2)
  coordinate_eq :
    cyclotomicSevenToTraceOne c b = sevenAxis * root ^ 7

/-- TERM-009-E's sole unresolved arithmetic receiver.  For the signed Row-Z
chart all structural data and seven-divisibility are already proved; what is
missing is exactly the ramified seventh-power extraction in the quadratic
order. -/
def AwaySevenBaseTerminalRowZSignedRamifiedArithmeticObligation
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {terminal : AwaySevenBaseTerminalUnitSectorPacket source r p}
    (_hz : AwaySevenBaseTerminalRowZProfile terminal) : Type :=
  { root : DkMath.NumberTheory.TraceOneQuadratic.TraceOneInt (-2) //
    cyclotomicSevenToTraceOne (x : ℤ) (-(y : ℤ)) =
      sevenAxis * root ^ 7 }

/-- The isolated Row-Z arithmetic receiver is precisely sufficient to build
the signed ramified normal form. -/
def AwaySevenBaseTerminalRowZProfile.to_signed_ramified
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {terminal : AwaySevenBaseTerminalUnitSectorPacket source r p}
    (hz : AwaySevenBaseTerminalRowZProfile terminal)
    (hclose :
      AwaySevenBaseTerminalRowZSignedRamifiedArithmeticObligation hz) :
    SignedRamifiedCoordinateNormalForm
      (z : ℤ) (-(y : ℤ)) (x : ℤ) := by
  rcases hclose with ⟨root, hroot⟩
  exact {
    chart := source.signedOddPermutation
    seven_dvd_gap := hz.seven_dvd_signed_gap
    root := root
    coordinate_eq := hroot }

/-- The fully verified structural data of the only terminal branch not
resolved by natural chart exchange. -/
structure AwaySevenBaseTerminalRowZSignedChartPacket
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    (terminal : AwaySevenBaseTerminalUnitSectorPacket source r p) : Type where
  profile : AwaySevenBaseTerminalRowZProfile terminal
  chart : SignedFermatSevenChart (z : ℤ) (-(y : ℤ)) (x : ℤ)
  seven_dvd_gap : (7 : ℤ) ∣ (x : ℤ) - (-(y : ℤ))

/-- TERM-009 terminal chart resolution.  The `Sum` row is absent because it is
contradictory; the `Y` row reaches the existing natural ramified chart; and
the `Z` row is reduced to one signed arithmetic packet. -/
inductive AwaySevenBaseTerminalChartResolution
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    (terminal : AwaySevenBaseTerminalUnitSectorPacket source r p) : Type
  | rowYRamified (packet : RamifiedCoordinateNormalForm y x z)
  | rowZSigned
      (packet : AwaySevenBaseTerminalRowZSignedChartPacket terminal)

/-- Every terminal away packet has the exact chart resolution described by
TERM-009.  This theorem does not claim that the remaining signed Row-Z
arithmetic obligation, or the natural ramified summit, is closed. -/
theorem AwaySevenBaseTerminalUnitSectorPacket.fermatChartResolution
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    (terminal : AwaySevenBaseTerminalUnitSectorPacket source r p) :
    Nonempty (AwaySevenBaseTerminalChartResolution terminal) := by
  rcases terminal.row_profile_decision with hy | hz | hs
  · rcases hy.to_swapped_ramified with ⟨packet⟩
    exact ⟨.rowYRamified packet⟩
  · exact ⟨.rowZSigned {
      profile := hz
      chart := source.signedOddPermutation
      seven_dvd_gap := hz.seven_dvd_signed_gap }⟩
  · exact hs.false_of_swapped_away.elim

end DkMath.FLT.Seven
