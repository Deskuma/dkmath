/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SpecializedPrimeAddress

#print "file: DkMath.FLT.Seven.PrimePowerCellSystems"

namespace DkMath.FLT.Seven

theorem isUnit_zmod_primePower_of_not_dvd {q e a : ℕ} (hq : Nat.Prime q)
    (_he : 0 < e) (ha : ¬ q ∣ a) : IsUnit (a : ZMod (q ^ e)) := by
  rw [ZMod.isUnit_iff_coprime]
  exact (hq.coprime_iff_not_dvd.mpr ha).symm.pow_right e

structure AwayNonSevenPrimeDepthPacket {x y z : ℕ}
    (r : AwayCubicRoutingPacket x y z) : Type where
  depth : AwayRoutingPrimeDepthPacket r
  q_ne_seven : depth.address.q ≠ 7

namespace AwayNonSevenPrimeDepthPacket

def q {x y z : ℕ} {r : AwayCubicRoutingPacket x y z}
    (p : AwayNonSevenPrimeDepthPacket r) : ℕ := p.depth.address.q
def row {x y z : ℕ} {r : AwayCubicRoutingPacket x y z}
    (p : AwayNonSevenPrimeDepthPacket r) : EndpointRoutingRow := p.depth.address.row
def column {x y z : ℕ} {r : AwayCubicRoutingPacket x y z}
    (p : AwayNonSevenPrimeDepthPacket r) : RootRoutingColumn := p.depth.address.column
def exponent {x y z : ℕ} {r : AwayCubicRoutingPacket x y z}
    (p : AwayNonSevenPrimeDepthPacket r) : ℕ := p.depth.exponent
def modulus {x y z : ℕ} {r : AwayCubicRoutingPacket x y z}
    (p : AwayNonSevenPrimeDepthPacket r) : ℕ := p.q ^ p.exponent

theorem q_prime {x y z : ℕ} {r : AwayCubicRoutingPacket x y z}
    (p : AwayNonSevenPrimeDepthPacket r) : Nat.Prime p.q := p.depth.address.q_prime

theorem exponent_pos {x y z : ℕ} {r : AwayCubicRoutingPacket x y z}
    (p : AwayNonSevenPrimeDepthPacket r) : 0 < p.exponent := p.depth.exponent_pos

theorem modulus_pos {x y z : ℕ} {r : AwayCubicRoutingPacket x y z}
    (p : AwayNonSevenPrimeDepthPacket r) : 0 < p.modulus :=
  pow_pos p.q_prime.pos p.exponent

theorem modulus_ne_one {x y z : ℕ} {r : AwayCubicRoutingPacket x y z}
    (p : AwayNonSevenPrimeDepthPacket r) : p.modulus ≠ 1 := by
  exact (one_lt_pow₀ p.q_prime.one_lt p.exponent_pos.ne').ne'

theorem modulus_dvd_cell {x y z : ℕ} {r : AwayCubicRoutingPacket x y z}
    (p : AwayNonSevenPrimeDepthPacket r) :
    p.modulus ∣ routingCell r.routing p.row p.column := by
  simpa [modulus, q, exponent, row, column, p.depth.exponent_eq_cell] using
    (pow_padicValNat_dvd : p.depth.address.q ^ padicValNat p.depth.address.q
      (routingCell r.routing p.depth.address.row p.depth.address.column) ∣ _)

theorem next_power_not_dvd_cell {x y z : ℕ} {r : AwayCubicRoutingPacket x y z}
    (p : AwayNonSevenPrimeDepthPacket r) :
    ¬ p.q ^ (p.exponent + 1) ∣ routingCell r.routing p.row p.column := by
  letI : Fact (Nat.Prime p.q) := ⟨p.q_prime⟩
  have hn : routingCell r.routing p.row p.column ≠ 0 :=
    routingCell_ne_zero p.row p.column
  simpa [q, exponent, row, column, p.depth.exponent_eq_cell, Nat.add_comm] using
    (pow_succ_padicValNat_not_dvd (p := p.q) hn)

theorem modulus_dvd_endpoint {x y z : ℕ} {r : AwayCubicRoutingPacket x y z}
    (p : AwayNonSevenPrimeDepthPacket r) :
    p.modulus ∣ endpointRoutingFactorNat y z p.row :=
  p.modulus_dvd_cell.trans (routingCell_dvd_endpointRoutingFactorNat r p.row p.column)

theorem modulus_dvd_root {x y z : ℕ} {r : AwayCubicRoutingPacket x y z}
    (p : AwayNonSevenPrimeDepthPacket r) :
    p.modulus ∣ rootRoutingFactorNat r p.column :=
  p.modulus_dvd_cell.trans (routingCell_dvd_rootRoutingFactorNat r p.row p.column)

theorem q_dvd_modulus {x y z : ℕ} {r : AwayCubicRoutingPacket x y z}
    (p : AwayNonSevenPrimeDepthPacket r) : p.q ∣ p.modulus := by
  exact dvd_pow_self p.q p.exponent_pos.ne'

theorem q_dvd_endpoint {x y z : ℕ} {r : AwayCubicRoutingPacket x y z}
    (p : AwayNonSevenPrimeDepthPacket r) :
    p.q ∣ endpointRoutingFactorNat y z p.row :=
  p.q_dvd_modulus.trans p.modulus_dvd_endpoint

theorem q_dvd_root {x y z : ℕ} {r : AwayCubicRoutingPacket x y z}
    (p : AwayNonSevenPrimeDepthPacket r) :
    p.q ∣ rootRoutingFactorNat r p.column :=
  p.q_dvd_modulus.trans p.modulus_dvd_root

end AwayNonSevenPrimeDepthPacket

def AwayEndpointPrimePowerNondegenerate (M : ℕ) :
    EndpointRoutingRow → ZMod M → ZMod M → Prop
  | .y, _, z => IsUnit z
  | .z, y, _ => IsUnit y
  | .sum, y, z => IsUnit y ∧ IsUnit z

def AwayEndpointPrimePowerEquation (M : ℕ) :
    EndpointRoutingRow → ZMod M → ZMod M → Prop :=
  AwayEndpointLocalEquation

def AwayRootPrimePowerNondegenerate (M : ℕ) :
    RootRoutingColumn → ZMod M → ZMod M → Prop
  | .sevenV, u, _ => IsUnit u
  | .leftCubic, _, v => IsUnit v
  | .rightCubic, _, v => IsUnit v

def AwayRootPrimePowerEquation (M : ℕ) :
    RootRoutingColumn → ZMod M → ZMod M → Prop := AwayRootLocalEquation

def AwayFirstCoordinatePrimePowerEquation (M : ℕ) :
    EndpointRoutingRow → RootRoutingColumn →
      ZMod M → ZMod M → ZMod M → ZMod M → Prop :=
  AwayFirstCoordinateLocalEquation

structure AwayRoutingPrimePowerSolution (M : ℕ) (row : EndpointRoutingRow)
    (column : RootRoutingColumn) : Type where
  u : ZMod M
  v : ZMod M
  y : ZMod M
  z : ZMod M
  endpoint_nondegenerate : AwayEndpointPrimePowerNondegenerate M row y z
  endpoint_equation : AwayEndpointPrimePowerEquation M row y z
  root_nondegenerate : AwayRootPrimePowerNondegenerate M column u v
  root_equation : AwayRootPrimePowerEquation M column u v
  first_coordinate_equation :
    AwayFirstCoordinatePrimePowerEquation M row column u v y z

end DkMath.FLT.Seven
