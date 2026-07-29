/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.PrimePowerOrbitAudit

#print "file: DkMath.FLT.Seven.SevenPivotDepthPacket"

namespace DkMath.FLT.Seven

structure AwaySevenPivotDepthPacket {x y z : ℕ}
    (r : AwayCubicRoutingPacket x y z) : Type where
  row : EndpointRoutingRow
  pivot : ℕ
  pivot_eq : pivot = routingCell r.routing row .sevenV
  seven_dvd_pivot : 7 ∣ pivot
  seven_not_dvd_other : ∀ row' column',
    row' ≠ row ∨ column' ≠ .sevenV →
      ¬ 7 ∣ routingCell r.routing row' column'
  exponent : ℕ
  exponent_eq_pivot : exponent = padicValNat 7 pivot
  exponent_pos : 0 < exponent
  carrier_depth_eq : padicValNat 7 r.cubic.transfer.carrier = exponent
  depth_eq : exponent = 1 + padicValNat 7 r.cubic.rootTriple.vPart
  root_depth_eq : padicValNat 7 r.cubic.rootTriple.vPart = exponent - 1

namespace AwaySevenPivotDepthPacket

def lowerExponent {x y z : ℕ} {r : AwayCubicRoutingPacket x y z}
    (p : AwaySevenPivotDepthPacket r) := p.exponent - 1
def upperModulus {x y z : ℕ} {r : AwayCubicRoutingPacket x y z}
    (p : AwaySevenPivotDepthPacket r) := 7 ^ p.exponent
def lowerModulus {x y z : ℕ} {r : AwayCubicRoutingPacket x y z}
    (p : AwaySevenPivotDepthPacket r) := 7 ^ p.lowerExponent

private theorem seven_dvd_of_padicValNat_pos {n : ℕ}
    (h : 0 < padicValNat 7 n) : 7 ∣ n := by
  exact (dvd_pow_self 7 h.ne').trans pow_padicValNat_dvd

theorem nonempty_awaySevenPivotDepthPacket {x y z : ℕ}
    (r : AwayCubicRoutingPacket x y z) :
    Nonempty (AwaySevenPivotDepthPacket r) := by
  rcases nonempty_awayRoutingPivotDepth r with ⟨d⟩
  have hpos : 0 < padicValNat 7 d.pivot := by rw [d.root_eq]; omega
  have hdvd : 7 ∣ d.pivot := seven_dvd_of_padicValNat_pos hpos
  have mkPacket (row : EndpointRoutingRow)
      (heq : d.pivot = routingCell r.routing row .sevenV)
      (hex : ∀ row' column', row' ≠ row ∨ column' ≠ .sevenV →
        ¬ 7 ∣ routingCell r.routing row' column') :
      AwaySevenPivotDepthPacket r := {
    row := row
    pivot := d.pivot
    pivot_eq := heq
    seven_dvd_pivot := hdvd
    seven_not_dvd_other := hex
    exponent := padicValNat 7 d.pivot
    exponent_eq_pivot := rfl
    exponent_pos := hpos
    carrier_depth_eq := d.carrier_eq.symm
    depth_eq := d.root_eq
    root_depth_eq := by rw [d.root_eq]; omega }
  cases hp : awayRoutingSevenPivot_of_packet r with
  | rowY h11 h12 h13 h21 h22 h23 h31 h32 h33 =>
      have hex : ∀ row' column', row' ≠ .y ∨ column' ≠ .sevenV →
          ¬ 7 ∣ routingCell r.routing row' column' := by
        intro row' column' hne
        cases row' <;> cases column' <;> simp_all [routingCell]
      rcases d.pivot_source with h | h | h
      · exact ⟨mkPacket .y (by simpa [routingCell] using h) hex⟩
      · exact False.elim (h21 (by simpa [h, routingCell] using hdvd))
      · exact False.elim (h31 (by simpa [h, routingCell] using hdvd))
  | rowZ h21 h11 h12 h13 h22 h23 h31 h32 h33 =>
      have hex : ∀ row' column', row' ≠ .z ∨ column' ≠ .sevenV →
          ¬ 7 ∣ routingCell r.routing row' column' := by
        intro row' column' hne
        cases row' <;> cases column' <;> simp_all [routingCell]
      rcases d.pivot_source with h | h | h
      · exact False.elim (h11 (by simpa [h, routingCell] using hdvd))
      · exact ⟨mkPacket .z (by simpa [routingCell] using h) hex⟩
      · exact False.elim (h31 (by simpa [h, routingCell] using hdvd))
  | rowSum h31 h11 h12 h13 h21 h22 h23 h32 h33 =>
      have hex : ∀ row' column', row' ≠ .sum ∨ column' ≠ .sevenV →
          ¬ 7 ∣ routingCell r.routing row' column' := by
        intro row' column' hne
        cases row' <;> cases column' <;> simp_all [routingCell]
      rcases d.pivot_source with h | h | h
      · exact False.elim (h11 (by simpa [h, routingCell] using hdvd))
      · exact False.elim (h21 (by simpa [h, routingCell] using hdvd))
      · exact ⟨mkPacket .sum (by simpa [routingCell] using h) hex⟩

theorem upperModulus_dvd_pivot {x y z : ℕ} {r : AwayCubicRoutingPacket x y z}
    (p : AwaySevenPivotDepthPacket r) : p.upperModulus ∣ p.pivot := by
  simpa [upperModulus, p.exponent_eq_pivot] using
    (pow_padicValNat_dvd : 7 ^ padicValNat 7 p.pivot ∣ p.pivot)

theorem next_upper_power_not_dvd_pivot {x y z : ℕ}
    {r : AwayCubicRoutingPacket x y z} (p : AwaySevenPivotDepthPacket r) :
    ¬ 7 ^ (p.exponent + 1) ∣ p.pivot := by
  letI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  rw [p.pivot_eq]
  simpa [p.exponent_eq_pivot, p.pivot_eq, Nat.add_comm] using
    (pow_succ_padicValNat_not_dvd (p := 7)
      (routingCell_ne_zero (r := r) p.row .sevenV))

theorem upperModulus_dvd_carrier {x y z : ℕ}
    {r : AwayCubicRoutingPacket x y z} (p : AwaySevenPivotDepthPacket r) :
    p.upperModulus ∣ r.cubic.transfer.carrier := by
  simpa [upperModulus, ← p.carrier_depth_eq] using
    (pow_padicValNat_dvd : 7 ^ padicValNat 7 r.cubic.transfer.carrier ∣ _)

theorem lowerModulus_dvd_vPart {x y z : ℕ}
    {r : AwayCubicRoutingPacket x y z} (p : AwaySevenPivotDepthPacket r) :
    p.lowerModulus ∣ r.cubic.rootTriple.vPart := by
  simpa [lowerModulus, lowerExponent, ← p.root_depth_eq] using
    (pow_padicValNat_dvd : 7 ^ padicValNat 7 r.cubic.rootTriple.vPart ∣ _)

theorem upperModulus_not_dvd_vPart {x y z : ℕ}
    {r : AwayCubicRoutingPacket x y z} (p : AwaySevenPivotDepthPacket r) :
    ¬ p.upperModulus ∣ r.cubic.rootTriple.vPart := by
  letI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hn := pow_succ_padicValNat_not_dvd (p := 7)
    r.cubic.rootTriple.vPart_pos.ne'
  simpa [upperModulus, ← p.depth_eq, Nat.add_comm] using hn

theorem upperModulus_dvd_seven_vPart {x y z : ℕ}
    {r : AwayCubicRoutingPacket x y z} (p : AwaySevenPivotDepthPacket r) :
    p.upperModulus ∣ 7 * r.cubic.rootTriple.vPart := by
  rcases p.lowerModulus_dvd_vPart with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  rw [hc]
  have hk : p.exponent = (p.exponent - 1) + 1 :=
    (Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr p.exponent_pos.ne')).symm
  have hpow : 7 ^ p.exponent = 7 * 7 ^ (p.exponent - 1) := by
    conv_lhs => rw [hk]
    rw [pow_succ]
    ring
  change 7 * (7 ^ (p.exponent - 1) * c) = 7 ^ p.exponent * c
  rw [hpow]
  ring

theorem upperModulus_eq_seven_mul_lowerModulus {x y z : ℕ}
    {r : AwayCubicRoutingPacket x y z} (p : AwaySevenPivotDepthPacket r) :
    p.upperModulus = 7 * p.lowerModulus := by
  have hk : p.exponent = (p.exponent - 1) + 1 :=
    (Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr p.exponent_pos.ne')).symm
  change 7 ^ p.exponent = 7 * 7 ^ (p.exponent - 1)
  conv_lhs => rw [hk]
  rw [pow_succ]
  ring

end AwaySevenPivotDepthPacket

end DkMath.FLT.Seven
