/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.AwaySecondCoordinateLoad

#print "file: DkMath.FLT.Seven.AwayValuationTransfer"

namespace DkMath.FLT.Seven

local instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

private theorem away_endpoint_product_padicValNat {x y z : ℕ}
    (p : AwayCoordinateNormalForm x y z) :
    padicValNat 7 (y * z * (y + z)) =
      1 + padicValNat 7 (Int.natAbs p.root.snd) := by
  rw [away_endpoint_product_load_eq p]
  apply padicValNat_seven_mul_of_core_not_dvd
  · exact Int.natAbs_ne_zero.mpr p.root_snd_ne_zero
  · exact Int.natAbs_ne_zero.mpr p.sndCore_ne_zero
  · exact p.seven_not_dvd_natAbs_sndCore

theorem away_right_padicValNat_transfer {x y z : ℕ}
    (p : AwayCoordinateNormalForm x y z) (_hy : 7 ∣ y)
    (hz : ¬ 7 ∣ z) (hsum : ¬ 7 ∣ y + z) :
    padicValNat 7 y = 1 + padicValNat 7 (Int.natAbs p.root.snd) := by
  calc
    _ = padicValNat 7 (y * z * (y + z)) :=
      (padicValNat_unique_factor_of_triple
        p.counterexample.hy.ne' p.counterexample.hz.ne'
        (Nat.add_pos_left p.counterexample.hy z).ne' hz hsum).symm
    _ = _ := away_endpoint_product_padicValNat p

theorem away_left_padicValNat_transfer {x y z : ℕ}
    (p : AwayCoordinateNormalForm x y z) (_hz : 7 ∣ z)
    (hy : ¬ 7 ∣ y) (hsum : ¬ 7 ∣ y + z) :
    padicValNat 7 z = 1 + padicValNat 7 (Int.natAbs p.root.snd) := by
  calc
    _ = padicValNat 7 (z * y * (y + z)) :=
      (padicValNat_unique_factor_of_triple
        p.counterexample.hz.ne' p.counterexample.hy.ne'
        (Nat.add_pos_left p.counterexample.hy z).ne' hy hsum).symm
    _ = padicValNat 7 (y * z * (y + z)) := by rw [mul_comm z y]
    _ = _ := away_endpoint_product_padicValNat p

theorem away_sum_padicValNat_transfer {x y z : ℕ}
    (p : AwayCoordinateNormalForm x y z) (_hsum : 7 ∣ y + z)
    (hy : ¬ 7 ∣ y) (hz : ¬ 7 ∣ z) :
    padicValNat 7 (y + z) =
      1 + padicValNat 7 (Int.natAbs p.root.snd) := by
  calc
    _ = padicValNat 7 ((y + z) * y * z) :=
      (padicValNat_unique_factor_of_triple
        (Nat.add_pos_left p.counterexample.hy z).ne'
        p.counterexample.hy.ne' p.counterexample.hz.ne' hy hz).symm
    _ = padicValNat 7 (y * z * (y + z)) := by congr 1; ring
    _ = _ := away_endpoint_product_padicValNat p

inductive AwayExceptionalCarrierSource (y z carrier : ℕ) : Prop
  | right (hy : 7 ∣ y) (hz : ¬ 7 ∣ z) (hsum : ¬ 7 ∣ y + z)
      (hcarrier : carrier = y)
  | left (hz : 7 ∣ z) (hy : ¬ 7 ∣ y) (hsum : ¬ 7 ∣ y + z)
      (hcarrier : carrier = z)
  | sum (hsum : 7 ∣ y + z) (hy : ¬ 7 ∣ y) (hz : ¬ 7 ∣ z)
      (hcarrier : carrier = y + z)

structure AwayValuationTransferPacket (x y z : ℕ) : Type where
  normal : AwayCoordinateNormalForm x y z
  carrier : ℕ
  source : AwayExceptionalCarrierSource y z carrier
  carrier_pos : 0 < carrier
  root_snd_abs_pos : 0 < Int.natAbs normal.root.snd
  valuation_eq :
    padicValNat 7 carrier =
      1 + padicValNat 7 (Int.natAbs normal.root.snd)

theorem nonempty_awayValuationTransferPacket {x y z : ℕ}
    (p : AwayCoordinateNormalForm x y z) :
    Nonempty (AwayValuationTransferPacket x y z) := by
  have hvpos : 0 < Int.natAbs p.root.snd :=
    Int.natAbs_pos.mpr p.root_snd_ne_zero
  cases awayExceptionalFactor_of_packet p with
  | right hy hz hsum =>
      exact ⟨{
        normal := p
        carrier := y
        source := .right hy hz hsum rfl
        carrier_pos := p.counterexample.hy
        root_snd_abs_pos := hvpos
        valuation_eq := away_right_padicValNat_transfer p hy hz hsum }⟩
  | left hz hy hsum =>
      exact ⟨{
        normal := p
        carrier := z
        source := .left hz hy hsum rfl
        carrier_pos := p.counterexample.hz
        root_snd_abs_pos := hvpos
        valuation_eq := away_left_padicValNat_transfer p hz hy hsum }⟩
  | sum hsum hy hz =>
      exact ⟨{
        normal := p
        carrier := y + z
        source := .sum hsum hy hz rfl
        carrier_pos := Nat.add_pos_left p.counterexample.hy z
        root_snd_abs_pos := hvpos
        valuation_eq := away_sum_padicValNat_transfer p hsum hy hz }⟩

noncomputable def awayValuationTransferPacket {x y z : ℕ}
    (p : AwayCoordinateNormalForm x y z) : AwayValuationTransferPacket x y z :=
  Classical.choice (nonempty_awayValuationTransferPacket p)

theorem AwayValuationTransferPacket.fortyNine_dvd_carrier_iff {x y z : ℕ}
    (p : AwayValuationTransferPacket x y z) :
    49 ∣ p.carrier ↔ (7 : ℤ) ∣ p.normal.root.snd := by
  have hc0 : p.carrier ≠ 0 := p.carrier_pos.ne'
  have hv0 : Int.natAbs p.normal.root.snd ≠ 0 := p.root_snd_abs_pos.ne'
  constructor
  · intro h49
    have htwo : 2 ≤ padicValNat 7 p.carrier :=
      (@padicValNat_dvd_iff_le 7 inferInstance p.carrier 2 hc0).mp (by simpa using h49)
    have hone : 1 ≤ padicValNat 7 (Int.natAbs p.normal.root.snd) := by
      rw [p.valuation_eq] at htwo
      omega
    have h7abs : 7 ∣ Int.natAbs p.normal.root.snd :=
      (@padicValNat_dvd_iff_le 7 inferInstance _ 1 hv0).mpr hone
    exact Int.natCast_dvd.mpr h7abs
  · intro h7
    have h7abs : 7 ∣ Int.natAbs p.normal.root.snd := Int.natCast_dvd.mp h7
    have hone : 1 ≤ padicValNat 7 (Int.natAbs p.normal.root.snd) :=
      (@padicValNat_dvd_iff_le 7 inferInstance _ 1 hv0).mp h7abs
    apply (@padicValNat_dvd_iff_le 7 inferInstance p.carrier 2 hc0).mpr
    rw [p.valuation_eq]
    omega

theorem AwayValuationTransferPacket.root_snd_depth_lt_carrier {x y z : ℕ}
    (p : AwayValuationTransferPacket x y z) :
    padicValNat 7 (Int.natAbs p.normal.root.snd) <
      padicValNat 7 p.carrier := by
  rw [p.valuation_eq]
  omega

theorem AwayValuationTransferPacket.one_le_carrier_depth {x y z : ℕ}
    (p : AwayValuationTransferPacket x y z) :
    1 ≤ padicValNat 7 p.carrier := by
  rw [p.valuation_eq]
  omega

inductive ValuationCounterexampleRoute (x y z : ℕ) : Type
  | ramified (packet : RamifiedCoordinateNormalForm x y z)
  | away (packet : AwayValuationTransferPacket x y z)

theorem valuationCounterexampleRoute_of_pack {x y z : ℕ}
    (hPack : CounterexamplePack x y z) :
    Nonempty (ValuationCounterexampleRoute x y z) := by
  rcases coordinateCounterexampleRoute_of_pack hPack with ⟨route⟩
  cases route with
  | ramified p => exact ⟨.ramified p⟩
  | away p =>
      rcases nonempty_awayValuationTransferPacket p with ⟨q⟩
      exact ⟨.away q⟩

end DkMath.FLT.Seven
