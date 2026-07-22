import DkMath.FLT.Seven

open DkMath.FLT.Seven

example {x y z : ℕ} (p : AwayCoordinateNormalForm x y z)
    (hy : 7 ∣ y) (hz : ¬ 7 ∣ z) (hsum : ¬ 7 ∣ y + z) :
    padicValNat 7 y = 1 + padicValNat 7 (Int.natAbs p.root.snd) :=
  away_right_padicValNat_transfer p hy hz hsum

example {x y z : ℕ} (p : AwayCoordinateNormalForm x y z)
    (hz : 7 ∣ z) (hy : ¬ 7 ∣ y) (hsum : ¬ 7 ∣ y + z) :
    padicValNat 7 z = 1 + padicValNat 7 (Int.natAbs p.root.snd) :=
  away_left_padicValNat_transfer p hz hy hsum

example {x y z : ℕ} (p : AwayCoordinateNormalForm x y z)
    (hsum : 7 ∣ y + z) (hy : ¬ 7 ∣ y) (hz : ¬ 7 ∣ z) :
    padicValNat 7 (y + z) = 1 + padicValNat 7 (Int.natAbs p.root.snd) :=
  away_sum_padicValNat_transfer p hsum hy hz

example {y z : ℕ} (hy : 7 ∣ y) (hz : ¬ 7 ∣ z) (hs : ¬ 7 ∣ y + z) :
    AwayExceptionalCarrierSource y z y := .right hy hz hs rfl

example {y z : ℕ} (hz : 7 ∣ z) (hy : ¬ 7 ∣ y) (hs : ¬ 7 ∣ y + z) :
    AwayExceptionalCarrierSource y z z := .left hz hy hs rfl

example {y z : ℕ} (hs : 7 ∣ y + z) (hy : ¬ 7 ∣ y) (hz : ¬ 7 ∣ z) :
    AwayExceptionalCarrierSource y z (y + z) := .sum hs hy hz rfl

example {x y z : ℕ} (p : AwayValuationTransferPacket x y z) :
    49 ∣ p.carrier ↔ (7 : ℤ) ∣ p.normal.root.snd :=
  p.fortyNine_dvd_carrier_iff

example {x y z : ℕ} (p : AwayValuationTransferPacket x y z) :
    padicValNat 7 (Int.natAbs p.normal.root.snd) < padicValNat 7 p.carrier :=
  p.root_snd_depth_lt_carrier

example {x y z : ℕ} (p : RamifiedCoordinateNormalForm x y z) :
    ValuationCounterexampleRoute x y z := .ramified p

example {x y z : ℕ} (p : AwayValuationTransferPacket x y z) :
    ValuationCounterexampleRoute x y z := .away p

#print axioms away_right_padicValNat_transfer
#print axioms nonempty_awayValuationTransferPacket
#print axioms AwayValuationTransferPacket.fortyNine_dvd_carrier_iff
#print axioms AwayValuationTransferPacket.root_snd_depth_lt_carrier
#print axioms valuationCounterexampleRoute_of_pack
