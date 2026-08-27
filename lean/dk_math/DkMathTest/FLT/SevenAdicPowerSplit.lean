import DkMath.FLT.Seven

open DkMath.CosmicFormulaBinom
open DkMath.FLT.Seven

example {x y z : ℕ} (p : SevenAdicCounterexamplePacket x y z) :
    z - y = 7 * ((z - y) / 7) :=
  (Nat.mul_div_cancel' p.seven_dvd_gap).symm

example {x y z : ℕ} (p : SevenAdicCounterexamplePacket x y z) :
    GN 7 (z - y) y = 7 * (GN 7 (z - y) y / 7) := by
  apply (Nat.mul_div_cancel' ?_).symm
  have h := Nat.gcd_dvd_right (z - y) (GN 7 (z - y) y)
  rw [p.gcd_eq_seven] at h
  exact h

example {x y z : ℕ} (p : SevenAdicCounterexamplePacket x y z) :
    x = 7 * (x / 7) :=
  (Nat.mul_div_cancel' p.seven_dvd_x).symm

example {x y z : ℕ} (p : SevenAdicCounterexamplePacket x y z) :
    Nat.Coprime ((z - y) / 7) ((GN 7 (z - y) y) / 7) :=
  sevenAdicPacket_coprime_div_seven p

example {x y z : ℕ} (p : SevenAdicCounterexamplePacket x y z) :
    (7 ^ 2 * ((z - y) / 7)) * (GN 7 (z - y) y / 7) =
      (7 * (x / 7)) ^ 7 :=
  sevenAdicPacket_normalized_product p

example {x y z : ℕ} (p : SevenAdicCounterexamplePacket x y z) :
    Nonempty (SevenAdicPowerSplit x y z) :=
  nonempty_sevenAdicPowerSplit_of_packet p

example {x y z : ℕ} (s : SevenAdicPowerSplit x y z) :
    z - y = 7 ^ 6 * s.a ^ 7 ∧
      GN 7 (z - y) y = 7 * s.b ^ 7 ∧ x = 7 * s.a * s.b :=
  ⟨s.gap_eq, s.residual_eq, s.distinguished_eq⟩

example {x y z : ℕ} (s : SevenAdicPowerSplit x y z) : ¬ 7 ∣ s.b :=
  s.seven_not_dvd_b

#print axioms sevenAdicPacket_residual_not_fortyNine_dvd
#print axioms sevenAdicPacket_seven_not_dvd_strippedResidual
#print axioms sevenAdicPacket_coprime_div_seven
#print axioms sevenAdicPacket_coprime_scaledGap_residual
#print axioms sevenAdicPacket_normalized_product
#print axioms SevenAdicPowerSplit.seven_not_dvd_b
#print axioms nonempty_sevenAdicPowerSplit_of_packet
