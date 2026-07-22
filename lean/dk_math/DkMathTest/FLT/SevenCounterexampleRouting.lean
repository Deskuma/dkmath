import DkMath.FLT.Seven

open DkMath.CosmicFormulaBinom
open DkMath.FLT.Seven

example {x y z : ℕ} (hPack : CounterexamplePack x y z) :
    Body7 (z - y) y = x ^ 7 :=
  body7_eq_seventh_power_of_counterexample hPack

example {x y z : ℕ} (hPack : CounterexamplePack x y z)
    (hAway : ¬ 7 ∣ z - y) :
    (∃ u : ℕ, z - y = u ^ 7) ∧
      (∃ v : ℕ, GN 7 (z - y) y = v ^ 7) :=
  branchAway_seventh_power_factor_split hPack hAway

example {x y z : ℕ} (hPack : CounterexamplePack x y z)
    (hRamified : 7 ∣ z - y) : SevenAdicCounterexamplePacket x y z :=
  sevenAdicCounterexamplePacket_of_branch hPack hRamified

example {x y z : ℕ} (packet : SevenAdicCounterexamplePacket x y z) :
    7 ^ 6 ∣ z - y := packet.seven_pow_six_dvd_gap

example {x y z : ℕ} (route : CounterexampleRoute x y z) :
    (¬ 7 ∣ z - y ∧
      (∃ u : ℕ, z - y = u ^ 7) ∧
      (∃ v : ℕ, GN 7 (z - y) y = v ^ 7)) ∨
      SevenAdicCounterexamplePacket x y z := by
  cases route with
  | away hnot gapPow gnPow => exact Or.inl ⟨hnot, gapPow, gnPow⟩
  | ramified packet => exact Or.inr packet

example {x y z : ℕ} (hPack : CounterexamplePack x y z) :
    CounterexampleRoute x y z := counterexampleRoute_of_pack hPack

#print axioms coprime_y_z_of_counterexamplePack
#print axioms coprime_gap_y_of_counterexamplePack
#print axioms body7_eq_seventh_power_of_counterexample
#print axioms GN_seven_pos_of_counterexample
#print axioms gcd_gap_GN_seven_dvd_seven
#print axioms gcd_gap_GN_seven_eq_one_of_not_seven_dvd
#print axioms gcd_gap_GN_seven_eq_seven_of_seven_dvd
#print axioms branchAway_seventh_power_factor_split
#print axioms padicValNat_GN_seven_eq_one_of_counterexample
#print axioms padicValNat_carrier_shape_of_mul_eq_seventh
#print axioms padicValNat_gap_shape_of_counterexample
#print axioms seven_pow_six_dvd_gap_of_counterexample
#print axioms sevenAdicCounterexamplePacket_of_branch
#print axioms counterexampleRoute_of_pack
