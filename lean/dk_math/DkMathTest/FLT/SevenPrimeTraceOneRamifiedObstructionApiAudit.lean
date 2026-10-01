import DkMath.FLT.Seven.PrimeTraceOneRamifiedObstruction

open DkMath.NumberTheory.TraceOneQuadratic
open DkMath.FLT.Seven

#check SevenQuadraticSeventhPowerPacket.root_norm_eq
#check SevenQuadraticSeventhPowerPacket.root_norm_not_seven_dvd
#check SevenQuadraticSeventhPowerPacket.root_linear_mod_seven_ne_zero
#check SevenQuadraticSeventhPowerPacket.ramified_coordinates_mod_seven_ne_zero
#check SevenQuadraticSeventhPowerPacket.seven_pow_five_dvd_root_snd

example {x y z : ℕ} (p : SevenQuadraticSeventhPowerPacket x y z) :
    norm p.root = (p.residual.powerSplit.b : ℤ) :=
  p.root_norm_eq

example {x y z : ℕ} (p : SevenQuadraticSeventhPowerPacket x y z) :
    ¬ (7 : ℤ) ∣ norm p.root :=
  p.root_norm_not_seven_dvd

example {x y z : ℕ} (p : SevenQuadraticSeventhPowerPacket x y z) :
    (7 : ℤ) ^ 5 ∣ p.root.snd :=
  p.seven_pow_five_dvd_root_snd

/- This is only a reduced root-side consistency witness; it is not a
counterexample packet. -/
example :
    ¬ (7 : ℤ) ∣ norm (⟨1, (7 : ℤ) ^ 5⟩ : TraceOneInt (-2)) ∧
      (7 : ℤ) ^ 5 ∣ (⟨1, (7 : ℤ) ^ 5⟩ : TraceOneInt (-2)).snd ∧
      ¬ (7 : ℤ) ∣ seventhPowerSndCore 1 ((7 : ℤ) ^ 5) := by
  norm_num [DkMath.NumberTheory.TraceOneQuadratic.norm,
    seventhPowerSndCore]
