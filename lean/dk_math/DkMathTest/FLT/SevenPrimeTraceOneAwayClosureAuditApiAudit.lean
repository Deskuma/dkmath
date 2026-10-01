import DkMath.FLT.Seven.PrimeTraceOneAwayClosureAudit

open DkMath.CosmicFormula
open DkMath.CosmicFormulaBinom
open DkMath.FLT.Seven

#check CounterexamplePack.toPrimitivePrimeCounterexample
#check CounterexamplePack.away_branch_power_factor_split_gtail
#check counterexamplePack_away_split_gtail_iff_gn
#check CounterexamplePack.away_branch_power_factor_split_iff_specialized
#check AwayCoordinateNormalForm.away_factor_split_gtail
#check AwayCoordinateNormalForm.counterexample
#check AwayCoordinateNormalForm.seven_not_dvd_gap
#check AwayCoordinateNormalForm.coordinate_eq
#check AwayCoordinateNormalForm.root_norm_not_seven_dvd
#check AwayCoordinateNormalForm.root_coordinates_isCoprime
#check AwayValuationTransferPacket.valuation_eq
#check AwayValuationTransferPacket.root_snd_depth_lt_carrier
#check AwayDescentClosureProvider
#check away_depth_descent_of_closureProvider

example {x y z : ℕ} (hPack : CounterexamplePack x y z) :
    Nat.Prime 7 := by
  exact hPack.toPrimitivePrimeCounterexample.prime

example {y z : ℕ} :
    ((∃ a : ℕ, z - y = a ^ 7) ∧
      (∃ b : ℕ, GTail 7 1 (z - y) y = b ^ 7)) ↔
    ((∃ a : ℕ, z - y = a ^ 7) ∧
      (∃ b : ℕ, DkMath.CosmicFormulaBinom.GN 7 (z - y) y = b ^ 7)) :=
  counterexamplePack_away_split_gtail_iff_gn

example {x y z : ℕ} (p : AwayCoordinateNormalForm x y z) :
    (∃ a : ℕ, z - y = a ^ 7) ∧
      (∃ b : ℕ, GTail 7 1 (z - y) y = b ^ 7) :=
  p.away_factor_split_gtail

example {x y z : ℕ} (p : AwayValuationTransferPacket x y z) :
    padicValNat 7 (Int.natAbs p.normal.root.snd) <
      padicValNat 7 p.carrier :=
  p.root_snd_depth_lt_carrier

example {x y z : ℕ} (p : AwayValuationTransferPacket x y z)
    (c : AwayDescentClosureProvider x y z p) :
    c.nextPack = c.nextRoute.normal.counterexample := by
  rfl
