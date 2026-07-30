import DkMath.FLT.Seven

open DkMath.FLT.Seven

/-- The generic theorem is usable over the non-field ring `ZMod 25`. -/
example : Nonempty (ThreeSevenUnitParametrization
    (1 : ZMod (5 ^ 2)) 1 1) := by
  apply unit_three_seven_parametrization isUnit_one isUnit_one isUnit_one
  norm_num

/-- One quantified test covers the weighted action in every row and column. -/
example {M : ℕ} {row : EndpointRoutingRow} {column : RootRoutingColumn}
    (a : AwayRoutingPrimePowerSolution M row column) (s : ZMod M)
    (hs : IsUnit s) : AwayRoutingPrimePowerSolution M row column :=
  scalePrimePowerSolution a s hs

example {M : ℕ} (a : AwayRoutingPrimePowerSolution M .y .sevenV) :
    Nonempty (PrimePowerOrbitWitness a (canonicalPrimePowerSolution_sevenV M .y)) :=
  sevenV_primePower_orbit_complete a
example {M : ℕ} (a : AwayRoutingPrimePowerSolution M .z .sevenV) :
    Nonempty (PrimePowerOrbitWitness a (canonicalPrimePowerSolution_sevenV M .z)) :=
  sevenV_primePower_orbit_complete a
example {M : ℕ} (a : AwayRoutingPrimePowerSolution M .sum .sevenV) :
    Nonempty (PrimePowerOrbitWitness a (canonicalPrimePowerSolution_sevenV M .sum)) :=
  sevenV_primePower_orbit_complete a

example {q e : ℕ} (hq : Nat.Prime q) (hq7 : q ≠ 7) (he : 0 < e)
    (a : AwayRoutingPrimePowerSolution (q ^ e) .y .leftCubic) :=
  leftCubic_primePower_orbit_complete hq hq7 he a
example {q e : ℕ} (hq : Nat.Prime q) (hq7 : q ≠ 7) (he : 0 < e)
    (a : AwayRoutingPrimePowerSolution (q ^ e) .z .leftCubic) :=
  leftCubic_primePower_orbit_complete hq hq7 he a
example {q e : ℕ} (hq : Nat.Prime q) (hq7 : q ≠ 7) (he : 0 < e)
    (a : AwayRoutingPrimePowerSolution (q ^ e) .sum .leftCubic) :=
  leftCubic_primePower_orbit_complete hq hq7 he a

example {q e : ℕ} (hq : Nat.Prime q) (hq7 : q ≠ 7) (he : 0 < e)
    (a : AwayRoutingPrimePowerSolution (q ^ e) .y .rightCubic) :=
  rightCubic_primePower_orbit_complete hq hq7 he a
example {q e : ℕ} (hq : Nat.Prime q) (hq7 : q ≠ 7) (he : 0 < e)
    (a : AwayRoutingPrimePowerSolution (q ^ e) .z .rightCubic) :=
  rightCubic_primePower_orbit_complete hq hq7 he a
example {q e : ℕ} (hq : Nat.Prime q) (hq7 : q ≠ 7) (he : 0 < e)
    (a : AwayRoutingPrimePowerSolution (q ^ e) .sum .rightCubic) :=
  rightCubic_primePower_orbit_complete hq hq7 he a

#print axioms unit_three_seven_parametrization
#print axioms scalePrimePowerSolution
#print axioms sevenV_primePower_orbit_complete
#print axioms leftCubic_primePower_orbit_complete
#print axioms rightCubic_primePower_orbit_complete
