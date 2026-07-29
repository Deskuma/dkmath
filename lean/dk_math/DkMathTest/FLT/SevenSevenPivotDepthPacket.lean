import DkMath.FLT.Seven.SevenPivotPrimePowerSystem
import DkMathTest.FLT.SevenSpecializedPrimeAddress

open DkMath.FLT.Seven

example : 2 ∣ routingCell genericAddressCounterexample .y .sevenV := by
  norm_num [routingCell, genericAddressCounterexample]

example {x y z : ℕ} {r : AwayCubicRoutingPacket x y z}
    (p : AwaySevenPivotDepthPacket r) :
    p.exponent = 1 + padicValNat 7 r.cubic.rootTriple.vPart := p.depth_eq

example {x y z : ℕ} {r : AwayCubicRoutingPacket x y z}
    (p : AwaySevenPivotDepthPacket r) :
    p.upperModulus = 7 * p.lowerModulus :=
  p.upperModulus_eq_seven_mul_lowerModulus

example (u v : ℤ) :
    seventhPowerFst u v = u^7 + 4*v^7 -
      14*v^2*(u+v)*sevenRamifiedResidualPolynomial u v :=
  seventhPowerFst_eq_sevenRamifiedCore_add_residual u v

example {x y z : ℕ} {r : AwayCubicRoutingPacket x y z}
    (p : AwaySevenPivotDepthPacket r) :
    AwaySevenPivotPrimePowerSolution p.exponent p.row :=
  p.toPrimePowerSolution

#check AwayRoutingSevenPivot.rowY
#check AwayRoutingSevenPivot.rowZ
#check AwayRoutingSevenPivot.rowSum

#print axioms AwaySevenPivotDepthPacket.nonempty_awaySevenPivotDepthPacket
#print axioms AwaySevenPivotDepthPacket.toPrimePowerSolution
