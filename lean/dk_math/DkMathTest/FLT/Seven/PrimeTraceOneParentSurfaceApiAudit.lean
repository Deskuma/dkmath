import DkMath.FLT.Seven

open DkMath.CosmicFormulaBinom
open DkMath.FLT.Prime
open DkMath.FLT.Seven

#check PrimeTraceOneStrippedIdealPacket.parent_eq_coord
#check SevenAdicCounterexamplePacket.toPrimeAdicFactorPacket
#check SevenAdicPowerSplit.gap_eq
#check SevenAdicPowerSplit.residual_eq
#check PrimeAdicPowerSplit.gap_eq
#check PrimeAdicPowerSplit.residual_eq
#check SevenQuadraticSeventhPowerPacket.coordinate_eq
#check SevenQuadraticSeventhPowerPacket.residual_eq

example {x y z : ℕ} (s : SevenAdicPowerSplit x y z) :
    z - y = 7 ^ 6 * s.a ^ 7 :=
  s.gap_eq

example {x y z : ℕ} (s : SevenAdicPowerSplit x y z) :
    GN 7 (z - y) y = 7 * s.b ^ 7 :=
  s.residual_eq
