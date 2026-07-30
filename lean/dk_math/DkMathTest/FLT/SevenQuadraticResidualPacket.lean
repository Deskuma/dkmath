import DkMath.FLT.Seven

open DkMath.NumberTheory.TraceOneQuadratic
open DkMath.FLT.Seven

example {x y z : ℕ} (s : SevenAdicPowerSplit x y z) :
    Nonempty (SevenQuadraticResidualPacket x y z) :=
  nonempty_sevenQuadraticResidualPacket_of_powerSplit s

example {x y z : ℕ} (q : SevenQuadraticResidualPacket x y z) :
    ¬ sevenAxis ∣ q.residualCore := q.residual_terminal

example {x y z : ℕ} (q : SevenQuadraticResidualPacket x y z) :
    ∃ b : ℕ, norm q.residualCore = (b : ℤ) ^ 7 :=
  q.norm_is_seventh_power

example {x y z : ℕ} (q : SevenQuadraticResidualPacket x y z) :
    0 < norm q.residualCore := q.norm_positive

#print axioms nonempty_sevenQuadraticResidualPacket_of_powerSplit
#print axioms SevenQuadraticResidualPacket.norm_is_seventh_power
#print axioms SevenQuadraticResidualPacket.norm_positive
