import DkMath.FLT.Seven

open DkMath.NumberTheory.TraceOneQuadratic
open DkMath.FLT.Seven

example {z y : ℕ} (hcop : Nat.Coprime z y) (hgap : ¬ 7 ∣ z - y) :
    IsUnit (gcd (cyclotomicSevenToTraceOne (z : ℤ) (y : ℤ))
      (conj (cyclotomicSevenToTraceOne (z : ℤ) (y : ℤ)))) :=
  cyclotomicSeven_gcd_conj_isUnit_of_not_seven_dvd_gap hcop hgap

example {x y z : ℕ} (hPack : CounterexamplePack x y z)
    (hgap : ¬ 7 ∣ z - y) :
    ∃ gamma : TraceOneInt (-2),
      cyclotomicSevenToTraceOne (z : ℤ) (y : ℤ) = gamma ^ 7 :=
  exists_cyclotomicSeven_eq_seventh_power_of_away hPack hgap

example {x y z : ℕ} (q : SevenQuadraticResidualPacket x y z) :
    IsUnit (gcd q.residualCore (conj q.residualCore)) :=
  q.gcd_residual_conj_isUnit

example {x y z : ℕ} (q : SevenQuadraticResidualPacket x y z) :
    ∃ gamma : TraceOneInt (-2), q.residualCore = gamma ^ 7 :=
  q.exists_residualCore_eq_seventh_power

example {x y z : ℕ} (hgap : ¬ 7 ∣ z - y)
    (root : TraceOneInt (-2))
    (heq : cyclotomicSevenToTraceOne (z : ℤ) (y : ℤ) = root ^ 7) :
    QuadraticCounterexampleRoute x y z := .away hgap root heq

example {x y z : ℕ} (packet : SevenQuadraticSeventhPowerPacket x y z) :
    QuadraticCounterexampleRoute x y z := .ramified packet

example {x y z : ℕ} (hPack : CounterexamplePack x y z) :
    Nonempty (QuadraticCounterexampleRoute x y z) :=
  quadraticCounterexampleRoute_of_pack hPack

#print axioms cyclotomicSeven_gcd_conj_isUnit_of_not_seven_dvd_gap
#print axioms exists_cyclotomicSeven_eq_seventh_power_of_away
#print axioms SevenQuadraticResidualPacket.gcd_residual_conj_isUnit
#print axioms SevenQuadraticResidualPacket.exists_residualCore_eq_seventh_power
#print axioms nonempty_sevenQuadraticSeventhPowerPacket_of_residual
#print axioms quadraticCounterexampleRoute_of_pack
