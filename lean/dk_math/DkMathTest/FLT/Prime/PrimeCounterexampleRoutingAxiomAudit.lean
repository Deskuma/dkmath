/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.FLT.Prime.CounterexampleRouting

#print "file: DkMathTest.FLT.Prime.PrimeCounterexampleRoutingAxiomAudit"

open DkMath.FLT.Prime

#print axioms PrimitivePrimeCounterexample.y_lt_z
#print axioms PrimitivePrimeCounterexample.gap_pos
#print axioms PrimitivePrimeCounterexample.coprime_y_z
#print axioms PrimitivePrimeCounterexample.coprime_gap_y
#print axioms PrimitivePrimeCounterexample.gap_mul_GTail_eq
#print axioms primeAdicFactorPacket_of_counterexample_of_prime_dvd_gap
#print axioms away_branch_coprime_gap_GTail
#print axioms away_branch_power_factor_split
#print axioms counterexampleRoute_of_primitive
