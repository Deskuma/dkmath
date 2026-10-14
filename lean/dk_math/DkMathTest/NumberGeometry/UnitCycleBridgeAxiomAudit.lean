/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberGeometry

/-!
# Axiom audit for the NGEO-009 UnitCycle bridge

The audit checks the exact DHNT ratio bridge, prime-chain growth, and the
deterministic strict-invariant no-cycle bridge.
-/

#check DkMath.NumberGeometry.ActiveKernel
#check DkMath.NumberGeometry.Bridge.UnitCycle.massUnit
#check DkMath.NumberGeometry.Bridge.UnitCycle.massUnit_val
#check DkMath.NumberGeometry.Bridge.UnitCycle.dhnt_ratio_massUnit
#check DkMath.NumberGeometry.Bridge.UnitCycle.dhnt_ratio_eq_factor_of_massScalesBy
#check DkMath.NumberGeometry.Bridge.UnitCycle.dhnt_ratio_comp_massUnit
#check DkMath.NumberGeometry.PrimeScaleStep.dhnt_ratio_eq_prime
#check DkMath.NumberGeometry.PrimeScaleStep.massGauge_lt
#check DkMath.NumberGeometry.PrimeScaleChain.closed_prod_eq_one
#check DkMath.NumberGeometry.PrimeScaleChain.massGauge_lt_of_nonempty
#check DkMath.NumberGeometry.PrimeScaleChain.eq_nil_of_closed_active
#check DkMath.UnitCycle.invariant_lt_iterate_of_strict
#check DkMath.UnitCycle.no_nontrivial_cycle_of_strict_invariant
#check DkMath.NumberGeometry.PrimeScaleDynamics
#check DkMath.NumberGeometry.PrimeScaleDynamics.massGauge_strict
#check DkMath.NumberGeometry.PrimeScaleDynamics.no_nontrivial_cycle

#print axioms DkMath.NumberGeometry.Bridge.UnitCycle.dhnt_ratio_massUnit
#print axioms DkMath.NumberGeometry.Bridge.UnitCycle.dhnt_ratio_eq_factor_of_massScalesBy
#print axioms DkMath.NumberGeometry.Bridge.UnitCycle.dhnt_ratio_comp_massUnit
#print axioms DkMath.NumberGeometry.PrimeScaleStep.dhnt_ratio_eq_prime
#print axioms DkMath.NumberGeometry.PrimeScaleStep.massGauge_lt
#print axioms DkMath.NumberGeometry.PrimeScaleChain.closed_prod_eq_one
#print axioms DkMath.NumberGeometry.PrimeScaleChain.massGauge_lt_of_nonempty
#print axioms DkMath.NumberGeometry.PrimeScaleChain.eq_nil_of_closed_active
#print axioms DkMath.UnitCycle.invariant_lt_iterate_of_strict
#print axioms DkMath.UnitCycle.no_nontrivial_cycle_of_strict_invariant
#print axioms DkMath.NumberGeometry.PrimeScaleDynamics.massGauge_strict
#print axioms DkMath.NumberGeometry.PrimeScaleDynamics.no_nontrivial_cycle
