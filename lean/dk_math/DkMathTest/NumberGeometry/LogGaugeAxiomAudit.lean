/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberGeometry

/-!
# Axiom audit for the NGEO-010 logarithmic gauge bridge

The audit checks the generic mass-log, ratio-log, prime-step, chain, and
distance-log declarations and prints their transitive axioms.
-/

#check DkMath.NumberGeometry.Bridge.LogGauge.logMassGauge
#check DkMath.NumberGeometry.Bridge.LogGauge.logMassGauge_eq_log_massGauge
#check DkMath.NumberGeometry.Bridge.LogGauge.logMassGauge_eq_add_log_factor
#check DkMath.NumberGeometry.Bridge.LogGauge.logMassGauge_sub_eq_log_factor
#check DkMath.NumberGeometry.Bridge.LogGauge.massGaugeRatio_pos
#check DkMath.NumberGeometry.Bridge.LogGauge.log_massGaugeRatio
#check DkMath.NumberGeometry.Bridge.LogGauge.log_massGaugeRatio_trans
#check DkMath.NumberGeometry.PrimeScaleStep.logMassGauge_sub_eq_log_prime
#check DkMath.NumberGeometry.PrimeScaleChain.logMassGauge_sub_eq_log_prod
#check DkMath.NumberGeometry.PrimeScaleChain.logMassGauge_sub_eq_mul_log_prime
#check DkMath.NumberGeometry.Bridge.LogGauge.logDistanceGauge
#check DkMath.NumberGeometry.Bridge.LogGauge.dist_pos_of_active
#check DkMath.NumberGeometry.Bridge.LogGauge.logMassGauge_eq_two_mul_logDistanceGauge
#check DkMath.NumberGeometry.PrimeScaleStep.logDistanceGauge_sub_eq_half_log_prime

#print axioms DkMath.NumberGeometry.Bridge.LogGauge.logMassGauge_eq_add_log_factor
#print axioms DkMath.NumberGeometry.Bridge.LogGauge.logMassGauge_sub_eq_log_factor
#print axioms DkMath.NumberGeometry.Bridge.LogGauge.log_massGaugeRatio
#print axioms DkMath.NumberGeometry.Bridge.LogGauge.log_massGaugeRatio_trans
#print axioms DkMath.NumberGeometry.PrimeScaleStep.logMassGauge_sub_eq_log_prime
#print axioms DkMath.NumberGeometry.PrimeScaleChain.logMassGauge_sub_eq_log_prod
#print axioms DkMath.NumberGeometry.PrimeScaleChain.logMassGauge_sub_eq_mul_log_prime
#print axioms DkMath.NumberGeometry.Bridge.LogGauge.logMassGauge_eq_two_mul_logDistanceGauge
#print axioms DkMath.NumberGeometry.PrimeScaleStep.logDistanceGauge_sub_eq_half_log_prime
