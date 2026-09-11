/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.TraceOneConjugateCoprime

#print "file: DkMathTest.FLT.Prime.TraceOneConjugateCoprimeAxiomAudit"

open DkMath.NumberTheory.TraceOneQuadratic

#print axioms sub_conj_eq_snd_mul_discrAxis
#print axioms discrAxis_mul_sub_tau_mul_sub_conj
#print axioms common_divisor_dvd_discrAxis_of_coordinate_coprime
#print axioms discrAxis_ne_zero_of_packet
#print axioms PrimeDiscriminantPacket.prime_discrAxis
#print axioms PrimeDiscriminantPacket.discrAxis_span_isMaximal
#print axioms discrAxis_mem_span_sup_conj
#print axioms ideal_isCoprime_span_conj_of_coordinate_coprime_of_axis_terminal
#print axioms PrimeDiscriminantPacket.exists_terminal_discrAxis_mul_of_natAbs_norm_eq_prime_mul_pow
