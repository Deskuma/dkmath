import DkMath.FLT.Seven

open DkMath.CosmicFormulaBinom
open DkMath.NumberTheory.TraceOneQuadratic
open DkMath.FLT.Seven

example : sevenAxis = (⟨-1, 2⟩ : TraceOneInt (-2)) := sevenAxis_eq

example : sevenAxis ^ 2 = (-7 : TraceOneInt (-2)) := sevenAxis_sq

example : conj sevenAxis = -sevenAxis := conj_sevenAxis

example : norm sevenAxis = 7 := sevenAxis_norm

example : norm (⟨3, -2⟩ : TraceOneInt (-2)) = 11 := by
  norm_num [DkMath.NumberTheory.TraceOneQuadratic.norm]

example : cyclotomicSeven 1 1 = 7 := by norm_num [cyclotomicSeven]

example : cyclotomicSeven 2 1 = 127 := by norm_num [cyclotomicSeven]

example :
    cyclotomicSevenFst 2 1 = 11 ∧ cyclotomicSevenSnd 2 1 = -6 := by
  norm_num [cyclotomicSevenFst, cyclotomicSevenSnd]

example :
    norm (cyclotomicSevenToTraceOne 2 1) = 127 := by
  rw [← cyclotomicSeven_eq_traceOneNorm_negTwo]
  norm_num [cyclotomicSeven]

example : ((GN 7 (2 - 1) 1 : ℕ) : ℤ) = 127 := by
  rw [GN_seven_sub_eq_traceOneNorm_negTwo 2 1 (by omega)]
  rw [← cyclotomicSeven_eq_traceOneNorm_negTwo]
  norm_num [cyclotomicSeven]

example (z y : ℤ) :
    cyclotomicSeven z y = 0 ↔ z = 0 ∧ y = 0 :=
  cyclotomicSeven_eq_zero_iff z y

example (z y : ℕ) (hz : 0 < z) (hy : 0 < y) :
    7 ≤ z ^ 6 + z ^ 5 * y + z ^ 4 * y ^ 2 + z ^ 3 * y ^ 3
      + z ^ 2 * y ^ 4 + z * y ^ 5 + y ^ 6 :=
  seven_le_cyclotomicSeven_nat z y hz hy

#print axioms traceOne_tau_sq
#print axioms traceOne_norm_mul
#print axioms sevenAxis_sq
#print axioms sevenAxis_norm
#print axioms traceOneNorm_negTwo_eq_zero_iff
#print axioms one_le_traceOneNorm_negTwo_of_ne_zero
#print axioms traceOneNorm_negTwo_eq_one_iff
#print axioms cyclotomicSeven_eq_traceOneNorm_negTwo
#print axioms cyclotomicSeven_eq_zero_iff
