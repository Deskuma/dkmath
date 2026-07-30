import DkMath.FLT.Seven

open DkMath.NumberTheory.TraceOneQuadratic
open DkMath.FLT.Seven

example (x : TraceOneInt (-2)) :
    sevenAxis ^ 0 ∣ x ↔ (7 : ℤ) ^ 0 ∣ norm x :=
  sevenAxis_pow_dvd_iff_pow_seven_dvd_norm 0 x

example (x : TraceOneInt (-2)) :
    sevenAxis ^ 1 ∣ x ↔ (7 : ℤ) ^ 1 ∣ norm x :=
  sevenAxis_pow_dvd_iff_pow_seven_dvd_norm 1 x

example (x : TraceOneInt (-2)) :
    sevenAxis ∣ x ↔ (7 : ℤ) ∣ norm x := by
  simpa using sevenAxis_pow_dvd_iff_pow_seven_dvd_norm 1 x

example : norm (sevenAxis ^ 2) = 49 := by
  rw [norm_sevenAxis_pow]
  norm_num

example : sevenAxis ^ 2 ∣ sevenAxis ^ 2 := dvd_refl _

example : ¬ sevenAxis ^ 2 ∣ (⟨1, 0⟩ : TraceOneInt (-2)) := by
  apply not_sevenAxis_pow_dvd_of_norm_lt_pow_seven
  · intro h
    have hf := congrArg TraceOneInt.fst h
    norm_num at hf
  · norm_num [DkMath.NumberTheory.TraceOneQuadratic.norm]

example (z y : ℤ) :
    sevenAxis ^ 2 ∣ cyclotomicSevenToTraceOne z y ↔
      (7 : ℤ) ^ 2 ∣ cyclotomicSeven z y :=
  sevenAxis_pow_dvd_cyclotomicSevenToTraceOne_iff 2 z y

#print axioms norm_sevenAxis_pow
#print axioms norm_eq_pow_seven_mul_norm_of_eq_sevenAxis_pow_mul
#print axioms sevenAxis_pow_dvd_iff_pow_seven_dvd_norm
#print axioms ne_zero_of_eq_sevenAxis_pow_mul_of_ne_zero
#print axioms one_le_norm_of_eq_sevenAxis_pow_mul_of_ne_zero
#print axioms pow_seven_le_norm_of_sevenAxis_pow_dvd
#print axioms not_sevenAxis_pow_dvd_of_norm_lt_pow_seven
#print axioms norm_lt_of_eq_sevenAxis_pow_mul_of_ne_zero
#print axioms sevenAxis_pow_dvd_cyclotomicSevenToTraceOne_iff
