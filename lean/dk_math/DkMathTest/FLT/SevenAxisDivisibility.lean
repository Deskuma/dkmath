import DkMath.FLT.Seven

open DkMath.CosmicFormulaBinom
open DkMath.NumberTheory.TraceOneQuadratic
open DkMath.FLT.Seven

example :
    sevenAxis * (⟨2, 3⟩ : TraceOneInt (-2)) = ⟨-14, 7⟩ := by
  apply traceOne_ext <;> norm_num

example : sevenAxis ∣ (⟨3, 1⟩ : TraceOneInt (-2)) := by
  rw [sevenAxis_dvd_iff_seven_dvd_trace]
  norm_num [trace]

example : ¬ sevenAxis ∣ (⟨1, 0⟩ : TraceOneInt (-2)) := by
  rw [sevenAxis_dvd_iff_seven_dvd_trace]
  norm_num [trace]

example : (7 : ℤ) ∣ norm (⟨3, 1⟩ : TraceOneInt (-2)) := by
  rw [seven_dvd_norm_iff_seven_dvd_trace]
  norm_num [trace]

example :
    norm (sevenAxis * (⟨2, 3⟩ : TraceOneInt (-2))) =
      7 * norm (⟨2, 3⟩ : TraceOneInt (-2)) :=
  norm_eq_seven_mul_norm_of_eq_sevenAxis_mul rfl

example : sevenAxis ∣ cyclotomicSevenToTraceOne 8 1 := by
  rw [sevenAxis_dvd_cyclotomicSevenToTraceOne_iff]
  norm_num

example : ¬ sevenAxis ∣ cyclotomicSevenToTraceOne 2 1 := by
  rw [sevenAxis_dvd_cyclotomicSevenToTraceOne_iff]
  norm_num

example : (7 : ℤ) ∣ cyclotomicSeven 8 1 := by
  rw [seven_dvd_cyclotomicSeven_iff]
  norm_num

example : ¬ (7 : ℤ) ∣ cyclotomicSeven 2 1 := by
  rw [seven_dvd_cyclotomicSeven_iff]
  norm_num

example : 7 ∣ GN 7 (8 - 1) 1 := by
  rw [seven_dvd_GN_seven_sub_iff 8 1 (by omega)]

example : ¬ 7 ∣ GN 7 (2 - 1) 1 := by
  rw [seven_dvd_GN_seven_sub_iff 2 1 (by omega)]
  norm_num

#print axioms sevenAxis_dvd_iff_seven_dvd_trace
#print axioms seven_dvd_norm_iff_seven_dvd_trace
#print axioms sevenAxis_dvd_iff_seven_dvd_norm
#print axioms norm_eq_seven_mul_norm_of_eq_sevenAxis_mul
#print axioms one_le_norm_of_eq_sevenAxis_mul_of_ne_zero
#print axioms norm_lt_of_eq_sevenAxis_mul_of_ne_zero
#print axioms trace_cyclotomicSevenToTraceOne
#print axioms sevenAxis_dvd_cyclotomicSevenToTraceOne_iff
#print axioms seven_dvd_cyclotomicSeven_iff
#print axioms seven_dvd_GN_seven_sub_iff
