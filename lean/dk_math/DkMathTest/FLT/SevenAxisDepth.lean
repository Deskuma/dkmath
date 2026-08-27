import DkMath.FLT.Seven

open DkMath.NumberTheory.TraceOneQuadratic
open DkMath.FLT.Seven

example : sevenAxisDepth (0 : TraceOneInt (-2)) = 0 := by simp

example : sevenAxisDepth (⟨1, 0⟩ : TraceOneInt (-2)) = 0 := by
  norm_num [sevenAxisDepth, DkMath.NumberTheory.TraceOneQuadratic.norm]

example : sevenAxisDepth sevenAxis = 1 := by
  simpa using sevenAxisDepth_sevenAxis_pow 1

example : sevenAxisDepth (sevenAxis ^ 2) = 2 :=
  sevenAxisDepth_sevenAxis_pow 2

example {x : TraceOneInt (-2)} (hx : x ≠ 0) : sevenAxis ^ 0 ∣ x := by
  rw [sevenAxis_pow_dvd_iff_le_sevenAxisDepth hx]
  omega

example {x : TraceOneInt (-2)} (hx : x ≠ 0) :
    sevenAxis ^ sevenAxisDepth x ∣ x :=
  sevenAxis_pow_depth_dvd hx

example {x : TraceOneInt (-2)} (hx : x ≠ 0) :
    ¬ sevenAxis ^ (sevenAxisDepth x + 1) ∣ x :=
  not_sevenAxis_pow_succ_depth_dvd hx

example :
    ∃ y : TraceOneInt (-2),
      sevenAxis = sevenAxis ^ sevenAxisDepth sevenAxis * y ∧
      y ≠ 0 ∧
      ¬ sevenAxis ∣ y ∧
      ¬ (7 : ℤ) ∣ norm y ∧
      norm sevenAxis = (7 : ℤ) ^ sevenAxisDepth sevenAxis * norm y ∧
      1 ≤ norm y := by
  apply exists_terminal_sevenAxis_core
  intro h
  have hf := congrArg TraceOneInt.fst h
  norm_num at hf

#print axioms sevenAxisDepth_zero
#print axioms norm_pos_of_ne_zero
#print axioms pow_seven_dvd_norm_iff_pow_seven_dvd_natAbs_norm
#print axioms sevenAxis_pow_dvd_iff_le_sevenAxisDepth
#print axioms sevenAxis_pow_depth_dvd
#print axioms not_sevenAxis_pow_succ_depth_dvd
#print axioms le_sevenAxisDepth_of_pow_dvd
#print axioms sevenAxis_pow_dvd_of_le_depth
#print axioms pow_seven_depth_le_norm
#print axioms exists_terminal_sevenAxis_core
#print axioms sevenAxisDepth_sevenAxis_pow
#print axioms sevenAxisDepth_cyclotomicSevenToTraceOne
