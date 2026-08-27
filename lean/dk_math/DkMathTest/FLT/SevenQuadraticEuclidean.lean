import DkMath.FLT.Seven

open DkMath.NumberTheory.TraceOneQuadratic
open DkMath.FLT.Seven

example {x : TraceOneInt (-2)} (h : norm x = 0) : x = 0 :=
  (norm_eq_zero_iff_of_negTwo x).mp h

example {x y z : TraceOneInt (-2)} (hx : x ≠ 0) (h : x * y = x * z) : y = z :=
  mul_left_cancel₀ hx h

example (x y : TraceOneInt (-2)) :
    |(sevenQuotientCoords x y).2 - sevenRoundedSnd x y| ≤ (1 : ℚ) / 2 :=
  sevenRoundedSnd_error_bound x y

example (x y : TraceOneInt (-2)) :
    |((sevenQuotientCoords x y).1 - sevenRoundedFst x y) +
      ((sevenQuotientCoords x y).2 - sevenRoundedSnd x y) / 2| ≤
        (1 : ℚ) / 2 :=
  sevenRoundedFst_skew_error_bound x y

example (x y : TraceOneInt (-2)) :
    y * sevenQuotient x y + sevenRemainder x y = x :=
  seven_quotient_mul_add_remainder x y

example : sevenEuclideanSize
      (sevenRemainder (⟨17, -5⟩ : TraceOneInt (-2)) sevenAxis) <
    sevenEuclideanSize sevenAxis := by
  apply seven_remainder_size_lt
  rw [sevenAxis_eq]
  intro h
  have := congrArg TraceOneInt.fst h
  norm_num at this

example : sevenEuclideanSize
      (sevenRemainder (⟨8, 11⟩ : TraceOneInt (-2)) ⟨2, 1⟩) <
    sevenEuclideanSize (⟨2, 1⟩ : TraceOneInt (-2)) := by
  apply seven_remainder_size_lt
  intro h
  have := congrArg TraceOneInt.fst h
  norm_num at this

example (x y : TraceOneInt (-2)) : gcd x y ∣ x := gcd_dvd_left x y

#print axioms traceOneNegTwo_eq_zero_or_eq_zero_of_mul_eq_zero
#print axioms sevenRatNorm_completed_square
#print axioms sevenRatNorm_le_eleven_sixteen
#print axioms sevenRatNorm_lt_one
#print axioms sevenRoundedSnd_error_bound
#print axioms sevenRoundedFst_skew_error_bound
#print axioms seven_quotient_mul_add_remainder
#print axioms seven_remainder_size_lt
