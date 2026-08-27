import DkMath.FLT.Seven

open DkMath.NumberTheory.TraceOneQuadratic
open DkMath.FLT.Seven

example : IsUnit (1 : TraceOneInt (-2)) := by simp

example : IsUnit (-1 : TraceOneInt (-2)) := by simp

example : ¬ IsUnit sevenAxis := by
  rw [isUnit_iff_norm_eq_one, sevenAxis_norm]
  norm_num

example : ∃ e : TraceOneInt (-2), (1 : TraceOneInt (-2)) = e ^ 7 :=
  exists_seventh_power_eq_of_isUnit (by simp)

example : ∃ e : TraceOneInt (-2), (-1 : TraceOneInt (-2)) = e ^ 7 :=
  exists_seventh_power_eq_of_isUnit (by simp)

example {x y z : TraceOneInt (-2)}
    (hcop : IsUnit (gcd x y)) (hpow : x * y = z ^ 7) :
    (∃ a, x = a ^ 7) ∧ (∃ b, y = b ^ 7) :=
  seventh_power_factor_split_traceOneNegTwo hcop hpow

#print axioms isUnit_iff_norm_eq_one
#print axioms isUnit_iff_eq_one_or_neg_one
#print axioms exists_seventh_power_eq_of_isUnit
#print axioms associated_seventh_power_of_coprime_mul_eq_pow
#print axioms exists_eq_seventh_power_of_coprime_mul_eq_pow
#print axioms seventh_power_factor_split_traceOneNegTwo
