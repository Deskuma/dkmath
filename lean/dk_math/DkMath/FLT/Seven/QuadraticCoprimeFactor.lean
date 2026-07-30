/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.QuadraticUnits

#print "file: DkMath.FLT.Seven.QuadraticCoprimeFactor"

namespace DkMath.FLT.Seven

open DkMath.NumberTheory.TraceOneQuadratic

noncomputable instance traceOneNegTwoGCDMonoid :
    GCDMonoid (TraceOneInt (-2)) :=
  EuclideanDomain.gcdMonoid (TraceOneInt (-2))

theorem associated_seventh_power_of_coprime_mul_eq_pow
    {x y z : TraceOneInt (-2)}
    (hcop : IsUnit (gcd x y)) (hpow : x * y = z ^ 7) :
    ∃ gamma : TraceOneInt (-2), Associated x (gamma ^ 7) := by
  rcases exists_associated_pow_of_mul_eq_pow hcop hpow with ⟨gamma, hgamma⟩
  exact ⟨gamma, hgamma.symm⟩

theorem exists_eq_seventh_power_of_coprime_mul_eq_pow
    {x y z : TraceOneInt (-2)}
    (hcop : IsUnit (gcd x y)) (hpow : x * y = z ^ 7) :
    ∃ gamma : TraceOneInt (-2), x = gamma ^ 7 := by
  rcases exists_associated_pow_of_mul_eq_pow hcop hpow with
    ⟨gamma, u, hu⟩
  rcases exists_seventh_power_eq_of_isUnit u.isUnit with ⟨e, he⟩
  refine ⟨gamma * e, ?_⟩
  calc
    x = gamma ^ 7 * (u : TraceOneInt (-2)) := hu.symm
    _ = gamma ^ 7 * e ^ 7 := by rw [he]
    _ = (gamma * e) ^ 7 := by rw [mul_pow]

theorem seventh_power_factor_split_traceOneNegTwo
    {x y z : TraceOneInt (-2)}
    (hcop : IsUnit (gcd x y)) (hpow : x * y = z ^ 7) :
    (∃ a, x = a ^ 7) ∧ (∃ b, y = b ^ 7) := by
  constructor
  · exact exists_eq_seventh_power_of_coprime_mul_eq_pow hcop hpow
  · apply exists_eq_seventh_power_of_coprime_mul_eq_pow
      (x := y) (y := x) (z := z)
    · exact (gcd_comm' x y).isUnit_iff.mp hcop
    · simpa [mul_comm] using hpow

end DkMath.FLT.Seven
