/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Gauge

#print "file: DkMathTest.NumberTheory.Gauge.Exponent"

namespace DkMathTest.NumberTheory.Gauge

open DkMath.NumberTheory.Gauge

#check exponentGaugeHeight
#check PrimeExponentGauge
#check PrimePowerExponentGauge
#check primeExponentGauge_of_prime
#check primeExponentGauge_uniformPrimeDialHeight
#check primeExponentGauge_height_eq_one
#check exponentGaugeHeight_eq_zero_of_row_lt
#check primePowerExponentGauge_of_prime_of_pos
#check exponentGaugeHeight_prime_pow_add_index
#check exponentGaugeHeight_prime_pow_of_not_dvd

example : PrimeExponentGauge 3 := by
  exact primeExponentGauge_of_prime (by norm_num)

example : exponentGaugeHeight 3 3 1 = 1 := by
  exact primeExponentGauge_height_eq_one (by norm_num) (by norm_num) (by norm_num)

example : exponentGaugeHeight 5 3 1 = 0 := by
  exact exponentGaugeHeight_eq_zero_of_row_lt (by norm_num) (by norm_num)

example : PrimePowerExponentGauge 3 2 := by
  exact primePowerExponentGauge_of_prime_of_pos (by norm_num) (by norm_num)

example : exponentGaugeHeight 3 (3 ^ 2) 2 + padicValNat 3 2 = 2 := by
  exact exponentGaugeHeight_prime_pow_add_index
    (by norm_num) (by norm_num) (by norm_num)

example : exponentGaugeHeight 3 (3 ^ 2) 2 = 2 := by
  exact exponentGaugeHeight_prime_pow_of_not_dvd
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end DkMathTest.NumberTheory.Gauge
