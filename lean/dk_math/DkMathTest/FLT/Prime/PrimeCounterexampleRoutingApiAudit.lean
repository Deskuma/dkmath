/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.FLT.Five.Basic
import DkMath.FLT.Prime.CounterexampleRouting
import DkMath.FLT.PrimeProvider.TriominoCosmicPrimeGe5Core
import DkMath.FLT.Seven.CounterexampleRouting
import DkMath.FLT.Seven.SevenAdicPowerSplit
import DkMath.FLT.Three.EisensteinConjugateCoprime

#print "file: DkMathTest.FLT.Prime.PrimeCounterexampleRoutingApiAudit"

open DkMath.CosmicFormula
open DkMath.FLT.Prime
open DkMath.FLT.Seven

noncomputable section

#check PrimitivePrimeCounterexample
#check PrimitivePrimeCounterexample.y_lt_z
#check PrimitivePrimeCounterexample.gap_pos
#check PrimitivePrimeCounterexample.coprime_y_z
#check PrimitivePrimeCounterexample.coprime_gap_y
#check PrimitivePrimeCounterexample.gap_mul_GTail_eq
#check PrimeAdicFactorPacket
#check PrimeAdicPowerSplit
#check DkMath.pow_eq_sub_mul_GN_of_add_pow_eq
#check DkMath.CosmicFormula.gcd_GN_prime_eq_one_of_not_dvd
#check DkMath.CosmicFormula.gcd_GN_prime_eq_prime_of_dvd
#check DkMath.Lib.NumberTheory.power_factor_split
#check primeAdicFactorPacket_of_counterexample_of_prime_dvd_gap
#check away_branch_coprime_gap_GTail
#check away_branch_power_factor_split
#check PrimeCounterexampleRoute
#check counterexampleRoute_of_primitive

#check DkMath.FLT.PrimeCounterexamplePack
#check DkMath.FLT.PrimeGe5CounterexamplePack
#check DkMath.FLT.Five.CounterexamplePack
#check DkMath.FLT.Seven.CounterexamplePack
#check DkMath.FLT.Seven.SevenAdicCounterexamplePacket
#check DkMath.FLT.Seven.SevenAdicCounterexamplePacket.toPrimeAdicFactorPacket
#check DkMath.FLT.Three.eisensteinConjugateCoprimePacket_of_primitive_solution

section GenericRoute

variable {p x y z : ℕ}
variable (P : PrimitivePrimeCounterexample p x y z)

example : y < z := P.y_lt_z

example : 0 < z - y := P.gap_pos

example : Nat.Coprime y z := P.coprime_y_z

example : Nat.Coprime (z - y) y := P.coprime_gap_y

example :
    (z - y) * GTail p 1 (z - y) y = x ^ p := P.gap_mul_GTail_eq

example (hgap : p ∣ z - y) :
    PrimeAdicFactorPacket p (z - y) y x :=
  primeAdicFactorPacket_of_counterexample_of_prime_dvd_gap P hgap

example (hgap : ¬ p ∣ z - y) :
    Nat.Coprime (z - y) (GTail p 1 (z - y) y) :=
  away_branch_coprime_gap_GTail P hgap

example (hgap : ¬ p ∣ z - y) :
    (∃ a : ℕ, z - y = a ^ p) ∧
      (∃ b : ℕ, GTail p 1 (z - y) y = b ^ p) :=
  away_branch_power_factor_split P hgap

example : PrimeCounterexampleRoute p x y z :=
  counterexampleRoute_of_primitive P

end GenericRoute

section SevenRegression

variable {x y z : ℕ}

theorem primitive_of_seven
    (P : DkMath.FLT.Seven.CounterexamplePack x y z) :
    PrimitivePrimeCounterexample 7 x y z :=
  { prime := by norm_num
    odd := by norm_num
    x_pos := P.hx
    y_pos := P.hy
    z_pos := P.hz
    coprime_x_y := P.hxy
    equation := by simpa [DkMath.FLT.Seven.Fermat7Equation] using P.hEq }

example (P : DkMath.FLT.Seven.CounterexamplePack x y z)
    (hgap : 7 ∣ z - y) :
    PrimeAdicFactorPacket 7 (z - y) y x :=
  primeAdicFactorPacket_of_counterexample_of_prime_dvd_gap
    (primitive_of_seven P) hgap

example (P : SevenAdicCounterexamplePacket x y z) :
    PrimeAdicFactorPacket 7 (z - y) y x :=
  P.toPrimeAdicFactorPacket

example (P : SevenAdicCounterexamplePacket x y z) :
    PrimeAdicFactorPacket 7 (z - y) y x := by
  exact primeAdicFactorPacket_of_counterexample_of_prime_dvd_gap
    (primitive_of_seven P.counterexample) P.seven_dvd_gap

end SevenRegression

section FiveRegression

variable {x y z : ℕ}

theorem primitive_of_five
    (P : DkMath.FLT.Five.CounterexamplePack x y z) :
    PrimitivePrimeCounterexample 5 x y z :=
  { prime := by norm_num
    odd := by norm_num
    x_pos := P.hx
    y_pos := P.hy
    z_pos := P.hz
    coprime_x_y := P.hxy
    equation := by simpa [DkMath.FLT.Five.Fermat5Equation] using P.hEq }

example (P : DkMath.FLT.Five.CounterexamplePack x y z)
    (hgap : 5 ∣ z - y) :
    PrimeAdicFactorPacket 5 (z - y) y x :=
  primeAdicFactorPacket_of_counterexample_of_prime_dvd_gap
    (primitive_of_five P) hgap

end FiveRegression

section ThreeVocabulary

example {x y z : ℕ}
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hxy : Nat.Coprime x y)
    (hEq : x ^ 3 + y ^ 3 = z ^ 3) :
    PrimitivePrimeCounterexample 3 x y z :=
  { prime := by norm_num
    odd := by norm_num
    x_pos := hx
    y_pos := hy
    z_pos := hz
    coprime_x_y := hxy
    equation := hEq }

end ThreeVocabulary

end
