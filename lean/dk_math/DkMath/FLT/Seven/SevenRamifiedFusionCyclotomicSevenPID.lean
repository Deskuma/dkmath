/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.NumberField.Cyclotomic.Embeddings
import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal

#print "file: DkMath.FLT.Seven.SevenRamifiedFusionCyclotomicSevenPID"

namespace DkMath.FLT.Seven

noncomputable section

set_option linter.style.longLine false

open NumberField InfinitePlace Real
open scoped NumberField

namespace CyclotomicSeven

variable (K : Type*) [Field K] [NumberField K]
  [hK : IsCyclotomicExtension {7} ℚ K]

local instance primeSevenFact : Fact (Nat.Prime 7) :=
  ⟨Nat.prime_seven⟩

/-- The natural floor of the Minkowski class bound of a seventh
cyclotomic field is at most four.

Only an upper bound is needed: every possible rational prime below the
class bound is then either two or three. -/
theorem minkowskiFloor_le_four :
    ⌊(4 / π) ^ nrComplexPlaces K *
        ((Module.finrank ℚ K).factorial /
            (Module.finrank ℚ K : ℝ) ^ Module.finrank ℚ K *
          √|NumberField.discr K|)⌋₊ ≤ 4 := by
  apply Nat.lt_succ_iff.mp
  rw [Nat.floor_lt' (by norm_num : (5 : ℕ) ≠ 0)]
  rw [IsCyclotomicExtension.Rat.nrComplexPlaces_eq_totient_div_two 7,
    IsCyclotomicExtension.finrank (n := 7) K
      (Polynomial.cyclotomic.irreducible_rat (by norm_num)),
    IsCyclotomicExtension.Rat.discr_prime 7 K,
    Nat.totient_prime Nat.prime_seven]
  norm_num
  have hsqrt : Real.sqrt 16807 < 392 / 3 := by
    rw [show (16807 : ℝ) = 49 ^ 2 * 7 by norm_num,
      Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 49 ^ 2),
      Real.sqrt_sq_eq_abs,
      abs_of_pos (by norm_num : (0 : ℝ) < 49)]
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 7)]
  have hpi : (3 : ℝ) < π := pi_gt_three
  calc
    (4 / π) ^ 3 * (5 / 324 * √16807) <
        (4 / 3) ^ 3 * (5 / 324 * (392 / 3)) := by
      gcongr
    _ < 5 := by norm_num

/-- The residue degree of two in the seventh cyclotomic field is three. -/
theorem orderOf_two_zmodSeven :
    orderOf (2 : ZMod 7) = 3 := by
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime (by decide) (by decide)

/-- The residue degree of three in the seventh cyclotomic field is six. -/
theorem orderOf_three_zmodSeven :
    orderOf (3 : ZMod 7) = 6 := by
  apply orderOf_eq_of_pow_and_pow_div_prime
  · norm_num
  · decide
  · intro q hq hqd
    have hq_cases : q = 2 ∨ q = 3 := by
      have hmul : q ∣ 2 * 3 := by
        simpa using hqd
      rcases hq.dvd_mul.mp hmul with htwo | hthree
      · exact Or.inl
          ((Nat.dvd_prime_two_le Nat.prime_two hq.two_le).mp htwo)
      · exact Or.inr
          ((Nat.dvd_prime_two_le Nat.prime_three hq.two_le).mp hthree)
    rcases hq_cases with rfl | rfl <;> decide

/-- The ring of integers of every seventh cyclotomic number field is a
principal ideal ring.

The proof uses the class-group Minkowski theorem. Its bound is below five,
while primes above two and three have norms at least `2^3` and `3^6`.
This theorem concerns an abstract cyclotomic number field; by itself it does
not identify the concrete rank-six carrier used by the FLT7 development with
that ring of integers. -/
theorem ringOfIntegers_isPrincipalIdealRing :
    IsPrincipalIdealRing (𝓞 K) := by
  letI : IsGalois ℚ K :=
    IsCyclotomicExtension.isGalois {7} ℚ K
  apply
    RingOfIntegers.isPrincipalIdealRing_of_isPrincipal_of_lt_or_isPrincipal_of_mem_primesOver_of_mem_Icc
  intro p hp_mem hp
  have hp_le : p ≤ 4 :=
    le_trans (Finset.mem_Icc.mp hp_mem).2
      (minkowskiFloor_le_four K)
  have hp_cases : p = 2 ∨ p = 3 := by
    rcases hp.eq_two_or_odd with htwo | hodd
    · exact Or.inl htwo
    · have hp2 : 2 ≤ p := hp.two_le
      have hp4 : p ≠ 4 := by
        intro heq
        subst p
        norm_num at hodd
      exact Or.inr (by omega)
  rcases hp_cases with rfl | rfl
  · letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    letI :
        (Ideal.span ({(2 : ℤ)} : Set ℤ)).IsPrime :=
      (Ideal.span_singleton_prime (by norm_num)).mpr
        (Nat.prime_iff_prime_int.mp Nat.prime_two)
    obtain ⟨⟨P, hPprime, hPlies⟩⟩ :=
      (Ideal.span ({(2 : ℤ)} : Set ℤ)).nonempty_primesOver
        (S := 𝓞 K)
    letI : P.IsPrime := hPprime
    letI : P.LiesOver (Ideal.span ({(2 : ℤ)} : Set ℤ)) := hPlies
    refine ⟨P, ⟨hPprime, hPlies⟩, Or.inl ?_⟩
    have hdeg :
        P.inertiaDeg ℤ =
          orderOf (2 : ZMod 7) :=
      IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd
        2 K P (by norm_num)
    change
      _ <
        2 ^
          P.inertiaDeg ℤ
    rw [hdeg, orderOf_two_zmodSeven]
    exact lt_of_le_of_lt (minkowskiFloor_le_four K) (by norm_num)
  · letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    letI :
        (Ideal.span ({(3 : ℤ)} : Set ℤ)).IsPrime :=
      (Ideal.span_singleton_prime (by norm_num)).mpr
        (Nat.prime_iff_prime_int.mp Nat.prime_three)
    obtain ⟨⟨P, hPprime, hPlies⟩⟩ :=
      (Ideal.span ({(3 : ℤ)} : Set ℤ)).nonempty_primesOver
        (S := 𝓞 K)
    letI : P.IsPrime := hPprime
    letI : P.LiesOver (Ideal.span ({(3 : ℤ)} : Set ℤ)) := hPlies
    refine ⟨P, ⟨hPprime, hPlies⟩, Or.inl ?_⟩
    have hdeg :
        P.inertiaDeg ℤ =
          orderOf (3 : ZMod 7) :=
      IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd
        3 K P (by norm_num)
    change
      _ <
        3 ^
          P.inertiaDeg ℤ
    rw [hdeg, orderOf_three_zmodSeven]
    exact lt_of_le_of_lt (minkowskiFloor_le_four K) (by norm_num)

/-- Class-number formulation of the cyclotomic-seven PID theorem. -/
theorem classNumber_eq_one :
    NumberField.classNumber K = 1 :=
  NumberField.classNumber_eq_one_iff.mpr
    (ringOfIntegers_isPrincipalIdealRing K)

#print axioms minkowskiFloor_le_four
#print axioms orderOf_two_zmodSeven
#print axioms orderOf_three_zmodSeven
#print axioms ringOfIntegers_isPrincipalIdealRing
#print axioms classNumber_eq_one

end CyclotomicSeven

end

end DkMath.FLT.Seven
