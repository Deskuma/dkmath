/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.PrimorialUniverse.SquareAnchorPhasePeriodTransport
import DkMath.NumberTheory.PrimorialUniverse.SquareAnchorPhaseFiberProjection
import Mathlib.Tactic

#print "file: DkMath.NumberTheory.PrimorialUniverse.SquareAnchorPhaseMixedRadixTransport"

/-!
# Square-anchor fresh-prime mixed-radix transport

PUU-L029 identifies the old-period quotient digit with the actual raw lift
index over the canonical enlarged representative.  For an old product `M`
and a fresh prime `q`, the digit is `(n / M) % q`; the enlarged canonical
representative is the corresponding old lift, and the dynamic plus sheet is
that same digit in `ZMod q`.  This is finite static/dynamic compatibility only:
it does not assert escape, primality of a lift, or a Legendre conclusion.
-/

namespace DkMath.NumberTheory.PrimorialUniverse

/-- The fresh-prime mixed-radix digit of the old-period block quotient. -/
def squareAnchorFreshPrimeBlockDigit
    (S : Finset ℕ) (q n : ℕ) : ℕ :=
  squareAnchorPhaseBlockQuotient S n % q

/-- The mixed-radix digit is in the canonical range below the fresh prime. -/
theorem squareAnchorFreshPrimeBlockDigit_lt
    {S : Finset ℕ} {q : ℕ} (hq : Nat.Prime q) (n : ℕ) :
    squareAnchorFreshPrimeBlockDigit S q n < q := by
  exact Nat.mod_lt _ hq.pos

/-- The old block quotient splits into its fresh-prime digit and the quotient
of the enlarged basis. -/
theorem squareAnchorPhaseBlockQuotient_eq_digit_add_enlargedQuotient
    {S : Finset ℕ} (_hS : IsFinitePrimeBasis S)
    {q : ℕ} (_hq : Nat.Prime q) (hqS : q ∉ S) (n : ℕ) :
    squareAnchorPhaseBlockQuotient S n =
      squareAnchorFreshPrimeBlockDigit S q n +
        q * squareAnchorPhaseBlockQuotient (insert q S) n := by
  have hquot :
      squareAnchorPhaseBlockQuotient S n / q =
        squareAnchorPhaseBlockQuotient (insert q S) n := by
    unfold squareAnchorPhaseBlockQuotient
    rw [finitePrimeBasisProduct_insert hqS]
    rw [Nat.div_div_eq_div_mul, Nat.mul_comm]
  have hsplit := (Nat.mod_add_div'
    (squareAnchorPhaseBlockQuotient S n) q).symm
  rw [hquot] at hsplit
  simpa [squareAnchorFreshPrimeBlockDigit, Nat.mul_comm] using hsplit

/-- The anchor has its full old/fresh mixed-radix decomposition. -/
theorem squareAnchorPhase_mixedRadix_decomposition
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S)
    {q : ℕ} (hq : Nat.Prime q) (hqS : q ∉ S) (n : ℕ) :
    n = squareAnchorPhaseRepresentative S n +
        squareAnchorFreshPrimeBlockDigit S q n *
          finitePrimeBasisProduct S +
        squareAnchorPhaseBlockQuotient (insert q S) n *
          (q * finitePrimeBasisProduct S) := by
  have hold := squareAnchorPhaseRepresentative_add_blockQuotient hS n
  have hquot := squareAnchorPhaseBlockQuotient_eq_digit_add_enlargedQuotient
    hS hq hqS n
  calc
    n = squareAnchorPhaseRepresentative S n +
        squareAnchorPhaseBlockQuotient S n * finitePrimeBasisProduct S := hold
    _ = squareAnchorPhaseRepresentative S n +
        (squareAnchorFreshPrimeBlockDigit S q n +
          q * squareAnchorPhaseBlockQuotient (insert q S) n) *
            finitePrimeBasisProduct S := by rw [hquot]
    _ = squareAnchorPhaseRepresentative S n +
        squareAnchorFreshPrimeBlockDigit S q n * finitePrimeBasisProduct S +
        squareAnchorPhaseBlockQuotient (insert q S) n *
          (q * finitePrimeBasisProduct S) := by ring

/-- The canonical enlarged representative is the old canonical representative
lifted at its fresh-prime mixed-radix digit. -/
theorem squareAnchorPhaseRepresentative_insert_eq_old_lift_digit
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S)
    {q : ℕ} (hq : Nat.Prime q) (hqS : q ∉ S) (n : ℕ) :
    squareAnchorPhaseRepresentative (insert q S) n =
      primeBasisWheelLift S (squareAnchorPhaseRepresentative S n)
        (squareAnchorFreshPrimeBlockDigit S q n) := by
  have hmix := squareAnchorPhase_mixedRadix_decomposition hS hq hqS n
  have hMpos : 0 < finitePrimeBasisProduct S :=
    Nat.pos_of_ne_zero (finitePrimeBasisProduct_ne_zero hS)
  have hrlt : squareAnchorPhaseRepresentative S n <
      finitePrimeBasisProduct S := by
    exact Nat.mod_lt _ hMpos
  have hdlt := squareAnchorFreshPrimeBlockDigit_lt (S := S) hq n
  have hlt : squareAnchorPhaseRepresentative S n +
      squareAnchorFreshPrimeBlockDigit S q n * finitePrimeBasisProduct S <
        q * finitePrimeBasisProduct S := by
    calc
      squareAnchorPhaseRepresentative S n +
          squareAnchorFreshPrimeBlockDigit S q n * finitePrimeBasisProduct S <
        finitePrimeBasisProduct S +
          squareAnchorFreshPrimeBlockDigit S q n * finitePrimeBasisProduct S :=
            Nat.add_lt_add_right hrlt _
      _ = (squareAnchorFreshPrimeBlockDigit S q n + 1) *
          finitePrimeBasisProduct S := by ring
      _ ≤ q * finitePrimeBasisProduct S :=
        Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hdlt)
  change n % finitePrimeBasisProduct (insert q S) =
    primeBasisWheelLift S (squareAnchorPhaseRepresentative S n)
      (squareAnchorFreshPrimeBlockDigit S q n)
  rw [finitePrimeBasisProduct_insert hqS]
  calc
    n % (q * finitePrimeBasisProduct S) =
        (squareAnchorPhaseRepresentative S n +
          squareAnchorFreshPrimeBlockDigit S q n * finitePrimeBasisProduct S +
          squareAnchorPhaseBlockQuotient (insert q S) n *
            (q * finitePrimeBasisProduct S)) %
          (q * finitePrimeBasisProduct S) := by
            exact congrArg (fun x : ℕ => x % (q * finitePrimeBasisProduct S)) hmix
    _ = (squareAnchorPhaseRepresentative S n +
          squareAnchorFreshPrimeBlockDigit S q n * finitePrimeBasisProduct S) %
          (q * finitePrimeBasisProduct S) := by
      exact Nat.add_mul_mod_self_right _ _ _
    _ = squareAnchorPhaseRepresentative S n +
          squareAnchorFreshPrimeBlockDigit S q n * finitePrimeBasisProduct S :=
      Nat.mod_eq_of_lt hlt
    _ = primeBasisWheelLift S (squareAnchorPhaseRepresentative S n)
          (squareAnchorFreshPrimeBlockDigit S q n) := by
      rfl

/-- The enlarged canonical representative still projects to the old canonical
representative. -/
theorem squareAnchorPhaseRepresentative_insert_projects_old
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S)
    {q : ℕ} (hq : Nat.Prime q) (hqS : q ∉ S) (n : ℕ) :
    primeBasisWheelProjection S (squareAnchorPhaseRepresentative (insert q S) n) =
      squareAnchorPhaseRepresentative S n := by
  rw [squareAnchorPhaseRepresentative_insert_eq_old_lift_digit hS hq hqS]
  exact primeBasisWheelProjection_lift (Nat.mod_lt _
    (Nat.pos_of_ne_zero (finitePrimeBasisProduct_ne_zero hS)))

/-- The dynamic plus sheet is the fresh-prime mixed-radix digit in `ZMod q`. -/
theorem squareAnchorFreshPrimePlus_eq_blockDigit
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S)
    {q : ℕ} (hq : Nat.Prime q) (hqS : q ∉ S) (n : ℕ) :
    squareAnchorFreshPrimePlus S q n =
      (squareAnchorFreshPrimeBlockDigit S q n : ZMod q) := by
  rw [squareAnchorFreshPrimePlus_eq_blockQuotient hS hq hqS]
  exact (ZMod.natCast_mod _ _).symm

/-- The mixed-radix digit is an actual `+n` raw fresh-prime lift index over the
canonical old representative, without a coprimality assumption on `n`. -/
theorem squareAnchorFreshPrimeBlockDigit_is_plusLiftIndex
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S)
    {q : ℕ} (hq : Nat.Prime q) (hqS : q ∉ S) (n : ℕ) :
    IsFreshPrimePlusLiftIndex S q n (squareAnchorPhaseRepresentative S n)
      (squareAnchorFreshPrimeBlockDigit S q n) := by
  have hmix := squareAnchorPhase_mixedRadix_decomposition hS hq hqS n
  have hdlt := squareAnchorFreshPrimeBlockDigit_lt (S := S) hq n
  refine ⟨hdlt, ?_⟩
  have hcast := congrArg (fun x : ℕ => (x : ZMod q)) hmix
  have hqzero : (q : ZMod q) = 0 :=
    (ZMod.natCast_eq_zero_iff q q).mpr (dvd_refl q)
  simpa [primeBasisWheelLift, Nat.cast_add, Nat.cast_mul, hqzero] using hcast.symm

/-- The canonical enlarged representative belongs to the static enlarged
phase-projection fiber over the canonical old representative. -/
theorem squareAnchorPhaseRepresentative_insert_mem_projectionFiber
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S)
    {q : ℕ} (hq : Nat.Prime q) (hqS : q ∉ S) (n : ℕ) :
    squareAnchorPhaseRepresentative (insert q S) n ∈
      squareAnchorPhaseProjectionFiber S q n
        (squareAnchorPhaseRepresentative S n) := by
  rw [mem_squareAnchorPhaseProjectionFiber]
  constructor
  · apply mem_squareAnchorPhaseFiber.mpr
    constructor
    · change n % finitePrimeBasisProduct (insert q S) <
        finitePrimeBasisProduct (insert q S)
      exact Nat.mod_lt _ (by
        rw [finitePrimeBasisProduct_insert hqS]
        exact Nat.mul_pos hq.pos
          (Nat.pos_of_ne_zero (finitePrimeBasisProduct_ne_zero hS)))
    · change n ^ 2 % finitePrimeBasisProduct (insert q S) =
        (n % finitePrimeBasisProduct (insert q S)) ^ 2 %
          finitePrimeBasisProduct (insert q S)
      exact Nat.pow_mod n 2 (finitePrimeBasisProduct (insert q S))
  · exact squareAnchorPhaseRepresentative_insert_projects_old hS hq hqS n

/-- One old-period turn advances the fresh-prime digit by one modulo `q`. -/
theorem squareAnchorFreshPrimeBlockDigit_add_period
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S)
    {q : ℕ} (_hq : Nat.Prime q) (n : ℕ) :
    squareAnchorFreshPrimeBlockDigit S q
        (n + finitePrimeBasisProduct S) =
      (squareAnchorFreshPrimeBlockDigit S q n + 1) % q := by
  unfold squareAnchorFreshPrimeBlockDigit
  rw [squareAnchorPhaseBlockQuotient_add_period hS]
  simp [Nat.add_mod]

/-- `k` old-period turns advance the fresh-prime digit by `k` modulo `q`. -/
theorem squareAnchorFreshPrimeBlockDigit_add_mul_period
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S)
    {q : ℕ} (_hq : Nat.Prime q) (n k : ℕ) :
    squareAnchorFreshPrimeBlockDigit S q
        (n + k * finitePrimeBasisProduct S) =
      (squareAnchorFreshPrimeBlockDigit S q n + k) % q := by
  unfold squareAnchorFreshPrimeBlockDigit
  rw [squareAnchorPhaseBlockQuotient_add_mul_period hS]
  simp [Nat.add_mod]

/-- After one enlarged fresh-prime period, the mixed-radix digit returns. -/
theorem squareAnchorFreshPrimeBlockDigit_add_enlarged_period
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S)
    {q : ℕ} (hq : Nat.Prime q) (hqS : q ∉ S) (n : ℕ) :
    squareAnchorFreshPrimeBlockDigit S q
        (n + finitePrimeBasisProduct (insert q S)) =
      squareAnchorFreshPrimeBlockDigit S q n := by
  rw [finitePrimeBasisProduct_insert hqS]
  have hdigit := squareAnchorFreshPrimeBlockDigit_lt (S := S) hq n
  simpa [Nat.add_mod, Nat.mod_self, Nat.mod_eq_of_lt hdigit] using
    squareAnchorFreshPrimeBlockDigit_add_mul_period hS hq n q

/-- The `{2,3}` old representative `4` traverses all five fresh-prime raw
lift digits and closes at the enlarged period `30`. -/
theorem squareAnchorFreshPrimeMixedRadix_two_three_six_to_thirty_regression :
    squareAnchorFreshPrimeBlockDigit ({2, 3} : Finset ℕ) 5 4 = 0 ∧
      squareAnchorFreshPrimeBlockDigit ({2, 3} : Finset ℕ) 5 10 = 1 ∧
      squareAnchorFreshPrimeBlockDigit ({2, 3} : Finset ℕ) 5 16 = 2 ∧
      squareAnchorFreshPrimeBlockDigit ({2, 3} : Finset ℕ) 5 22 = 3 ∧
      squareAnchorFreshPrimeBlockDigit ({2, 3} : Finset ℕ) 5 28 = 4 ∧
      squareAnchorFreshPrimeBlockDigit ({2, 3} : Finset ℕ) 5 34 = 0 ∧
      squareAnchorPhaseRepresentative (insert 5 ({2, 3} : Finset ℕ)) 4 = 4 ∧
      squareAnchorPhaseRepresentative (insert 5 ({2, 3} : Finset ℕ)) 10 = 10 ∧
      squareAnchorPhaseRepresentative (insert 5 ({2, 3} : Finset ℕ)) 16 = 16 ∧
      squareAnchorPhaseRepresentative (insert 5 ({2, 3} : Finset ℕ)) 22 = 22 ∧
      squareAnchorPhaseRepresentative (insert 5 ({2, 3} : Finset ℕ)) 28 = 28 ∧
      squareAnchorPhaseRepresentative (insert 5 ({2, 3} : Finset ℕ)) 34 = 4 := by
  have hS : IsFinitePrimeBasis ({2, 3} : Finset ℕ) := by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl <;> norm_num
  have hq : Nat.Prime 5 := by norm_num
  have hqS : 5 ∉ ({2, 3} : Finset ℕ) := by simp
  have hdigit := squareAnchorFreshPrimeBlockDigit_add_mul_period
    hS hq 4
  have hrep4 := squareAnchorPhaseRepresentative_insert_eq_old_lift_digit
    hS hq hqS 4
  have hrep10 := squareAnchorPhaseRepresentative_insert_eq_old_lift_digit
    hS hq hqS 10
  have hrep16 := squareAnchorPhaseRepresentative_insert_eq_old_lift_digit
    hS hq hqS 16
  have hrep22 := squareAnchorPhaseRepresentative_insert_eq_old_lift_digit
    hS hq hqS 22
  have hrep28 := squareAnchorPhaseRepresentative_insert_eq_old_lift_digit
    hS hq hqS 28
  have hrep34 := squareAnchorPhaseRepresentative_insert_eq_old_lift_digit
    hS hq hqS 34
  norm_num [squareAnchorFreshPrimeBlockDigit, squareAnchorPhaseBlockQuotient,
    finitePrimeBasisProduct] at hdigit
  have hrep4' : squareAnchorPhaseRepresentative (insert 5 ({2, 3} : Finset ℕ)) 4 = 4 := by
    calc
      squareAnchorPhaseRepresentative (insert 5 ({2, 3} : Finset ℕ)) 4 =
          primeBasisWheelLift ({2, 3} : Finset ℕ)
            (squareAnchorPhaseRepresentative ({2, 3} : Finset ℕ) 4)
              (squareAnchorFreshPrimeBlockDigit ({2, 3} : Finset ℕ) 5 4) := hrep4
      _ = 4 := by norm_num [squareAnchorPhaseRepresentative,
        primeBasisWheelProjection, primeBasisWheelLift,
        squareAnchorFreshPrimeBlockDigit, squareAnchorPhaseBlockQuotient,
        finitePrimeBasisProduct]
  have hrep10' : squareAnchorPhaseRepresentative (insert 5 ({2, 3} : Finset ℕ)) 10 = 10 := by
    calc
      squareAnchorPhaseRepresentative (insert 5 ({2, 3} : Finset ℕ)) 10 =
          primeBasisWheelLift ({2, 3} : Finset ℕ)
            (squareAnchorPhaseRepresentative ({2, 3} : Finset ℕ) 10)
              (squareAnchorFreshPrimeBlockDigit ({2, 3} : Finset ℕ) 5 10) := hrep10
      _ = 10 := by norm_num [squareAnchorPhaseRepresentative,
        primeBasisWheelProjection, primeBasisWheelLift,
        squareAnchorFreshPrimeBlockDigit, squareAnchorPhaseBlockQuotient,
        finitePrimeBasisProduct]
  have hrep16' : squareAnchorPhaseRepresentative (insert 5 ({2, 3} : Finset ℕ)) 16 = 16 := by
    calc
      squareAnchorPhaseRepresentative (insert 5 ({2, 3} : Finset ℕ)) 16 =
          primeBasisWheelLift ({2, 3} : Finset ℕ)
            (squareAnchorPhaseRepresentative ({2, 3} : Finset ℕ) 16)
              (squareAnchorFreshPrimeBlockDigit ({2, 3} : Finset ℕ) 5 16) := hrep16
      _ = 16 := by norm_num [squareAnchorPhaseRepresentative,
        primeBasisWheelProjection, primeBasisWheelLift,
        squareAnchorFreshPrimeBlockDigit, squareAnchorPhaseBlockQuotient,
        finitePrimeBasisProduct]
  have hrep22' : squareAnchorPhaseRepresentative (insert 5 ({2, 3} : Finset ℕ)) 22 = 22 := by
    calc
      squareAnchorPhaseRepresentative (insert 5 ({2, 3} : Finset ℕ)) 22 =
          primeBasisWheelLift ({2, 3} : Finset ℕ)
            (squareAnchorPhaseRepresentative ({2, 3} : Finset ℕ) 22)
              (squareAnchorFreshPrimeBlockDigit ({2, 3} : Finset ℕ) 5 22) := hrep22
      _ = 22 := by norm_num [squareAnchorPhaseRepresentative,
        primeBasisWheelProjection, primeBasisWheelLift,
        squareAnchorFreshPrimeBlockDigit, squareAnchorPhaseBlockQuotient,
        finitePrimeBasisProduct]
  have hrep28' : squareAnchorPhaseRepresentative (insert 5 ({2, 3} : Finset ℕ)) 28 = 28 := by
    calc
      squareAnchorPhaseRepresentative (insert 5 ({2, 3} : Finset ℕ)) 28 =
          primeBasisWheelLift ({2, 3} : Finset ℕ)
            (squareAnchorPhaseRepresentative ({2, 3} : Finset ℕ) 28)
              (squareAnchorFreshPrimeBlockDigit ({2, 3} : Finset ℕ) 5 28) := hrep28
      _ = 28 := by norm_num [squareAnchorPhaseRepresentative,
        primeBasisWheelProjection, primeBasisWheelLift,
        squareAnchorFreshPrimeBlockDigit, squareAnchorPhaseBlockQuotient,
        finitePrimeBasisProduct]
  have hrep34' : squareAnchorPhaseRepresentative (insert 5 ({2, 3} : Finset ℕ)) 34 = 4 := by
    calc
      squareAnchorPhaseRepresentative (insert 5 ({2, 3} : Finset ℕ)) 34 =
          primeBasisWheelLift ({2, 3} : Finset ℕ)
            (squareAnchorPhaseRepresentative ({2, 3} : Finset ℕ) 34)
              (squareAnchorFreshPrimeBlockDigit ({2, 3} : Finset ℕ) 5 34) := hrep34
      _ = 4 := by norm_num [squareAnchorPhaseRepresentative,
        primeBasisWheelProjection, primeBasisWheelLift,
        squareAnchorFreshPrimeBlockDigit, squareAnchorPhaseBlockQuotient,
        finitePrimeBasisProduct]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num [squareAnchorFreshPrimeBlockDigit,
      squareAnchorPhaseBlockQuotient, finitePrimeBasisProduct]
  · norm_num [squareAnchorFreshPrimeBlockDigit,
      squareAnchorPhaseBlockQuotient, finitePrimeBasisProduct]
  · norm_num [squareAnchorFreshPrimeBlockDigit,
      squareAnchorPhaseBlockQuotient, finitePrimeBasisProduct]
  · norm_num [squareAnchorFreshPrimeBlockDigit,
      squareAnchorPhaseBlockQuotient, finitePrimeBasisProduct]
  · norm_num [squareAnchorFreshPrimeBlockDigit,
      squareAnchorPhaseBlockQuotient, finitePrimeBasisProduct]
  · norm_num [squareAnchorFreshPrimeBlockDigit,
      squareAnchorPhaseBlockQuotient, finitePrimeBasisProduct]
  · exact hrep4'
  · exact hrep10'
  · exact hrep16'
  · exact hrep22'
  · exact hrep28'
  · exact hrep34'

end DkMath.NumberTheory.PrimorialUniverse
