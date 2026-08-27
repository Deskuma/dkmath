/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Nat.Prime.Basic

#print "file: DkMath.NumberTheory.PrimorialUniverse.FiniteReservationEscape"

/-!
# Finite prime-basis reservation escape

This module fixes the finite Euclidean core of the Primorial Unit Universe
branch.  A finite set `S` of ordinary natural primes has product `M`; the
point `M + 1` is divisible by none of the members of `S`, and therefore has a
prime divisor outside `S`.

Here `prime` means `Nat.Prime`.  No relative unit universe, primitive
coordinate, wheel, PowerSwap bridge, Legendre argument, or analytic counting
statement is defined here.  In particular, `M + 1` is an escape point for a
finite reservation sheet, not a claim about the least survivor of a primorial
wheel.
-/

namespace DkMath.NumberTheory.PrimorialUniverse

open scoped BigOperators

/-! ## Finite basis and reservation vocabulary -/

/-- Every member of `S` is an ordinary natural prime. -/
def IsFinitePrimeBasis (S : Finset ℕ) : Prop :=
  ∀ p ∈ S, Nat.Prime p

/-- The product reserved by a finite prime basis. -/
def finitePrimeBasisProduct (S : Finset ℕ) : ℕ :=
  ∏ p ∈ S, p

/-- A natural is reserved by at least one prime scale from `S`. -/
def ReservedByPrimeBasis (S : Finset ℕ) (n : ℕ) : Prop :=
  ∃ p ∈ S, p ∣ n

/-- The product-plus-one escape point attached to `S`. -/
def finitePrimeBasisEscapePoint (S : Finset ℕ) : ℕ :=
  finitePrimeBasisProduct S + 1

/-- Every prime divisor of `n` belongs to the finite basis `S`. -/
def PrimeSupportContainedIn (S : Finset ℕ) (n : ℕ) : Prop :=
  ∀ q : ℕ, Nat.Prime q → q ∣ n → q ∈ S

@[simp] theorem reservedByPrimeBasis_iff (S : Finset ℕ) (n : ℕ) :
    ReservedByPrimeBasis S n ↔ ∃ p, p ∈ S ∧ p ∣ n :=
  Iff.rfl

theorem finitePrimeBasisProduct_ne_zero
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S) :
    finitePrimeBasisProduct S ≠ 0 := by
  classical
  unfold finitePrimeBasisProduct
  exact Finset.prod_ne_zero_iff.mpr (by
    intro p hp
    exact (hS p hp).ne_zero)

theorem mem_dvd_finitePrimeBasisProduct
    {S : Finset ℕ} {p : ℕ} (hp : p ∈ S) :
    p ∣ finitePrimeBasisProduct S := by
  unfold finitePrimeBasisProduct
  exact Finset.dvd_prod_of_mem (fun p : ℕ => p) hp

/-! ## Exact escape from the old reservation sheet -/

/-- A member of the basis cannot divide its product plus one. -/
theorem member_not_dvd_finitePrimeBasisEscapePoint
    {S : Finset ℕ} {p : ℕ}
    (hS : IsFinitePrimeBasis S) (hp : p ∈ S) :
    ¬ p ∣ finitePrimeBasisEscapePoint S := by
  intro hpEscape
  have hpProduct : p ∣ finitePrimeBasisProduct S :=
    mem_dvd_finitePrimeBasisProduct hp
  have hpOne : p ∣ 1 := by
    exact (Nat.dvd_add_iff_right hpProduct).mpr hpEscape
  exact (hS p hp).not_dvd_one hpOne

/-- The Euclidean escape point is not reserved by the finite basis. -/
theorem finitePrimeBasisEscapePoint_not_reserved
    (S : Finset ℕ) (hS : IsFinitePrimeBasis S) :
    ¬ ReservedByPrimeBasis S (finitePrimeBasisEscapePoint S) := by
  intro hReserved
  obtain ⟨p, hp, hpEscape⟩ := hReserved
  exact member_not_dvd_finitePrimeBasisEscapePoint hS hp hpEscape

/-- A finite prime basis has a strictly nontrivial escape point. -/
theorem one_lt_finitePrimeBasisEscapePoint
    (S : Finset ℕ) (hS : IsFinitePrimeBasis S) :
    1 < finitePrimeBasisEscapePoint S := by
  unfold finitePrimeBasisEscapePoint
  have hProduct : 0 < finitePrimeBasisProduct S :=
    Nat.pos_of_ne_zero (finitePrimeBasisProduct_ne_zero hS)
  omega

/-! ## The new prime divisor -/

/-- The escape point has a prime divisor outside the old finite basis.

This is the main PUU-L001 theorem.  Its witness is obtained from the concrete
point `M(S) + 1`, rather than from an infinitude theorem imported from the
background library.
-/
theorem exists_new_prime_divisor_of_finitePrimeBasis
    (S : Finset ℕ) (hS : IsFinitePrimeBasis S) :
    ∃ q : ℕ,
      Nat.Prime q ∧
      q ∣ finitePrimeBasisEscapePoint S ∧
      q ∉ S := by
  have hEscape : 1 < finitePrimeBasisEscapePoint S :=
    one_lt_finitePrimeBasisEscapePoint S hS
  obtain ⟨q, hq, hqEscape⟩ :=
    Nat.exists_prime_and_dvd (by omega : finitePrimeBasisEscapePoint S ≠ 1)
  refine ⟨q, hq, hqEscape, ?_⟩
  intro hqMem
  exact member_not_dvd_finitePrimeBasisEscapePoint hS hqMem hqEscape

/-- A finite prime basis cannot reserve every natural above one. -/
theorem finitePrimeBasis_not_globally_reserving
    (S : Finset ℕ) (hS : IsFinitePrimeBasis S) :
    ∃ n : ℕ, 1 < n ∧ ¬ ReservedByPrimeBasis S n := by
  refine ⟨finitePrimeBasisEscapePoint S,
    one_lt_finitePrimeBasisEscapePoint S hS, ?_⟩
  exact finitePrimeBasisEscapePoint_not_reserved S hS

/-- Every finite prime basis omits some ordinary natural prime. -/
theorem finitePrimeBasis_has_prime_outside
    (S : Finset ℕ) (hS : IsFinitePrimeBasis S) :
    ∃ q : ℕ, Nat.Prime q ∧ q ∉ S := by
  obtain ⟨q, hq, _hqEscape, hqMem⟩ :=
    exists_new_prime_divisor_of_finitePrimeBasis S hS
  exact ⟨q, hq, hqMem⟩

/-! ## Support-containment interface -/

/-- A prime outside `S` persists in a positive multiple as a support witness.

The positivity assumption records the intended multiplicative-scale use of
the interface.  The direct divisibility witness itself is even valid for
`k = 0`.
-/
theorem newPrime_mul_not_primeSupportContainedIn
    {S : Finset ℕ} {q k : ℕ}
    (hq : Nat.Prime q) (hqS : q ∉ S) (_hk : 0 < k) :
    ¬ PrimeSupportContainedIn S (q * k) := by
  intro hSupport
  exact hqS (hSupport q hq (dvd_mul_right q k))

/-- The Euclidean escape point is not supported only by the old basis. -/
theorem finitePrimeBasisEscapePoint_not_primeSupportContainedIn
    (S : Finset ℕ) (hS : IsFinitePrimeBasis S) :
    ¬ PrimeSupportContainedIn S (finitePrimeBasisEscapePoint S) := by
  obtain ⟨q, hq, hqEscape, hqS⟩ :=
    exists_new_prime_divisor_of_finitePrimeBasis S hS
  intro hSupport
  exact hqS (hSupport q hq hqEscape)

/-! ## Small arithmetic regressions -/

theorem finitePrimeBasisProduct_two_three :
    finitePrimeBasisProduct ({2, 3} : Finset ℕ) = 6 := by
  decide

theorem finitePrimeBasisEscapePoint_two_three :
    finitePrimeBasisEscapePoint ({2, 3} : Finset ℕ) = 7 := by
  decide

end DkMath.NumberTheory.PrimorialUniverse
