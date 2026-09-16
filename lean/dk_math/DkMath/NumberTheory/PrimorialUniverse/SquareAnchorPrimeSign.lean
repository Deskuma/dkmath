/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.PrimorialUniverse.SquareAnchorPhase
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

#print "file: DkMath.NumberTheory.PrimorialUniverse.SquareAnchorPrimeSign"

/-!
# Local prime signs of a square phase

This provider-side module extracts the local `+`/`-` content of equality of
square anchors modulo each prime in a finite basis.  It deliberately stops at
the local factorization: it does not synthesize mixed sign choices by CRT or
count phase fibers.
-/

namespace DkMath.NumberTheory.PrimorialUniverse

/-! ## Local sign predicate -/

/-- Two natural anchors have the same signed square root modulo a prime. -/
def SameSquarePrimeSign (p a b : ℕ) : Prop :=
  ((a : ZMod p) = (b : ZMod p)) ∨
    ((a : ZMod p) = -(b : ZMod p))

/-- The local signed-square-root relation is symmetric. -/
theorem sameSquarePrimeSign_symm {p a b : ℕ} :
    SameSquarePrimeSign p a b ↔ SameSquarePrimeSign p b a := by
  constructor
  · intro h
    rcases h with h | h
    · left
      exact h.symm
    · right
      rw [h]
      simp
  · intro h
    rcases h with h | h
    · left
      exact h.symm
    · right
      rw [h]
      simp

/-! ## Prime-local dichotomy -/

/-- Over a prime modulus, equal squares have exactly the two possible signs. -/
theorem square_mod_prime_eq_iff_sameSquarePrimeSign
    {p a b : ℕ}
    (hp : Nat.Prime p) :
    ((a : ZMod p) ^ 2 = (b : ZMod p) ^ 2) ↔
      SameSquarePrimeSign p a b := by
  let : Fact (Nat.Prime p) := ⟨hp⟩
  constructor
  · intro hsq
    have hfactor :
        ((a : ZMod p) - (b : ZMod p)) *
            ((a : ZMod p) + (b : ZMod p)) = 0 := by
      calc
        ((a : ZMod p) - (b : ZMod p)) *
              ((a : ZMod p) + (b : ZMod p)) =
            (a : ZMod p) ^ 2 - (b : ZMod p) ^ 2 := by ring
        _ = 0 := sub_eq_zero.mpr hsq
    rcases mul_eq_zero.mp hfactor with hminus | hplus
    · left
      exact sub_eq_zero.mp hminus
    · right
      exact (add_eq_zero_iff_eq_neg.mp hplus)
  · intro h
    rcases h with h | h
    · rw [h]
    · rw [h]
      simp

/-! ## Descent from a global phase -/

/-- A global square phase supplies a local sign at every basis prime. -/
theorem sameSquareAnchorPhase_implies_primeSign
    {S : Finset ℕ}
    (hS : IsFinitePrimeBasis S)
    {a b p : ℕ}
    (hab : SameSquareAnchorPhase S a b)
    (hpS : p ∈ S) :
    SameSquarePrimeSign p a b := by
  let M := finitePrimeBasisProduct S
  have hpM : p ∣ M := by
    exact mem_dvd_finitePrimeBasisProduct hpS
  have hmodM : a ^ 2 ≡ b ^ 2 [MOD M] := by
    change a ^ 2 % M = b ^ 2 % M
    exact hab
  have hmodp : a ^ 2 ≡ b ^ 2 [MOD p] := by
    have hmodM' := congrArg (fun x => x % p) hmodM
    change a ^ 2 % p = b ^ 2 % p
    simpa only [Nat.mod_mod_of_dvd _ hpM] using hmodM'
  have hsq : (a : ZMod p) ^ 2 = (b : ZMod p) ^ 2 := by
    simpa only [Nat.cast_pow] using
      (ZMod.natCast_eq_natCast_iff (a ^ 2) (b ^ 2) p).mpr hmodp
  exact (square_mod_prime_eq_iff_sameSquarePrimeSign (hS p hpS)).mp hsq

/-! ## Basis-wide profile -/

/-- Every basis prime receives a local sign choice from a global phase. -/
def SameSquarePrimeSignProfile (S : Finset ℕ) (a b : ℕ) : Prop :=
  ∀ p ∈ S, SameSquarePrimeSign p a b

/-- A global square phase implies the full local prime-sign profile. -/
theorem sameSquareAnchorPhase_implies_primeSignProfile
    {S : Finset ℕ}
    (hS : IsFinitePrimeBasis S)
    {a b : ℕ}
    (hab : SameSquareAnchorPhase S a b) :
    SameSquarePrimeSignProfile S a b := by
  intro p hpS
  exact sameSquareAnchorPhase_implies_primeSign hS hab hpS

/-! ## The two canonical phase generators -/

/-- Whole-period translation is the all-plus local sign profile. -/
theorem period_translation_primeSign_plus
    {S : Finset ℕ}
    (_hS : IsFinitePrimeBasis S)
    (n k : ℕ)
    {p : ℕ} (hpS : p ∈ S) :
    ((n : ZMod p) =
      ((n + k * finitePrimeBasisProduct S : ℕ) : ZMod p)) := by
  have hpM : p ∣ finitePrimeBasisProduct S :=
    mem_dvd_finitePrimeBasisProduct hpS
  apply (ZMod.natCast_eq_natCast_iff n
    (n + k * finitePrimeBasisProduct S) p).mpr
  simp [Nat.ModEq, Nat.add_mod, Nat.mul_mod,
    Nat.mod_eq_zero_of_dvd hpM]

/-- Reflection is the all-minus local sign profile. -/
theorem reflection_primeSign_minus
    {S : Finset ℕ}
    (_hS : IsFinitePrimeBasis S)
    {n p : ℕ}
    (hn : n ≤ finitePrimeBasisProduct S)
    (hpS : p ∈ S) :
    (((finitePrimeBasisProduct S - n : ℕ) : ZMod p) =
      -(n : ZMod p)) := by
  have hpM : p ∣ finitePrimeBasisProduct S :=
    mem_dvd_finitePrimeBasisProduct hpS
  have hzero :
      (finitePrimeBasisProduct S : ZMod p) = 0 :=
    (ZMod.natCast_eq_zero_iff (finitePrimeBasisProduct S) p).mpr hpM
  rw [Nat.cast_sub hn, hzero, zero_sub]

/-- Reflection supplies the corresponding local signed-square-root choice. -/
theorem reflection_sameSquarePrimeSign
    {S : Finset ℕ}
    (hS : IsFinitePrimeBasis S)
    {n p : ℕ}
    (hn : n ≤ finitePrimeBasisProduct S)
    (hpS : p ∈ S) :
    SameSquarePrimeSign p n (finitePrimeBasisProduct S - n) := by
  right
  rw [reflection_primeSign_minus hS hn hpS]
  simp

/-! ## Visible `{2, 3}`, `M = 6` regressions -/

private theorem isFinitePrimeBasis_two_three :
    IsFinitePrimeBasis ({2, 3} : Finset ℕ) := by
  intro p hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl <;> norm_num

/-- Translation `1 ↔ 7` is plus at both basis primes of the `6`-wheel. -/
theorem period_translation_primeSign_two_three_regression :
    ((1 : ZMod 2) = (7 : ZMod 2)) ∧
      ((1 : ZMod 3) = (7 : ZMod 3)) := by
  have hS := isFinitePrimeBasis_two_three
  have h2 := period_translation_primeSign_plus hS 1 1 (p := 2) (by simp)
  have h3 := period_translation_primeSign_plus hS 1 1 (p := 3) (by simp)
  simpa [finitePrimeBasisProduct] using And.intro h2 h3

/-- Reflection `1 ↔ 5` is minus at both basis primes of the `6`-wheel. -/
theorem reflection_primeSign_two_three_regression :
    (((5 : ℕ) : ZMod 2) = -((1 : ℕ) : ZMod 2)) ∧
      (((5 : ℕ) : ZMod 3) = -((1 : ℕ) : ZMod 3)) := by
  have hS := isFinitePrimeBasis_two_three
  have hM : finitePrimeBasisProduct ({2, 3} : Finset ℕ) = 6 :=
    finitePrimeBasisProduct_two_three
  have hn : (1 : ℕ) ≤ finitePrimeBasisProduct ({2, 3} : Finset ℕ) := by
    omega
  have h2 := reflection_primeSign_minus hS hn (p := 2) (by simp)
  have h3 := reflection_primeSign_minus hS hn (p := 3) (by simp)
  simpa [hM] using And.intro h2 h3

/-- At `p = 2`, the plus and minus descriptions genuinely overlap. -/
theorem sameSquarePrimeSign_two_overlap_regression :
    ((1 : ZMod 2) = (5 : ZMod 2)) ∧
      ((1 : ZMod 2) = -(5 : ZMod 2)) := by
  decide

end DkMath.NumberTheory.PrimorialUniverse
