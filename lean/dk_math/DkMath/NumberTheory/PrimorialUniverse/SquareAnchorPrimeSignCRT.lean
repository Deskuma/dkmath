/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.PrimorialUniverse.SquareAnchorPrimeSign
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

#print "file: DkMath.NumberTheory.PrimorialUniverse.SquareAnchorPrimeSignCRT"

/-!
# Mixed prime-sign CRT synthesis

This provider-side module closes the local-to-global square-phase factorization
and realizes arbitrary chosen local signs by the finite Chinese remainder
theorem.  The result is existential only: it does not claim sign uniqueness,
phase-fiber cardinality, escape existence, or any Legendre consumer theorem.
-/

namespace DkMath.NumberTheory.PrimorialUniverse

/-! ## Local-to-global factorization -/

/-- A local prime-sign profile implies equality of square phases modulo the basis product. -/
theorem primeSignProfile_implies_sameSquareAnchorPhase
    {S : Finset ℕ}
    (hS : IsFinitePrimeBasis S)
    {a b : ℕ}
    (hprofile : SameSquarePrimeSignProfile S a b) :
    SameSquareAnchorPhase S a b := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      change a ^ 2 % finitePrimeBasisProduct ∅ =
        b ^ 2 % finitePrimeBasisProduct ∅
      simp [finitePrimeBasisProduct, Nat.mod_one]
  | @insert p S hpS ih =>
      have hp : Nat.Prime p := hS p (Finset.mem_insert_self p S)
      have hS' : IsFinitePrimeBasis S := by
        intro q hq
        exact hS q (Finset.mem_insert_of_mem hq)
      have hprofile' : SameSquarePrimeSignProfile S a b := by
        intro q hq
        exact hprofile q (Finset.mem_insert_of_mem hq)
      have hphaseS : SameSquareAnchorPhase S a b := ih hS' hprofile'
      have hmodS : a ^ 2 ≡ b ^ 2 [MOD finitePrimeBasisProduct S] := by
        change a ^ 2 % finitePrimeBasisProduct S =
          b ^ 2 % finitePrimeBasisProduct S
        exact hphaseS
      have hsign : SameSquarePrimeSign p a b :=
        hprofile p (Finset.mem_insert_self p S)
      have hsq : (a : ZMod p) ^ 2 = (b : ZMod p) ^ 2 :=
        (square_mod_prime_eq_iff_sameSquarePrimeSign hp).mpr hsign
      have hmodP : a ^ 2 ≡ b ^ 2 [MOD p] := by
        exact (ZMod.natCast_eq_natCast_iff (a ^ 2) (b ^ 2) p).mp
          (by simpa only [Nat.cast_pow] using hsq)
      have hcop : Nat.Coprime p (finitePrimeBasisProduct S) := by
        unfold finitePrimeBasisProduct
        rw [Nat.coprime_prod_right_iff]
        intro q hq
        apply (Nat.coprime_primes hp (hS q (Finset.mem_insert_of_mem hq))).mpr
        intro hpq
        apply hpS
        simpa [hpq] using hq
      have hmod : a ^ 2 ≡ b ^ 2 [MOD
          p * finitePrimeBasisProduct S] :=
        (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨hmodP, hmodS⟩
      change a ^ 2 % finitePrimeBasisProduct (insert p S) =
        b ^ 2 % finitePrimeBasisProduct (insert p S)
      change a ^ 2 % (p * finitePrimeBasisProduct S) =
        b ^ 2 % (p * finitePrimeBasisProduct S) at hmod
      simpa [finitePrimeBasisProduct, hpS] using hmod

/-! ## Exact factorization theorem -/

/-- Square phase is equivalent to the basis-wide local prime-sign profile. -/
theorem sameSquareAnchorPhase_iff_primeSignProfile
    {S : Finset ℕ}
    (hS : IsFinitePrimeBasis S)
    {a b : ℕ} :
    SameSquareAnchorPhase S a b ↔
      SameSquarePrimeSignProfile S a b := by
  constructor
  · exact sameSquareAnchorPhase_implies_primeSignProfile hS
  · exact primeSignProfile_implies_sameSquareAnchorPhase hS

/-! ## Chosen sign assignments -/

/-- A Boolean assignment chooses `+a` when true and `-a` when false modulo each basis prime. -/
def RealizesPrimeSignChoice
    (S : Finset ℕ) (sigma : ℕ → Bool) (a b : ℕ) : Prop :=
  ∀ p ∈ S,
    if sigma p = true then
      ((b : ZMod p) = (a : ZMod p))
    else
      ((b : ZMod p) = -(a : ZMod p))

/-- A chosen sign assignment supplies the corresponding unsigned sign profile. -/
theorem realizesPrimeSignChoice_implies_primeSignProfile
    {S : Finset ℕ}
    (_hS : IsFinitePrimeBasis S)
    {sigma : ℕ → Bool} {a b : ℕ}
    (hchoice : RealizesPrimeSignChoice S sigma a b) :
    SameSquarePrimeSignProfile S a b := by
  intro p hpS
  by_cases hσ : sigma p = true
  · left
    have hplus := hchoice p hpS
    have hplus' : (b : ZMod p) = (a : ZMod p) := by
      simpa [hσ] using hplus
    exact hplus'.symm
  · right
    have hneg : (b : ZMod p) = -(a : ZMod p) := by
      simpa [hσ] using hchoice p hpS
    rw [hneg]
    simp

/-! ## CRT construction -/

private theorem prime_coprime_finitePrimeBasisProduct_of_not_mem
    {S : Finset ℕ}
    (hS : IsFinitePrimeBasis S)
    {p : ℕ} (hp : Nat.Prime p) (hpS : p ∉ S) :
    Nat.Coprime p (finitePrimeBasisProduct S) := by
  unfold finitePrimeBasisProduct
  rw [Nat.coprime_prod_right_iff]
  intro q hq
  apply (Nat.coprime_primes hp (hS q hq)).mpr
  intro hpq
  apply hpS
  simpa [hpq] using hq

private theorem neg_residue_in_zmod
    {p a : ℕ} (hp : Nat.Prime p) :
    ((p - a % p : ℕ) : ZMod p) = -(a : ZMod p) := by
  have hle : a % p ≤ p := le_of_lt (Nat.mod_lt a hp.pos)
  rw [Nat.cast_sub hle]
  have hzero : (p : ZMod p) = 0 := by
    exact (ZMod.natCast_eq_zero_iff p p).mpr dvd_rfl
  rw [hzero, zero_sub]
  simp

/-!
The following induction is the semantic CRT API.  Its conjunction shape
handles the empty basis as well: the product is `1` and the representative is
`0`, with the sign condition vacuous.
-/

/-- Every Boolean local sign assignment has a representative below the basis period. -/
theorem exists_anchor_lt_period_realizing_primeSignChoice
    {S : Finset ℕ}
    (hS : IsFinitePrimeBasis S)
    (sigma : ℕ → Bool)
    (a : ℕ) :
    ∃ b : ℕ,
      b < finitePrimeBasisProduct S ∧
      RealizesPrimeSignChoice S sigma a b := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      refine ⟨0, ?_, ?_⟩
      · simp [finitePrimeBasisProduct]
      · intro p hp
        simp at hp
  | @insert p S hpS ih =>
      have hp : Nat.Prime p := hS p (Finset.mem_insert_self p S)
      have hS' : IsFinitePrimeBasis S := by
        intro q hq
        exact hS q (Finset.mem_insert_of_mem hq)
      obtain ⟨bS, hbS, hchoiceS⟩ := ih hS'
      have hcop : Nat.Coprime p (finitePrimeBasisProduct S) :=
        prime_coprime_finitePrimeBasisProduct_of_not_mem hS' hp hpS
      let c : ℕ := if sigma p = true then a else p - a % p
      let b : ℕ := Nat.chineseRemainder hcop c bS
      have hbBound : b < finitePrimeBasisProduct (insert p S) := by
        have hbound := Nat.chineseRemainder_lt_mul hcop c bS
          hp.ne_zero (finitePrimeBasisProduct_ne_zero hS')
        simpa [b, finitePrimeBasisProduct, hpS] using hbound
      refine ⟨b, hbBound, ?_⟩
      intro q hq
      simp only [Finset.mem_insert] at hq
      rcases hq with hqp | hq
      · subst q
        by_cases hσ : sigma p = true
        · have hbp : b ≡ a [MOD p] := by
            have h := (Nat.chineseRemainder hcop c bS).property.1
            simpa [b, c, hσ] using h
          have hcast : (b : ZMod p) = (a : ZMod p) :=
            (ZMod.natCast_eq_natCast_iff b a p).mpr hbp
          simp only [if_pos hσ]
          exact hcast
        · have hbc : b ≡ (p - a % p) [MOD p] := by
            have h := (Nat.chineseRemainder hcop c bS).property.1
            simpa [b, c, hσ] using h
          have hcast : (b : ZMod p) =
              ((p - a % p : ℕ) : ZMod p) :=
            (ZMod.natCast_eq_natCast_iff b (p - a % p) p).mpr hbc
          simp only [if_neg hσ]
          exact hcast.trans (neg_residue_in_zmod hp)
      · have hmodS : b ≡ bS [MOD finitePrimeBasisProduct S] := by
          simpa [b] using
            (Nat.chineseRemainder hcop c bS).property.2
        have hqdiv : q ∣ finitePrimeBasisProduct S :=
          mem_dvd_finitePrimeBasisProduct hq
        have hmodq : b ≡ bS [MOD q] := hmodS.of_dvd hqdiv
        have hcast : (b : ZMod q) = (bS : ZMod q) :=
          (ZMod.natCast_eq_natCast_iff b bS q).mpr hmodq
        have hold := hchoiceS q hq
        by_cases hσ : sigma q = true
        · have hplus : (bS : ZMod q) = (a : ZMod q) := by
            simpa [RealizesPrimeSignChoice, hσ] using hold
          simp only [if_pos hσ]
          exact hcast.trans hplus
        · have hminus : (bS : ZMod q) = -(a : ZMod q) := by
            simpa [RealizesPrimeSignChoice, hσ] using hold
          simp only [if_neg hσ]
          exact hcast.trans hminus

/-- CRT synthesis also returns an anchor in the same square phase as the base anchor. -/
theorem exists_sameSquareAnchorPhase_realizing_primeSignChoice
    {S : Finset ℕ}
    (hS : IsFinitePrimeBasis S)
    (sigma : ℕ → Bool)
    (a : ℕ) :
    ∃ b : ℕ,
      b < finitePrimeBasisProduct S ∧
      RealizesPrimeSignChoice S sigma a b ∧
      SameSquareAnchorPhase S a b := by
  obtain ⟨b, hb, hchoice⟩ :=
    exists_anchor_lt_period_realizing_primeSignChoice hS sigma a
  refine ⟨b, hb, hchoice, ?_⟩
  apply primeSignProfile_implies_sameSquareAnchorPhase hS
  exact realizesPrimeSignChoice_implies_primeSignProfile hS hchoice

/-! ## Visible mixed-sign regression -/

private theorem isFinitePrimeBasis_two_three_five :
    IsFinitePrimeBasis ({2, 3, 5} : Finset ℕ) := by
  intro p hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl <;> norm_num

/-- The assignment `(+,+,-)` for base `1` is realized by the mixed residue `19 < 30`. -/
theorem mixedPrimeSign_two_three_five_regression :
    19 < finitePrimeBasisProduct ({2, 3, 5} : Finset ℕ) ∧
      RealizesPrimeSignChoice ({2, 3, 5} : Finset ℕ)
        (fun p => if p = 5 then false else true) 1 19 ∧
      SameSquareAnchorPhase ({2, 3, 5} : Finset ℕ) 1 19 := by
  have hS := isFinitePrimeBasis_two_three_five
  have hchoice : RealizesPrimeSignChoice ({2, 3, 5} : Finset ℕ)
      (fun p => if p = 5 then false else true) 1 19 := by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl <;> decide
  refine ⟨by norm_num [finitePrimeBasisProduct], hchoice, ?_⟩
  apply primeSignProfile_implies_sameSquareAnchorPhase hS
  exact realizesPrimeSignChoice_implies_primeSignProfile hS hchoice

end DkMath.NumberTheory.PrimorialUniverse
