/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.PrimorialUniverse.SquareAnchorPrimeSignCRT
import Mathlib.Tactic

#print "file: DkMath.NumberTheory.PrimorialUniverse.SquareAnchorPhaseFiber"

/-!
# Square-anchor phase fibers

This provider-side module counts the one-period square-phase fiber of a
coprime anchor.  The prime `2` is deliberately removed from the sign index:
there is no plus/minus distinction there, while every other basis prime has
two distinct signs.  CRT synthesis supplies every subset of the remaining
prime basis, and the resulting finite bijection gives the exact cardinality.

The result is a finite congruence statement only.  It does not introduce an
arbitrary-anchor count, higher prime powers, an escape or Legendre provider,
PowerSwap, or an analytic consumer.
-/

namespace DkMath.NumberTheory.PrimorialUniverse

/-! ## The one-period fiber -/

/-!
The representatives below the finite basis period having the same square
phase as `a` form the fiber counted in this file.
-/
noncomputable def squareAnchorPhaseFiber (S : Finset ℕ) (a : ℕ) : Finset ℕ :=
  by
    classical
    exact (Finset.range (finitePrimeBasisProduct S)).filter
      (fun b => SameSquareAnchorPhase S a b)

@[simp] theorem mem_squareAnchorPhaseFiber {S : Finset ℕ} {a b : ℕ} :
    b ∈ squareAnchorPhaseFiber S a ↔
      b < finitePrimeBasisProduct S ∧ SameSquareAnchorPhase S a b := by
  simp [squareAnchorPhaseFiber]

/-! ## Coprimality and sign separation -/

/-! A basis prime cannot divide a coprime anchor. -/
theorem prime_not_dvd_coprime_anchor
    {S : Finset ℕ}
    (hS : IsFinitePrimeBasis S)
    {a : ℕ} (hcop : Nat.Coprime a (finitePrimeBasisProduct S))
    {p : ℕ} (hpS : p ∈ S) :
    ¬ p ∣ a := by
  have hpM : p ∣ finitePrimeBasisProduct S :=
    mem_dvd_finitePrimeBasisProduct hpS
  have hpa : Nat.Coprime p a :=
    (Nat.Coprime.of_dvd_right hpM hcop).symm
  exact (hS p hpS).coprime_iff_not_dvd.mp hpa

/-! The anchor has a nonzero residue at every basis prime. -/
theorem prime_anchor_cast_ne_zero
    {S : Finset ℕ}
    (hS : IsFinitePrimeBasis S)
    {a : ℕ} (hcop : Nat.Coprime a (finitePrimeBasisProduct S))
    {p : ℕ} (hpS : p ∈ S) :
    (a : ZMod p) ≠ 0 := by
  intro ha
  exact prime_not_dvd_coprime_anchor hS hcop hpS
    ((ZMod.natCast_eq_zero_iff a p).mp ha)

/-! At an odd basis prime, the plus and minus residues are distinct. -/
theorem primeSign_plus_ne_minus_of_coprime_anchor
    {S : Finset ℕ}
    (hS : IsFinitePrimeBasis S)
    {a : ℕ} (hcop : Nat.Coprime a (finitePrimeBasisProduct S))
    {p : ℕ} (hpS : p ∈ S) (hp2 : p ≠ 2) :
    (a : ZMod p) ≠ -(a : ZMod p) := by
  letI : Fact (Nat.Prime p) := ⟨hS p hpS⟩
  intro hsign
  have hsum : (a : ZMod p) + (a : ZMod p) = 0 := by
    calc
      (a : ZMod p) + (a : ZMod p) =
          (a : ZMod p) + -(a : ZMod p) :=
            congrArg (fun x => (a : ZMod p) + x) hsign
      _ = 0 := add_neg_cancel _
  have hmul : (2 : ZMod p) * (a : ZMod p) = 0 := by
    simpa [two_mul] using hsum
  rcases mul_eq_zero.mp hmul with htwo | ha
  · have hpdiv2 : p ∣ 2 :=
      (ZMod.natCast_eq_zero_iff 2 p).mp htwo
    have hpeq : p = 2 := by
      exact ((Nat.dvd_prime Nat.prime_two).mp hpdiv2).resolve_left
        (hS p hpS).ne_one
    exact hp2 hpeq
  · exact prime_anchor_cast_ne_zero hS hcop hpS ha

/-! ## The minus-sign subset -/

/-! The odd basis primes at which `b` realizes the minus sign of `a`. -/
noncomputable def squareAnchorMinusPrimeSet
    (S : Finset ℕ) (a b : ℕ) : Finset ℕ :=
  by
    classical
    exact (S.erase 2).filter (fun p => ((b : ZMod p) = -(a : ZMod p)))

@[simp] theorem mem_squareAnchorMinusPrimeSet
    {S : Finset ℕ} {a b p : ℕ} :
    p ∈ squareAnchorMinusPrimeSet S a b ↔
      p ∈ S.erase 2 ∧ ((b : ZMod p) = -(a : ZMod p)) := by
  simp [squareAnchorMinusPrimeSet]

/-! A local congruence at every basis prime lifts to the basis product. -/
theorem modEq_finitePrimeBasisProduct_of_forall_modEq
    {S : Finset ℕ}
    (hS : IsFinitePrimeBasis S)
    {b c : ℕ}
    (hmod : ∀ p ∈ S, b ≡ c [MOD p]) :
    b ≡ c [MOD finitePrimeBasisProduct S] := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      change b % finitePrimeBasisProduct ∅ = c % finitePrimeBasisProduct ∅
      simp [finitePrimeBasisProduct, Nat.mod_one]
  | @insert p S hpS ih =>
      have hp : Nat.Prime p := hS p (Finset.mem_insert_self p S)
      have hS' : IsFinitePrimeBasis S := by
        intro q hq
        exact hS q (Finset.mem_insert_of_mem hq)
      have hmodS : b ≡ c [MOD finitePrimeBasisProduct S] :=
        ih hS' (fun q hq => hmod q (Finset.mem_insert_of_mem hq))
      have hcop : Nat.Coprime p (finitePrimeBasisProduct S) := by
        unfold finitePrimeBasisProduct
        rw [Nat.coprime_prod_right_iff]
        intro q hq
        apply (Nat.coprime_primes hp (hS q (Finset.mem_insert_of_mem hq))).mpr
        intro hpq
        apply hpS
        simpa [hpq] using hq
      have hmod' : b ≡ c [MOD p * finitePrimeBasisProduct S] :=
        (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp
          ⟨hmod p (Finset.mem_insert_self p S), hmodS⟩
      change b % (p * finitePrimeBasisProduct S) =
        c % (p * finitePrimeBasisProduct S) at hmod'
      change b % finitePrimeBasisProduct (insert p S) =
        c % finitePrimeBasisProduct (insert p S)
      simpa [finitePrimeBasisProduct, hpS] using hmod'

/-! Equal minus-sign subsets identify two coprime anchors in the fiber. -/
theorem squareAnchorPhaseFiber_eq_of_minusPrimeSet_eq
    {S : Finset ℕ}
    (hS : IsFinitePrimeBasis S)
    {a : ℕ} (_hcop : Nat.Coprime a (finitePrimeBasisProduct S))
    {b c : ℕ}
    (hb : b ∈ squareAnchorPhaseFiber S a)
    (hc : c ∈ squareAnchorPhaseFiber S a)
    (hminus : squareAnchorMinusPrimeSet S a b =
      squareAnchorMinusPrimeSet S a c) :
    b = c := by
  have hb' := mem_squareAnchorPhaseFiber.mp hb
  have hc' := mem_squareAnchorPhaseFiber.mp hc
  have hprofileB : SameSquarePrimeSignProfile S a b :=
    (sameSquareAnchorPhase_iff_primeSignProfile hS).mp hb'.2
  have hprofileC : SameSquarePrimeSignProfile S a c :=
    (sameSquareAnchorPhase_iff_primeSignProfile hS).mp hc'.2
  have hlocal : ∀ p ∈ S, b ≡ c [MOD p] := by
    intro p hpS
    by_cases hp2 : p = 2
    · subst p
      have hB : (b : ZMod 2) = (a : ZMod 2) := by
        rcases hprofileB 2 hpS with h | h
        · exact h.symm
        · simpa using h.symm
      have hC : (c : ZMod 2) = (a : ZMod 2) := by
        rcases hprofileC 2 hpS with h | h
        · exact h.symm
        · simpa using h.symm
      exact (ZMod.natCast_eq_natCast_iff b c 2).mp (hB.trans hC.symm)
    · have hsignB := hprofileB p hpS
      have hsignC := hprofileC p hpS
      have hminusMem :
          p ∈ squareAnchorMinusPrimeSet S a b ↔
            p ∈ squareAnchorMinusPrimeSet S a c := by
        rw [hminus]
      by_cases hBm : (b : ZMod p) = -(a : ZMod p)
      · have hmemB : p ∈ squareAnchorMinusPrimeSet S a b :=
          mem_squareAnchorMinusPrimeSet.mpr
            ⟨Finset.mem_erase.mpr ⟨hp2, hpS⟩, hBm⟩
        have hmemC := hminusMem.mp hmemB
        have hCm : (c : ZMod p) = -(a : ZMod p) :=
          (mem_squareAnchorMinusPrimeSet.mp hmemC).2
        exact (ZMod.natCast_eq_natCast_iff b c p).mp (hBm.trans hCm.symm)
      · have hCnot : ¬ (c : ZMod p) = -(a : ZMod p) := by
          intro hCm
          apply hBm
          have hmemC : p ∈ squareAnchorMinusPrimeSet S a c :=
            mem_squareAnchorMinusPrimeSet.mpr
              ⟨Finset.mem_erase.mpr ⟨hp2, hpS⟩, hCm⟩
          have hmemB := hminusMem.mpr hmemC
          exact (mem_squareAnchorMinusPrimeSet.mp hmemB).2
        have hBnot : ¬ (a : ZMod p) = -(b : ZMod p) := by
          intro h
          apply hBm
          rw [h]
          simp
        have hCnot' : ¬ (a : ZMod p) = -(c : ZMod p) := by
          intro h
          apply hCnot
          rw [h]
          simp
        have hBplus : (a : ZMod p) = (b : ZMod p) := hsignB.resolve_right hBnot
        have hCplus : (a : ZMod p) = (c : ZMod p) := hsignC.resolve_right hCnot'
        exact (ZMod.natCast_eq_natCast_iff b c p).mp
          (hBplus.symm.trans hCplus)
  have hmod := modEq_finitePrimeBasisProduct_of_forall_modEq hS hlocal
  change b % finitePrimeBasisProduct S = c % finitePrimeBasisProduct S at hmod
  calc
    b = b % finitePrimeBasisProduct S := (Nat.mod_eq_of_lt hb'.1).symm
    _ = c % finitePrimeBasisProduct S := hmod
    _ = c := Nat.mod_eq_of_lt hc'.1

/-! ## Surjectivity from CRT -/

/-! Every subset of the odd basis is the minus-sign set of a fiber element. -/
theorem exists_phaseFiber_anchor_with_minusPrimeSet
    {S : Finset ℕ}
    (hS : IsFinitePrimeBasis S)
    {a : ℕ} (hcop : Nat.Coprime a (finitePrimeBasisProduct S))
    {T : Finset ℕ} (hT : T ⊆ S.erase 2) :
    ∃ b, b ∈ squareAnchorPhaseFiber S a ∧
      squareAnchorMinusPrimeSet S a b = T := by
  let sigma : ℕ → Bool := fun p => decide (p ∉ T)
  obtain ⟨b, hb, hchoice, hphase⟩ :=
    exists_sameSquareAnchorPhase_realizing_primeSignChoice hS sigma a
  refine ⟨b, mem_squareAnchorPhaseFiber.mpr ⟨hb, hphase⟩, ?_⟩
  ext p
  constructor
  · intro hp
    have hpdata := mem_squareAnchorMinusPrimeSet.mp hp
    by_contra hpT
    have hplus : (b : ZMod p) = (a : ZMod p) := by
      have hpS := (Finset.mem_erase.mp hpdata.1).2
      have h := hchoice p hpS
      simpa [sigma, hpT] using h
    have haa : (a : ZMod p) = -(a : ZMod p) := hplus.symm.trans hpdata.2
    have hpErase := Finset.mem_erase.mp hpdata.1
    exact primeSign_plus_ne_minus_of_coprime_anchor hS hcop hpErase.2 hpErase.1 haa
  · intro hpT
    have hpErase := hT hpT
    have hpdata := Finset.mem_erase.mp hpErase
    have hminus : (b : ZMod p) = -(a : ZMod p) := by
      have h := hchoice p hpdata.2
      simpa [sigma, hpT] using h
    exact mem_squareAnchorMinusPrimeSet.mpr ⟨hpErase, hminus⟩

/-! ## Exact finite cardinality -/

/-!
For a coprime anchor, the fiber is in bijection with the powerset of
`S.erase 2`.  Thus the only loss of sign information is the unavoidable
identification at the prime `2`.
-/
theorem squareAnchorPhaseFiber_card_of_coprime_anchor
    {S : Finset ℕ}
    (hS : IsFinitePrimeBasis S)
    {a : ℕ} (hcop : Nat.Coprime a (finitePrimeBasisProduct S)) :
    (squareAnchorPhaseFiber S a).card = 2 ^ (S.erase 2).card := by
  classical
  let odd : Finset ℕ := S.erase 2
  let i : ∀ T ∈ odd.powerset, ℕ := fun T hT =>
    Classical.choose (exists_phaseFiber_anchor_with_minusPrimeSet hS hcop
      (T := T) (Finset.mem_powerset.mp hT))
  have hi : ∀ T hT, i T hT ∈ squareAnchorPhaseFiber S a := by
    intro T hT
    exact (Classical.choose_spec
      (exists_phaseFiber_anchor_with_minusPrimeSet hS hcop
        (T := T) (Finset.mem_powerset.mp hT))).1
  have hi_inj : ∀ T hT U hU, i T hT = i U hU → T = U := by
    intro T hT U hU heq
    have hTset := (Classical.choose_spec
      (exists_phaseFiber_anchor_with_minusPrimeSet hS hcop
        (T := T) (Finset.mem_powerset.mp hT))).2
    have hUset := (Classical.choose_spec
      (exists_phaseFiber_anchor_with_minusPrimeSet hS hcop
        (T := U) (Finset.mem_powerset.mp hU))).2
    calc
      T = squareAnchorMinusPrimeSet S a (i T hT) := hTset.symm
      _ = squareAnchorMinusPrimeSet S a (i U hU) := by rw [heq]
      _ = U := hUset
  have hi_surj : ∀ b, b ∈ squareAnchorPhaseFiber S a →
      ∃ T hT, i T hT = b := by
    intro b hb
    let T : Finset ℕ := squareAnchorMinusPrimeSet S a b
    have hTsub : T ⊆ odd := by
      intro p hp
      have hpdata := mem_squareAnchorMinusPrimeSet.mp hp
      exact hpdata.1
    have hT : T ∈ odd.powerset := Finset.mem_powerset.mpr hTsub
    have hiT := hi T hT
    have hTset := (Classical.choose_spec
      (exists_phaseFiber_anchor_with_minusPrimeSet hS hcop
        (T := T) (Finset.mem_powerset.mp hT))).2
    have hsame : squareAnchorMinusPrimeSet S a (i T hT) =
        squareAnchorMinusPrimeSet S a b := by
      calc
        squareAnchorMinusPrimeSet S a (i T hT) = T := hTset
        _ = squareAnchorMinusPrimeSet S a b := rfl
    exact ⟨T, hT, squareAnchorPhaseFiber_eq_of_minusPrimeSet_eq
      hS hcop hiT hb hsame⟩
  have hcard : odd.powerset.card =
      (squareAnchorPhaseFiber S a).card := by
    apply Finset.card_bij i hi hi_inj
    exact hi_surj
  calc
    (squareAnchorPhaseFiber S a).card = odd.powerset.card := hcard.symm
    _ = 2 ^ odd.card := Finset.card_powerset odd
    _ = 2 ^ (S.erase 2).card := by rfl

/-! ## Concrete regressions -/

private theorem isFinitePrimeBasis_two_three_five_phaseFiber :
    IsFinitePrimeBasis ({2, 3, 5} : Finset ℕ) := by
  intro p hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl <;> norm_num

/-! The `{2, 3, 5}` coprime fiber has four representatives in one period. -/
theorem squareAnchorPhaseFiber_two_three_five_regression :
    (squareAnchorPhaseFiber ({2, 3, 5} : Finset ℕ) 1).card = 4 ∧
      1 ∈ squareAnchorPhaseFiber ({2, 3, 5} : Finset ℕ) 1 ∧
      11 ∈ squareAnchorPhaseFiber ({2, 3, 5} : Finset ℕ) 1 ∧
      19 ∈ squareAnchorPhaseFiber ({2, 3, 5} : Finset ℕ) 1 ∧
      29 ∈ squareAnchorPhaseFiber ({2, 3, 5} : Finset ℕ) 1 := by
  have hS := isFinitePrimeBasis_two_three_five_phaseFiber
  have hcop : Nat.Coprime 1 (finitePrimeBasisProduct
      ({2, 3, 5} : Finset ℕ)) := by simp
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [finitePrimeBasisProduct] using
      (squareAnchorPhaseFiber_card_of_coprime_anchor hS hcop)
  all_goals
    norm_num [squareAnchorPhaseFiber, SameSquareAnchorPhase,
      squareAnchorWheelProjection, primeBasisWheelProjection,
      finitePrimeBasisProduct]

end DkMath.NumberTheory.PrimorialUniverse
