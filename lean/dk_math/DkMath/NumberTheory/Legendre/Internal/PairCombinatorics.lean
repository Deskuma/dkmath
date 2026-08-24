/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.Data.Finset.Prod
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Totient

#print "file: DkMath.NumberTheory.Legendre.Internal.PairCombinatorics"

/-!
## Internal pair combinatorics

Reusable finite unordered-pair representatives and their binomial cardinality.
This internal module has no Legendre mathematics and is shared by the
within-seat localized ledgers without duplicating the combinatorial proof.
-/

namespace DkMath.NumberTheory.Legendre.Internal

open scoped BigOperators

def upperPairs (s : Finset ℕ) : Finset (ℕ × ℕ) :=
  s.offDiag.filter (fun pair => pair.1 < pair.2)

/-- The reverse orientation of the canonical representatives. -/
private def lowerPairs (s : Finset ℕ) : Finset (ℕ × ℕ) :=
  s.offDiag.filter (fun pair => pair.2 < pair.1)

/-- Canonical pair representatives have the expected binomial cardinality. -/
theorem card_upperPairs_eq_choose (s : Finset ℕ) :
    (upperPairs s).card = Nat.choose s.card 2 := by
  classical
  have hswap : (lowerPairs s).card = (upperPairs s).card := by
    apply Finset.card_bij (fun pair _ => (pair.2, pair.1))
    · intro pair hpair
      have hpair' := Finset.mem_filter.mp hpair
      have hdiag := Finset.mem_offDiag.mp hpair'.1
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_offDiag.mpr
          ⟨hdiag.2.1, hdiag.1, Ne.symm hdiag.2.2⟩,
        hpair'.2⟩
    · intro pair₁ hpair₁ pair₂ hpair₂ heq
      exact Prod.ext (congrArg Prod.snd heq) (congrArg Prod.fst heq)
    · intro pair hpair
      refine ⟨(pair.2, pair.1), ?_, ?_⟩
      · have hpair' := Finset.mem_filter.mp hpair
        have hdiag := Finset.mem_offDiag.mp hpair'.1
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_offDiag.mpr
            ⟨hdiag.2.1, hdiag.1, Ne.symm hdiag.2.2⟩,
          hpair'.2⟩
      · rfl
  have hneg : s.offDiag.filter (fun pair => ¬ pair.1 < pair.2) =
      lowerPairs s := by
    ext pair
    simp [lowerPairs]
    omega
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := s.offDiag) (p := fun pair : ℕ × ℕ => pair.1 < pair.2)
  rw [hneg] at hsplit
  have hsum : (upperPairs s).card + (lowerPairs s).card = s.offDiag.card := by
    simpa [upperPairs] using hsplit
  have htwice : 2 * (upperPairs s).card = s.offDiag.card := by
    omega
  rw [Nat.choose_two_right, Nat.mul_sub_left_distrib, mul_one,
    ← Finset.offDiag_card]
  exact (Nat.div_eq_of_eq_mul_right Nat.zero_lt_two htwice.symm).symm

end DkMath.NumberTheory.Legendre.Internal
