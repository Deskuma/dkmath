/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Collatz.PetalBridge.FloatWindow.FiniteSignedTransition

#print "file: DkMath.Collatz.PetalBridge.FloatWindow.FinitePotentialIncompleteness"

namespace DkMath.Collatz

/-!
# Finite-potential incompleteness witness

Uniformly nonpositive prefix sums do not imply a pointwise upper bound on
signed increments.  The explicit pair sequence below makes that distinction
formal.  Consequently, a finite successor upper-weight table is a strictly
stronger certificate shape than the prefix inequality it is intended to
prove.
-/

/-- Alternating signed weights with cancelling pairs and unbounded positive
odd-index terms:

`w (2*k) = -(k+1)` and `w (2*k+1) = k+1`.
-/
def alternatingUnboundedWeight (m : ℕ) : ℤ :=
  if m % 2 = 0 then -((m / 2 + 1 : ℕ) : ℤ)
  else ((m / 2 + 1 : ℕ) : ℤ)

@[simp] theorem alternatingUnboundedWeight_even (k : ℕ) :
    alternatingUnboundedWeight (2 * k) = -((k + 1 : ℕ) : ℤ) := by
  simp [alternatingUnboundedWeight]

@[simp] theorem alternatingUnboundedWeight_odd (k : ℕ) :
    alternatingUnboundedWeight (2 * k + 1) = ((k + 1 : ℕ) : ℤ) := by
  have hmod : (2 * k + 1) % 2 = 1 := by omega
  have hdiv : (2 * k + 1) / 2 = k := by omega
  simp [alternatingUnboundedWeight, hmod, hdiv]

/-- Every complete pair prefix has total zero. -/
theorem sum_alternatingUnboundedWeight_range_even (k : ℕ) :
    (∑ m ∈ Finset.range (2 * k), alternatingUnboundedWeight m) = 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [show 2 * (k + 1) = (2 * k + 1) + 1 by omega,
        Finset.sum_range_succ,
        show 2 * k + 1 = 2 * k + 1 by rfl,
        Finset.sum_range_succ, ih]
      simp

/-- A prefix ending after a negative term has total `-(k+1)`. -/
theorem sum_alternatingUnboundedWeight_range_odd (k : ℕ) :
    (∑ m ∈ Finset.range (2 * k + 1), alternatingUnboundedWeight m) =
      -((k + 1 : ℕ) : ℤ) := by
  rw [Finset.sum_range_succ, sum_alternatingUnboundedWeight_range_even]
  simp

/-- Every prefix sum of the explicit sequence is nonpositive. -/
theorem sum_alternatingUnboundedWeight_range_nonpos (M : ℕ) :
    (∑ m ∈ Finset.range M, alternatingUnboundedWeight m) ≤ 0 := by
  rcases Nat.even_or_odd M with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · simpa [two_mul] using
      (show (∑ m ∈ Finset.range (2 * k), alternatingUnboundedWeight m) ≤ 0 by
        rw [sum_alternatingUnboundedWeight_range_even])
  · simpa [two_mul] using
      (show (∑ m ∈ Finset.range (2 * k + 1), alternatingUnboundedWeight m) ≤ 0 by
        rw [sum_alternatingUnboundedWeight_range_odd]
        exact neg_nonpos.mpr (Int.natCast_nonneg _))

/-- Positive individual terms of the sequence are unbounded above. -/
theorem alternatingUnboundedWeight_not_bddAbove :
    ∀ B : ℤ, ∃ m : ℕ, B < alternatingUnboundedWeight m := by
  intro B
  refine ⟨2 * B.natAbs + 1, ?_⟩
  rw [alternatingUnboundedWeight_odd]
  have habs : B ≤ |B| := le_abs_self B
  have hcast : (B.natAbs : ℤ) = |B| := by simp
  rw [← hcast] at habs
  omega

/-- No finite signature admits a sound successor upper-weight table for the
explicit sequence, despite all of its prefixes being nonpositive. -/
theorem no_finiteSignatureSuccessorUpperWeight_alternatingUnboundedWeight
    {Signature : Type*} [Finite Signature]
    (signature : ℕ → Signature) :
    ¬ ∃ projectedUpperWeight : Signature → Signature → ℤ,
      FiniteSignatureSuccessorUpperWeightSound signature
        alternatingUnboundedWeight projectedUpperWeight := by
  intro htable
  have hbound :=
    (exists_finiteSignatureSuccessorUpperWeight_iff_uniformUpperBound
      signature alternatingUnboundedWeight).mp htable
  rcases hbound with ⟨B, hB⟩
  rcases alternatingUnboundedWeight_not_bddAbove B with ⟨m, hm⟩
  exact (not_lt_of_ge (hB m)) hm

/-!
The two theorems
`sum_alternatingUnboundedWeight_range_nonpos` and
`no_finiteSignatureSuccessorUpperWeight_alternatingUnboundedWeight` formally
separate the desired prefix property from the stronger finite-table method.
Failure of that method is therefore not evidence that a prefix theorem is
false; it is evidence that an unbounded counter may be required.
-/

end DkMath.Collatz
