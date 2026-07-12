/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Collatz.PetalBridge.FloatWindow.PaymentBlockBridge

#print "file: DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentBlock"

namespace DkMath.Collatz

/-!
# Universal first-payment coordinates

The earlier `floatDebtPaymentTarget` was introduced for delayed width-growth
debts.  Exact all-ones depth, however, assigns the same canonical target to
every orbit time.  This module exposes that total coordinate without turning a
first-claim relation into a final allocation claim.
-/

/-- The canonical payment target determined by exact all-ones depth at any orbit time. -/
noncomputable def orbitPaymentTarget (n : OddNat) (i : ℕ) : ℕ :=
  i + orbitExactDepth n i - 1

/-- The debt-facing target is definitionally the universal target. -/
theorem floatDebtPaymentTarget_eq_orbitPaymentTarget
    (n : OddNat) (i : ℕ) :
    floatDebtPaymentTarget n i = orbitPaymentTarget n i := rfl

/-- A height-one source has a strictly later canonical payment target. -/
theorem lt_orbitPaymentTarget_of_orbitWindowHeight_eq_one
    {n : OddNat} {i : ℕ}
    (hheight : orbitWindowHeight n i = 1) :
    i < orbitPaymentTarget n i := by
  unfold orbitPaymentTarget
  have hdepth := (orbitWindowHeight_eq_one_iff_two_le_orbitExactDepth n i).1 hheight
  omega

/-- An extra-height event pays immediately at its own orbit time. -/
theorem orbitPaymentTarget_eq_self_of_two_le_orbitWindowHeight
    {n : OddNat} {i : ℕ}
    (hheight : 2 ≤ orbitWindowHeight n i) :
    orbitPaymentTarget n i = i := by
  unfold orbitPaymentTarget
  have hdepth := (two_le_orbitWindowHeight_iff_orbitExactDepth_eq_one n i).1 hheight
  omega

/-- Every orbit time targets a genuine extra-height payment slot. -/
theorem two_le_orbitWindowHeight_orbitPaymentTarget
    (n : OddNat) (i : ℕ) :
    2 ≤ orbitWindowHeight n (orbitPaymentTarget n i) := by
  by_cases hheight : orbitWindowHeight n i = 1
  · have hdepth := (orbitWindowHeight_eq_one_iff_two_le_orbitExactDepth n i).1 hheight
    have hexact : OrbitDepthRecoversExactlyAt n i (orbitExactDepth n i) := by rfl
    simpa [orbitPaymentTarget] using
      orbitDepthRecoversExactlyAt_delayed_height_two_le n i (orbitExactDepth n i) hdepth hexact
  · have htwo : 2 ≤ orbitWindowHeight n i := by
      have hone := orbitWindowHeight_one_le n i
      omega
    rw [orbitPaymentTarget_eq_self_of_two_le_orbitWindowHeight htwo]
    exact htwo

/-- All sources at most `j` whose canonical payment target is `j`. -/
noncomputable def orbitPaymentSourceFiberAt (n : OddNat) (j : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (j + 1)).filter fun i => orbitPaymentTarget n i = j

/-- Membership API for a universal canonical payment-source fiber. -/
theorem mem_orbitPaymentSourceFiberAt_iff
    {n : OddNat} {i j : ℕ} :
    i ∈ orbitPaymentSourceFiberAt n j ↔ i ≤ j ∧ orbitPaymentTarget n i = j := by
  classical
  simp [orbitPaymentSourceFiberAt]

/-- A nonempty universal source fiber has a canonical earliest source. -/
noncomputable def universalPaymentBlockStart
    (n : OddNat) (j : ℕ) (h : (orbitPaymentSourceFiberAt n j).Nonempty) : ℕ :=
  (orbitPaymentSourceFiberAt n j).min' h

/-- The universal block start belongs to its endpoint's source fiber. -/
theorem universalPaymentBlockStart_mem_sourceFiber
    (n : OddNat) (j : ℕ) (h : (orbitPaymentSourceFiberAt n j).Nonempty) :
    universalPaymentBlockStart n j h ∈ orbitPaymentSourceFiberAt n j :=
  Finset.min'_mem _ h

/-- Every time belongs to the universal source fiber of its own canonical target. -/
theorem self_mem_orbitPaymentSourceFiberAt_target
    (n : OddNat) (i : ℕ) :
    i ∈ orbitPaymentSourceFiberAt n (orbitPaymentTarget n i) := by
  rw [mem_orbitPaymentSourceFiberAt_iff]
  constructor
  · by_cases hheight : orbitWindowHeight n i = 1
    · exact (lt_orbitPaymentTarget_of_orbitWindowHeight_eq_one hheight).le
    · have htwo : 2 ≤ orbitWindowHeight n i := by
        have hone := orbitWindowHeight_one_le n i
        omega
      rw [orbitPaymentTarget_eq_self_of_two_le_orbitWindowHeight htwo]
  · rfl

/-- Every canonical payment target has a nonempty universal source fiber. -/
theorem orbitPaymentSourceFiberAt_nonempty_target
    (n : OddNat) (i : ℕ) :
    (orbitPaymentSourceFiberAt n (orbitPaymentTarget n i)).Nonempty :=
  ⟨i, self_mem_orbitPaymentSourceFiberAt_target n i⟩

/-- A nonempty universal source fiber has an actual extra-height endpoint. -/
theorem two_le_orbitWindowHeight_of_orbitPaymentSourceFiberAt_nonempty
    {n : OddNat} {j : ℕ}
    (h : (orbitPaymentSourceFiberAt n j).Nonempty) :
    2 ≤ orbitWindowHeight n j := by
  rcases h with ⟨i, hi⟩
  have htarget := (mem_orbitPaymentSourceFiberAt_iff.mp hi).2
  rw [← htarget]
  exact two_le_orbitWindowHeight_orbitPaymentTarget n i

/-- A nonempty universal source fiber contains its endpoint as the immediate source. -/
theorem endpoint_mem_orbitPaymentSourceFiberAt_of_nonempty
    {n : OddNat} {j : ℕ}
    (h : (orbitPaymentSourceFiberAt n j).Nonempty) :
    j ∈ orbitPaymentSourceFiberAt n j := by
  rw [mem_orbitPaymentSourceFiberAt_iff]
  exact ⟨le_rfl,
    orbitPaymentTarget_eq_self_of_two_le_orbitWindowHeight
      (two_le_orbitWindowHeight_of_orbitPaymentSourceFiberAt_nonempty h)⟩

/-- Every delayed growth-debt source is a universal source for the same target. -/
theorem mem_orbitPaymentSourceFiberAt_of_mem_floatGrowthDebtFiberAt
    {n : OddNat} {i j : ℕ}
    (hi : i ∈ floatGrowthDebtFiberAt n j) :
    i ∈ orbitPaymentSourceFiberAt n j := by
  rcases mem_floatGrowthDebtFiberAt_iff.mp hi with ⟨hij, _, htarget⟩
  rw [mem_orbitPaymentSourceFiberAt_iff]
  exact ⟨by omega,
    by simpa [← floatDebtPaymentTarget_eq_orbitPaymentTarget] using htarget⟩

/-- A nonempty delayed growth-debt fiber induces a nonempty universal source fiber. -/
theorem orbitPaymentSourceFiberAt_nonempty_of_floatGrowthDebtFiberAt_nonempty
    {n : OddNat} {j : ℕ}
    (h : (floatGrowthDebtFiberAt n j).Nonempty) :
    (orbitPaymentSourceFiberAt n j).Nonempty := by
  rcases h with ⟨i, hi⟩
  exact ⟨i, mem_orbitPaymentSourceFiberAt_of_mem_floatGrowthDebtFiberAt hi⟩

/--
The universal block begins no later than the delayed-growth-debt block.

This is only an inclusion-of-fibers statement.  Equality is not claimed: the
universal fiber can contain height-one sources that are not Float growth debts.
-/
theorem universalPaymentBlockStart_le_floatPaymentBlockStart
    (n : OddNat) (j : ℕ) (h : (floatGrowthDebtFiberAt n j).Nonempty) :
    universalPaymentBlockStart n j
      (orbitPaymentSourceFiberAt_nonempty_of_floatGrowthDebtFiberAt_nonempty h) ≤
      floatPaymentBlockStart n j h := by
  apply Finset.min'_le
  exact mem_orbitPaymentSourceFiberAt_of_mem_floatGrowthDebtFiberAt
    (floatPaymentBlockStart_mem_growthDebtFiber n j h)

/-!
## Next closure requirement

To identify a nonempty universal source fiber with the full interval from its
minimum to its endpoint, the missing direction is not finite-set arithmetic.
It is an exact-depth staircase *reverse closure*: from a source targeting `j`,
one must show that every intervening time has the corresponding decremented
exact depth and therefore the same target.  Until that theorem is supplied,
this module intentionally exposes membership, minima, endpoint height, and
the debt-fiber inclusion only; it does not claim interval contiguity or
prefix-family coverage.
-/

end DkMath.Collatz
