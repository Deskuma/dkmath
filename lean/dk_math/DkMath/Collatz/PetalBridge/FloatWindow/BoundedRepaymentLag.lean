/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentAmortizedResource
import Mathlib.Algebra.Order.BigOperators.Group.Finset

#print "file: DkMath.Collatz.PetalBridge.FloatWindow.BoundedRepaymentLag"

namespace DkMath.Collatz

/-!
# Generic bounded repayment lag

The recent window is the half-open interval `[m-L,m)`.  Unlike the former
shifted-range formula, it never refers to arrivals after observation time `m`.
-/

/-- Total arrivals in the at-most-`L` slots immediately preceding `m`. -/
def recentArrivalMass (arrivals : ℕ → ℕ) (L m : ℕ) : ℕ :=
  ∑ k ∈ Finset.Ico (m - L) m, arrivals k

/-- Before the lag horizon is filled, the recent window is the full prefix. -/
theorem recentArrivalMass_eq_sum_range_of_lt
    (arrivals : ℕ → ℕ) {L m : ℕ} (hm : m < L) :
    recentArrivalMass arrivals L m = ∑ k ∈ Finset.range m, arrivals k := by
  unfold recentArrivalMass
  rw [Nat.sub_eq_zero_of_le hm.le, Nat.Ico_zero_eq_range]

/-- After the horizon is filled, the exact past window has `L` shifted slots. -/
theorem recentArrivalMass_eq_sum_range_of_le
    (arrivals : ℕ → ℕ) {L m : ℕ} (hL : L ≤ m) :
    recentArrivalMass arrivals L m =
      ∑ j ∈ Finset.range L, arrivals (m - L + j) := by
  unfold recentArrivalMass
  rw [Finset.sum_Ico_eq_sum_range]
  have hlen : m - (m - L) = L := by omega
  rw [hlen]

/-- The recent half-open interval contains at most `L` indices. -/
theorem card_recentArrivalWindow_le (L m : ℕ) :
    (Finset.Ico (m - L) m).card ≤ L := by
  simp
  omega

/-- Correct scalar lag surface: outstanding work is covered by actual past
arrivals in the recent half-open window. -/
def OutstandingBeforeQueueCoveredByRecentArrivals
    (queue arrivals : ℕ → ℕ) (L : ℕ) : Prop :=
  ∀ m, queue m ≤ recentArrivalMass arrivals L m

/-- Coarse compatibility predicate from cp-331.  It may include future slots
when `m < L`; new proofs should use
`OutstandingBeforeQueueCoveredByRecentArrivals`. -/
@[deprecated OutstandingBeforeQueueCoveredByRecentArrivals (since := "2026-07-16")]
def OutstandingQueueHasRepaymentLag
    (queue arrivals : ℕ → ℕ) (L : ℕ) : Prop :=
  ∀ m, queue m ≤ ∑ j ∈ Finset.range L, arrivals (m - L + j)

/-- A direct recent-window mass ceiling gives the same queue ceiling. -/
theorem queue_le_of_recentArrivalMass_le
    {queue arrivals : ℕ → ℕ} {L B : ℕ}
    (hlag : OutstandingBeforeQueueCoveredByRecentArrivals queue arrivals L)
    (hmass : ∀ m, recentArrivalMass arrivals L m ≤ B) (m : ℕ) :
    queue m ≤ B := (hlag m).trans (hmass m)

/-- Per-slot arrival bound `A` controls each exact recent window by `L*A`. -/
theorem recentArrivalMass_le_mul_of_arrivals_le
    {arrivals : ℕ → ℕ} {L A : ℕ}
    (harrivals : ∀ k, arrivals k ≤ A) (m : ℕ) :
    recentArrivalMass arrivals L m ≤ L * A := by
  unfold recentArrivalMass
  calc
    (∑ k ∈ Finset.Ico (m - L) m, arrivals k) ≤
        ∑ _k ∈ Finset.Ico (m - L) m, A :=
      Finset.sum_le_sum fun k _ => harrivals k
    _ = (Finset.Ico (m - L) m).card * A := by simp
    _ ≤ L * A := Nat.mul_le_mul_right A (card_recentArrivalWindow_le L m)

/-- Correct lag plus per-slot arrivals yields a uniform queue bound. -/
theorem queue_le_mul_of_recentCoverage_of_arrivals_le
    {queue arrivals : ℕ → ℕ} {L A : ℕ}
    (hlag : OutstandingBeforeQueueCoveredByRecentArrivals queue arrivals L)
    (harrivals : ∀ k, arrivals k ≤ A) (m : ℕ) :
    queue m ≤ L * A :=
  (hlag m).trans (recentArrivalMass_le_mul_of_arrivals_le harrivals m)

/-! ## Boundary regressions -/

@[simp] theorem recentArrivalMass_zero (arrivals : ℕ → ℕ) (L : ℕ) :
    recentArrivalMass arrivals L 0 = 0 := by simp [recentArrivalMass]

theorem recentArrivalMass_early
    (arrivals : ℕ → ℕ) {L m : ℕ} (hm : m < L) :
    recentArrivalMass arrivals L m = ∑ k ∈ Finset.range m, arrivals k :=
  recentArrivalMass_eq_sum_range_of_lt arrivals hm

theorem recentArrivalMass_at_horizon (arrivals : ℕ → ℕ) (L : ℕ) :
    recentArrivalMass arrivals L L = ∑ k ∈ Finset.range L, arrivals k := by
  simpa using recentArrivalMass_eq_sum_range_of_le arrivals (le_rfl : L ≤ L)

@[simp] theorem recentArrivalMass_lag_zero (arrivals : ℕ → ℕ) (m : ℕ) :
    recentArrivalMass arrivals 0 m = 0 := by simp [recentArrivalMass]

/-! ## Canonical conditional surfaces -/

/-- Conditional lag coverage for the actual canonical reflected queue. -/
def CanonicalOutstandingQueueCoveredByRecentDemand
    (n : OddNat) (L : ℕ) : Prop :=
  OutstandingBeforeQueueCoveredByRecentArrivals
    (canonicalOutstandingClaimQueueBeforeBlock n) (canonicalQueueDemand n) L

/-- Canonical lag plus a per-block demand ceiling gives an explicit queue
ceiling.  Neither hypothesis is currently known uniformly. -/
theorem canonicalQueueBound_of_recentDemandCoverage_of_demand_le
    {n : OddNat} {L A : ℕ}
    (hlag : CanonicalOutstandingQueueCoveredByRecentDemand n L)
    (hdemand : ∀ k, canonicalQueueDemand n k ≤ A) :
    ∀ m, canonicalOutstandingClaimQueueBeforeBlock n m ≤ L * A :=
  fun m => queue_le_mul_of_recentCoverage_of_arrivals_le hlag hdemand m

/-- Canonical lag plus a direct recent-demand mass ceiling gives the sharper
queue ceiling `B`. -/
theorem canonicalQueueBound_of_recentDemandCoverage_of_mass_le
    {n : OddNat} {L B : ℕ}
    (hlag : CanonicalOutstandingQueueCoveredByRecentDemand n L)
    (hmass : ∀ m, recentArrivalMass (canonicalQueueDemand n) L m ≤ B) :
    ∀ m, canonicalOutstandingClaimQueueBeforeBlock n m ≤ B :=
  fun m => queue_le_of_recentArrivalMass_le hlag hmass m

/-!
No uniform canonical `L`, per-block `A`, or recent-window `B` is proved.  The
owned claim carrier remains a possible mechanism for proving lag, but lag and
recent-demand mass control are logically separate obligations.
-/

end DkMath.Collatz
