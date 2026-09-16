/-
Copyright (c) 2026 DkMath contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: DkMath contributors.
-/

import DkMath.NumberTheory.MultiGauge.Basic
import DkMath.NumberTheory.PrimorialUniverse.SquareAnchorOffsetSuccessorPairFreshPrimeTransport

#print "file: DkMath.NumberTheory.Legendre.MultiGaugeBridge"

/-!
# Degree-two MultiGauge bridge for successor increments

The production `GTail` orientation is `GTail 2 1 x u = x + 2 * u`.
Consequently the successor increment `2 * n + 1` is represented by the
reversed stage `(x, u) = (1, n)`. This module only supplies the resulting
single-stage/channel reinterpretation of the existing tied-pair obstruction;
it does not manufacture a concrete two-stage gauge transition.
-/

namespace DkMath.NumberTheory.Legendre

open DkMath.NumberTheory.MultiGauge
open DkMath.NumberTheory.PrimorialUniverse

/-! ## Canonical reversed degree-two stage -/

/-- The canonical GN stage for the successor-square increment `2 * n + 1`. -/
def successorIncrementGaugeStage (n : ℕ) : GNGaugeStage 2 :=
  { x := 1
    u := n
    coprime := by simp }

/-- The reversed degree-two GN observer is exactly the successor increment. -/
theorem successorIncrementGaugeStage_gnValue (n : ℕ) :
    (successorIncrementGaugeStage n).gnValue = 2 * n + 1 := by
  norm_num [successorIncrementGaugeStage, GNGaugeStage.gnValue,
    DkMath.CosmicFormula.GTail, Finset.sum_range_succ]

/-- The full stage value is also the successor increment because the boundary
factor is `1`. -/
theorem successorIncrementGaugeStage_value (n : ℕ) :
    (successorIncrementGaugeStage n).value = 2 * n + 1 := by
  change 1 * (successorIncrementGaugeStage n).gnValue = 2 * n + 1
  rw [successorIncrementGaugeStage_gnValue]
  simp

/-! ## Channel interpretation -/

/-- At the reversed stage, capture is exactly GN-channel divisibility. -/
theorem primeCaught_successorIncrementGaugeStage_iff_gnValue
    (q n : ℕ) :
    PrimeCaught q (successorIncrementGaugeStage n) ↔
      q ∣ (successorIncrementGaugeStage n).gnValue := by
  simp [PrimeCaught, GNGaugeStage.value, successorIncrementGaugeStage]

/-- The stage capture predicate is exactly divisibility of `2 * n + 1`. -/
theorem primeCaught_successorIncrementGaugeStage_iff_increment
    (q n : ℕ) :
    PrimeCaught q (successorIncrementGaugeStage n) ↔ q ∣ 2 * n + 1 := by
  change q ∣ (successorIncrementGaugeStage n).value ↔ q ∣ 2 * n + 1
  rw [successorIncrementGaugeStage_value]

/-! ## Existing tied-pair obstruction as capture -/

/-- The existing tied-pair fresh-prime delay is capture in the reversed GN
stage. -/
theorem fresh_tied_successor_pair_delay_primeCaught
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S) (hSne : S.Nonempty)
    {q : ℕ} (hq : Nat.Prime q) (hqS : q ∉ S) (n h : ℕ)
    (htie0 : squareAnchorFirstPositiveUnreservedOffset S n hS hSne = h)
    (htie1 : squareAnchorFirstPositiveUnreservedOffset S (n + 1) hS hSne = h)
    (hdelay : squareAnchorSuccessorPairPositiveFirstHit S n hS hSne <
      squareAnchorSuccessorPairPositiveFirstHit (insert q S) n
        (isFinitePrimeBasis_insert_fresh hS hq hqS) (by simp)) :
    PrimeCaught q (successorIncrementGaugeStage n) := by
  apply (primeCaught_successorIncrementGaugeStage_iff_increment q n).mpr
  exact freshPrime_dvd_successor_increment_of_tied_pair_delay
    hS hSne hq hqS n h htie0 htie1 hdelay

/-- Escape of the reversed increment stage is precisely the persistence
condition supplied by the existing tied-pair theorem. -/
theorem tied_successor_pair_persists_of_increment_stage_escape
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S) (hSne : S.Nonempty)
    {q : ℕ} (hq : Nat.Prime q) (hqS : q ∉ S) (n h : ℕ)
    (htie0 : squareAnchorFirstPositiveUnreservedOffset S n hS hSne = h)
    (htie1 : squareAnchorFirstPositiveUnreservedOffset S (n + 1) hS hSne = h)
    (hEscape : PrimeEscapes q (successorIncrementGaugeStage n)) :
    squareAnchorSuccessorPairPositiveFirstHit (insert q S) n
        (isFinitePrimeBasis_insert_fresh hS hq hqS) (by simp) =
      squareAnchorSuccessorPairPositiveFirstHit S n hS hSne := by
  have hqnot : ¬ q ∣ 2 * n + 1 := by
    intro hqdiv
    apply hEscape
    exact (primeCaught_successorIncrementGaugeStage_iff_increment q n).mpr hqdiv
  exact squareAnchorSuccessorPairPositiveFirstHit_eq_insert_fresh_of_tied_and_increment_not_dvd
    hS hSne hq hqS n h htie0 htie1 hqnot

end DkMath.NumberTheory.Legendre
