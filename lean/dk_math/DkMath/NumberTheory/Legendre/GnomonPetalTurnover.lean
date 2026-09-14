/-
Copyright (c) 2026 DkMath contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: DkMath contributors.
-/

import DkMath.NumberTheory.Legendre.GnomonSupportTurnover
import DkMath.NumberTheory.MultiGauge.GnomonPetalTransition

#print "file: DkMath.NumberTheory.Legendre.GnomonPetalTurnover"

/-!
# Petal factorization of lower adjacent-shell support turnover

This module connects the exact lower-region support turnover theorem to the
production Petal multiplication law.  When the shell index has the form
`petalMul a b`, the common old/successor support can only lie in the prime
support of the two odd-gnomon factors.

The second factor is exactly the numerator support of
`gnomonPetalTransition a b`.  Thus any common lower support not inherited from
the first Petal factor is localized to a genuine MultiGauge transition
numerator.
-/

namespace DkMath.NumberTheory.Legendre

open DkMath.NumberTheory.MultiGauge

/-- Exact Petal-factor decomposition of common lower-region support. -/
theorem mem_reindexed_primeSupport_inter_lower_petalMul_iff
    {a b r q : ℕ}
    (hr : SquareOffset (DkMath.Gnomon.petalMul a b) r)
    (hlow : r < DkMath.Gnomon.petalMul a b + 1)
    (hq : Nat.Prime q) :
    q ∈ squareOffsetPrimeSupport (DkMath.Gnomon.petalMul a b) r ∩
        squareOffsetPrimeSupport (DkMath.Gnomon.petalMul a b + 1)
          (successorThresholdInsert (DkMath.Gnomon.petalMul a b) r) ↔
      q ∈ squareOffsetPrimeSupport (DkMath.Gnomon.petalMul a b) r ∧
        (q ∣ DkMath.Gnomon.oddGnomon a ∨
          q ∣ DkMath.Gnomon.oddGnomon b) := by
  rw [mem_reindexed_primeSupport_inter_lower_iff hr hlow]
  rw [DkMath.Gnomon.oddGnomon_petalMul]
  rw [hq.dvd_mul]

/-- If common lower support does not come from the first Petal factor, it must
come from the second factor, hence from the MultiGauge transition numerator. -/
theorem common_lower_dvd_gnomonPetalTransition_numerator_of_not_dvd_first
    {a b r q : ℕ}
    (hr : SquareOffset (DkMath.Gnomon.petalMul a b) r)
    (hlow : r < DkMath.Gnomon.petalMul a b + 1)
    (hq : Nat.Prime q)
    (hnotFirst : ¬ q ∣ DkMath.Gnomon.oddGnomon a)
    (hcommon :
      q ∈ squareOffsetPrimeSupport (DkMath.Gnomon.petalMul a b) r ∩
        squareOffsetPrimeSupport (DkMath.Gnomon.petalMul a b + 1)
          (successorThresholdInsert (DkMath.Gnomon.petalMul a b) r)) :
    q ∣ (gnomonPetalTransition a b).numerator := by
  have hsplit :=
    (mem_reindexed_primeSupport_inter_lower_petalMul_iff hr hlow hq).mp hcommon
  rcases hsplit.2 with hFirst | hSecond
  · exact False.elim (hnotFirst hFirst)
  · simpa using hSecond

/-- Avoiding both Petal factors forces exact lower-region support turnover. -/
theorem disjoint_reindexed_primeSupport_lower_petalMul_of_factor_avoid
    {a b r q : ℕ}
    (hr : SquareOffset (DkMath.Gnomon.petalMul a b) r)
    (hlow : r < DkMath.Gnomon.petalMul a b + 1)
    (hq : Nat.Prime q)
    (hnotA : ¬ q ∣ DkMath.Gnomon.oddGnomon a)
    (hnotB : ¬ q ∣ DkMath.Gnomon.oddGnomon b) :
    ¬ (q ∈ squareOffsetPrimeSupport (DkMath.Gnomon.petalMul a b) r ∩
      squareOffsetPrimeSupport (DkMath.Gnomon.petalMul a b + 1)
        (successorThresholdInsert (DkMath.Gnomon.petalMul a b) r)) := by
  intro hcommon
  have hsplit :=
    (mem_reindexed_primeSupport_inter_lower_petalMul_iff hr hlow hq).mp hcommon
  rcases hsplit.2 with hA | hB
  · exact hnotA hA
  · exact hnotB hB

end DkMath.NumberTheory.Legendre

#print axioms DkMath.NumberTheory.Legendre.mem_reindexed_primeSupport_inter_lower_petalMul_iff
#print axioms DkMath.NumberTheory.Legendre.common_lower_dvd_gnomonPetalTransition_numerator_of_not_dvd_first
