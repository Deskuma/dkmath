/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMathTest.NumberTheory.LegendreDeletion1031Calibration

#print "file: DkMathTest.NumberTheory.LegendreDeletion1031Strictness"

namespace DkMathTest.LegendreDeletion1031Strictness

open DkMath.NumberTheory.Legendre
open DkMath.NumberTheory.Primitive
open DkMathTest.LegendreDeletion1031Data
open DkMathTest.LegendreDeletion1031Calibration

set_option maxRecDepth 100000

private theorem actualFiber_eq_arithmetic (S : Finset ℕ) (n q : ℕ)
    (hp : q.Prime) (hle : q ≤ n) :
    coarseFullTownPrimeFiber S n q = oldSupportSeatFiber n (coarsePrimeWorldFullTown S n) q := by
  ext a
  simp only [coarseFullTownPrimeFiber, oldSupportSeatFiber, Finset.mem_filter,
    mem_squareOffsetPrimeSupport, hp, hle, true_and]

private theorem primeEdges_subset_actual (S : Finset ℕ) (n q : ℕ) :
    coarseTownPrimeCollisionEdges S n q ⊆ coarseTownSupportCollisionEdges S n := by
  rintro ⟨a,b⟩ hab
  obtain ⟨ha,hb,hlt⟩ := mem_coarseTownPrimeCollisionEdges.mp hab
  have ha' := Finset.mem_filter.mp ha
  have hb' := Finset.mem_filter.mp hb
  refine mem_coarseTownSupportCollisionEdges.mpr ⟨ha'.1,hb'.1,hlt,?_⟩
  intro hdisj
  exact Finset.disjoint_left.mp hdisj ha'.2 hb'.2

/-- A single old-prime fiber already gives enough edges to refute the weaker test. -/
theorem fiber11_card1031 :
    (coarseFullTownPrimeFiber (primeScalesUpTo 10) 1031 11).card = 39 := by
  rw [actualFiber_eq_arithmetic _ _ _ (by norm_num) (by omega)]
  unfold oldSupportSeatFiber
  rw [town1031Seats_eq_production]
  decide +kernel

/-- The strict deletion improvement at the large anchor is kernel-proved without counting all edges. -/
theorem strict_deletion_vs_edge1031 :
    (primeScalesUpTo 1031).card + (coarseTownDeletionVertices (primeScalesUpTo 10) 1031).card <
      (coarsePrimeWorldFullTown (primeScalesUpTo 10) 1031).card ∧
      ¬ ((primeScalesUpTo 1031).card + (coarseTownSupportCollisionEdges (primeScalesUpTo 10) 1031).card <
        (coarsePrimeWorldFullTown (primeScalesUpTo 10) 1031).card) := by
  have hl := Finset.card_le_card (primeEdges_subset_actual (primeScalesUpTo 10) 1031 11)
  rw [card_coarseTownPrimeCollisionEdges, fiber11_card1031,
    show Nat.choose 39 2 = 741 by decide +kernel] at hl
  rw [oldPrimes1031_card_checked, deletion1031_symbolic_card,
    DkMathTest.LegendreFullTownRegression.large_anchor_grid.2.2]
  omega

end DkMathTest.LegendreDeletion1031Strictness
