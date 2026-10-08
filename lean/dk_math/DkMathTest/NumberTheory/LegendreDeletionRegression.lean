/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.CoarseTownDeletionCapacity
import DkMathTest.NumberTheory.LegendreFullTownRegression

#print "file: DkMathTest.NumberTheory.LegendreDeletionRegression"

namespace DkMathTest.LegendreDeletionRegression

open DkMath.NumberTheory.Legendre
open DkMath.NumberTheory.Primitive
open DkMath.Combinatorics

/-- A collision-free family is retained exactly, including both endpoint conventions. -/
theorem tiny_collision_free :
    supportCollisionDeletionVertices ({1,2,3} : Finset ℕ) (fun _ => (∅ : Finset ℕ)) = ∅ ∧
      supportPackingRemainder ({1,2,3} : Finset ℕ) (fun _ => (∅ : Finset ℕ)) = {1,2,3} := by
  simp [supportCollisionDeletionVertices, supportCollisionEdges, supportPackingRemainder]

/-- Several edges share a deleted endpoint; deleting vertices is strictly cheaper. -/
theorem six_shared_first_endpoints :
    (coarseTownDeletionVertices {3} 6).card = 3 ∧
      (coarseTownSupportCollisionEdges {3} 6).card = 6 ∧
      (coarsePrimeWorldFullTown {3} 6).card = 8 ∧ (primeScalesUpTo 6).card = 3 := by
  rw [coarseTownDeletionVertices_eq_fibers]
  unfold coarseTownSupportCollisionEdges supportCollisionEdges
  simp_rw [squareOffsetPrimeSupport_eq_boundedSquareSupport]
  decide +kernel

theorem six_strict_deletion_vs_edge :
    (primeScalesUpTo 6).card + (coarseTownDeletionVertices {3} 6).card <
      (coarsePrimeWorldFullTown {3} 6).card ∧
      ¬ ((primeScalesUpTo 6).card + (coarseTownSupportCollisionEdges {3} 6).card <
        (coarsePrimeWorldFullTown {3} 6).card) := by
  rw [six_shared_first_endpoints.1, six_shared_first_endpoints.2.1,
    six_shared_first_endpoints.2.2.1, six_shared_first_endpoints.2.2.2]
  decide +kernel

theorem six_prime_via_exact_deletion : ∃ p, p.Prime ∧ SquareCell 6 p :=
  exists_prime_squareCell_of_coarseTown_deletion_deficit {3} (by decide) six_strict_deletion_vs_edge.1

/-- The previous eleven-seat edge endpoint remains the same named proof. -/
theorem eleven_edge_endpoint_preserved : ∃ p, p.Prime ∧ SquareCell 11 p :=
  DkMathTest.LegendreFullTownRegression.eleven_prime_via_existing_packing_consumer

/-- Every seat is in the shell and the family is large enough, but seats 1 and 5 share q=2. -/
theorem invalid_three_certificate :
    (∀ a ∈ ({1,2,4,5} : Finset ℕ), SquareOffset 3 a) ∧
      (primeScalesUpTo 3).card < ({1,2,4,5} : Finset ℕ).card ∧
      checkOldSupportCapacityCertificate 3 {1,2,4,5} = false := by
  unfold SquareOffset
  decide +kernel

theorem invalid_three_certificate_semantic : ¬ OldSupportCapacityCertificate 3 {1,2,4,5} := by
  intro hc
  have ht := (checkOldSupportCapacityCertificate_eq_true_iff 3 {1,2,4,5}).mpr hc
  rw [invalid_three_certificate.2.2] at ht
  contradiction

end DkMathTest.LegendreDeletionRegression
