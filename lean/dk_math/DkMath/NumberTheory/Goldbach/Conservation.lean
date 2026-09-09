/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/
import DkMath.NumberTheory.Goldbach.PrimeWorld
import DkMath.NumberTheory.Primitive.PrimitiveConservationKernel

#print "file: DkMath.NumberTheory.Goldbach.Conservation"

/-!
# Connection to the existing Primitive Conservation Kernel

Each endpoint lies below the next square after `sqrt (2*n)`. The existing
kernel therefore classifies it as old-generated or old-times-one-fresh.
This is a pointwise classification: its old-generated branch can contain a
composite, and it supplies no simultaneous escape seat. The bridge below
states exactly this classification and the existing support-based closure.
-/

namespace DkMath.NumberTheory

open Primitive StructuralArithmetic

/-- Exact identification of the square-root cutoff with the existing complete prime world. -/
theorem goldbachSmallPrimes_eq_primeScalesUpTo (n : ℕ) :
    goldbachSmallPrimes n = primeScalesUpTo (Nat.sqrt (2 * n)) := by
  ext r
  simp [Nat.le_sqrt']

/-- The entire endpoint interval lies in the square Body at its square-root anchor. -/
theorem goldbach_endpoint_le_squareBody {n m : ℕ} (hm : m ≤ 2 * n) :
    m ≤ squareBody (Nat.sqrt (2 * n)) := by
  have h := Nat.sqrt_le_add (2 * n)
  unfold squareBody
  nlinarith

/-- The exact pointwise old/fresh decomposition exported by the existing kernel. -/
def GoldbachEndpointDecomposition (P m : ℕ) : Prop :=
  PrimeScaleGeneratedBy (primeScalesUpTo P) m ∨
    ∃ p k, Nat.Prime p ∧ P < p ∧ 0 < k ∧ k ≤ P ∧
      FreshPrimeDirection (primeScalesUpTo P) m p ∧ p * k = m ∧
      PrimeScaleGeneratedBy (primeScalesUpTo P) k ∧ Nat.Coprime p k ∧
      (∀ ⦃r : ℕ⦄, FreshPrimeDirection (primeScalesUpTo P) m r → r = p)

/-- Applying the actual PCK theorem to any positive endpoint below `2*n`. -/
theorem goldbach_endpoint_primitive_dichotomy {n m : ℕ}
    (hm : 0 < m) (hbound : m ≤ 2 * n) :
    GoldbachEndpointDecomposition (Nat.sqrt (2 * n)) m :=
  primitiveConservationKernel_dichotomy_of_le_fine_squareBody le_rfl hm
    (goldbach_endpoint_le_squareBody hbound)

/-- Both endpoints receive a PCK decomposition; neither branch is forced to be fresh. -/
theorem goldbach_paired_primitive_dichotomy {n u : ℕ}
    (hu : u ∈ goldbachOffsets n) :
    GoldbachEndpointDecomposition (Nat.sqrt (2 * n)) (n - u) ∧
      GoldbachEndpointDecomposition (Nat.sqrt (2 * n)) (n + u) := by
  have hb := goldbachOffset_bounds hu
  exact ⟨goldbach_endpoint_primitive_dichotomy (by omega) hb.2.2.2.1,
    goldbach_endpoint_primitive_dichotomy (by omega) hb.2.2.2.2⟩

/-- Existing square-world support closure proves both primes when simultaneous escape is supplied. -/
theorem goldbach_prime_pair_of_square_support {n u : ℕ}
    (hu : u ∈ goldbachOffsets n)
    (hl : SupportDisjointFrom (goldbachSmallPrimes n) (n - u))
    (hr : SupportDisjointFrom (goldbachSmallPrimes n) (n + u)) :
    Nat.Prime (n - u) ∧ Nat.Prime (n + u) := by
  have hb := goldbachOffset_bounds hu
  rw [goldbachSmallPrimes_eq_primeScalesUpTo] at hl hr
  exact ⟨prime_of_supportDisjointFrom_primeScalesUpTo_le_squareBody
      (by omega) (goldbach_endpoint_le_squareBody hb.2.2.2.1) hl,
    prime_of_supportDisjointFrom_primeScalesUpTo_le_squareBody
      (by omega) (goldbach_endpoint_le_squareBody hb.2.2.2.2) hr⟩

/-- A support-escape witness in the actual interval yields the fixed-center GN endpoint. -/
theorem goldbachGNFiberAt_of_square_support {n u : ℕ}
    (hu : u ∈ goldbachOffsets n)
    (hl : SupportDisjointFrom (goldbachSmallPrimes n) (n - u))
    (hr : SupportDisjointFrom (goldbachSmallPrimes n) (n + u)) : GoldbachGNFiberAt n :=
  (goldbachPairAt_iff_gnFiberAt n).mp
    ((goldbachPairAt_iff_exists_offset n).mpr
      ⟨u, hu, goldbach_prime_pair_of_square_support hu hl hr⟩)

end DkMath.NumberTheory
