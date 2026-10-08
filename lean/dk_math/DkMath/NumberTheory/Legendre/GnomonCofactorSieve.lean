/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.GnomonCofactorWindow
import DkMath.NumberTheory.PrimorialUniverse.WheelSurvivor

#print "file: DkMath.NumberTheory.Legendre.GnomonCofactorSieve"

/-! Reduced-residue cofactor windows give a finite weighted sieve envelope.
The exact surviving-composite error is exposed, not estimated by a prime oracle. -/

namespace DkMath.NumberTheory.Legendre

open DkMath.NumberTheory.PrimorialUniverse
open scoped BigOperators

/-- Actual integers in the quotient window surviving the existing finite wheel. -/
def gnomonCofactorSieveCandidates (n k : ℕ) (S : Finset ℕ) : Finset ℕ :=
  (Finset.Icc (max (n ^ 2 / k) (2 * n) + 1) ((n ^ 2 + 2 * n) / k)).filter
    (fun q => Nat.Coprime q (finitePrimeBasisProduct S))

/-- Thin bridge to the repository's finite prime-basis reservation predicate. -/
theorem mem_gnomonCofactorSieveCandidates_iff {n k q : ℕ} {S : Finset ℕ}
    (hS : IsFinitePrimeBasis S) :
    q ∈ gnomonCofactorSieveCandidates n k S ↔
      max (n ^ 2 / k) (2 * n) < q ∧ q ≤ (n ^ 2 + 2 * n) / k ∧
        ¬ ReservedByPrimeBasis S q := by
  simp only [gnomonCofactorSieveCandidates, Finset.mem_filter, Finset.mem_Icc,
    Nat.add_one_le_iff, ← not_reserved_iff_coprime_finitePrimeBasisProduct hS q]
  tauto

/-- Basis primes below the width delete no prime in any cofactor window. -/
theorem gnomonCofactorSieveCandidates_prime_filter {n k : ℕ} {S : Finset ℕ}
    (hS : IsFinitePrimeBasis S) (hbound : ∀ q ∈ S, q ≤ 2 * n) :
    (gnomonCofactorSieveCandidates n k S).filter Nat.Prime =
      gnomonCofactorWindowPrimes n k := by
  ext p
  constructor
  · intro hp
    obtain ⟨hc, hprime⟩ := Finset.mem_filter.mp hp
    obtain ⟨hA, hB, _⟩ := (mem_gnomonCofactorSieveCandidates_iff hS).mp hc
    exact mem_gnomonCofactorWindowPrimes.mpr ⟨hprime,
      (le_max_right _ _).trans_lt hA, (le_max_left _ _).trans_lt hA, hB⟩
  · intro hp
    obtain ⟨hprime, hw, hlo, hhi⟩ := mem_gnomonCofactorWindowPrimes.mp hp
    have hcop : Nat.Coprime p (finitePrimeBasisProduct S) := by
      unfold finitePrimeBasisProduct
      rw [Nat.coprime_prod_right_iff]
      intro q hq
      apply (Nat.coprime_primes hprime (hS q hq)).mpr
      have hb := hbound q hq
      omega
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨by have ha := max_lt hlo hw; omega, hhi⟩, hcop⟩, hprime⟩

/-- Uncapped weight; no primality or carry predicate occurs in this definition. -/
noncomputable def gnomonCofactorSieveMass (n : ℕ) (S : Finset ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 2 (n - 1),
    ∑ q ∈ gnomonCofactorSieveCandidates n k S, Real.log (q : ℝ)

/-- Exact error for auditing: surviving composite slots, weighted by log(q). -/
noncomputable def gnomonCofactorSieveCompositeError (n : ℕ) (S : Finset ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 2 (n - 1),
    ∑ q ∈ (gnomonCofactorSieveCandidates n k S).filter (fun q => ¬ q.Prime),
      Real.log (q : ℝ)

theorem gnomonCofactorSieveCompositeError_nonneg (n : ℕ) (S : Finset ℕ) :
    0 ≤ gnomonCofactorSieveCompositeError n S := by
  apply Finset.sum_nonneg
  intro k _
  apply Finset.sum_nonneg
  intro q hq
  have h := Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1
  exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ q by omega))

/-- The accumulated sieve loss is exactly its surviving nonprime log weight. -/
theorem gnomonCofactorSieveMass_eq_window_add_error {n : ℕ} {S : Finset ℕ}
    (hS : IsFinitePrimeBasis S) (hbound : ∀ q ∈ S, q ≤ 2 * n) :
    gnomonCofactorSieveMass n S = gnomonCofactorWindowMass n +
      gnomonCofactorSieveCompositeError n S := by
  unfold gnomonCofactorSieveMass gnomonCofactorWindowMass gnomonCofactorSieveCompositeError
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [← gnomonCofactorSieveCandidates_prime_filter hS hbound]
  exact (Finset.sum_filter_add_sum_filter_not _ Nat.Prime _).symm

/-- Preserve the previous envelope whenever a chosen sieve is too coarse. -/
noncomputable def gnomonCofactorSieveBudget (n : ℕ) (S : Finset ℕ) : ℝ :=
  min (gnomonCofactorGeometricBudget n) (gnomonCofactorSieveMass n S)

theorem gnomonCofactorWindowMass_le_sieveBudget {n : ℕ} {S : Finset ℕ} (hn : 3 ≤ n)
    (hS : IsFinitePrimeBasis S) (hbound : ∀ q ∈ S, q ≤ 2 * n) :
    gnomonCofactorWindowMass n ≤ gnomonCofactorSieveBudget n S := by
  apply le_min (gnomonCofactorWindowMass_le_geometricBudget hn)
  rw [gnomonCofactorSieveMass_eq_window_add_error hS hbound]
  have h := gnomonCofactorSieveCompositeError_nonneg n S
  linarith

theorem gnomonCofactorSieveBudget_le_geometricBudget (n : ℕ) (S : Finset ℕ) :
    gnomonCofactorSieveBudget n S ≤ gnomonCofactorGeometricBudget n := min_le_left _ _

/-- Exact remaining error after capping by the previous independent envelope. -/
theorem gnomonCofactorSieveBudget_excess {n : ℕ} {S : Finset ℕ}
    (hS : IsFinitePrimeBasis S) (hbound : ∀ q ∈ S, q ≤ 2 * n) :
    gnomonCofactorSieveBudget n S - gnomonCofactorWindowMass n =
      min (gnomonCofactorGeometricBudget n - gnomonCofactorWindowMass n)
        (gnomonCofactorSieveCompositeError n S) := by
  unfold gnomonCofactorSieveBudget
  rw [gnomonCofactorSieveMass_eq_window_add_error hS hbound, ← min_sub_sub_right]
  congr 1
  ring

/-- Substitution preserves every small, repeated-power and higher residual. -/
theorem gnomonPascalOldLogBudget_sieve_excess {n : ℕ} (hn : 3 ≤ n) (S : Finset ℕ) :
    gnomonPascalSmallCarryMass n + gnomonRepeatedCarryMass n +
      gnomonCofactorSieveBudget n S + gnomonPascalShellHigherPrimePowerMass n =
    gnomonPascalOldLogBudget n +
      (gnomonCofactorSieveBudget n S - gnomonCofactorWindowMass n) := by
  have h := gnomonPascalOldLogBudget_cofactor_excess hn
  linarith

/-- A finite weighted sieve supplies a conditional singleton-budget consumer. -/
theorem exists_prime_squareCell_of_cofactorSieveBudget_lt {n : ℕ} {S : Finset ℕ}
    (hn : 3 ≤ n) (hS : IsFinitePrimeBasis S) (hbound : ∀ q ∈ S, q ≤ 2 * n)
    (hstrict : gnomonPascalSmallCarryMass n + gnomonRepeatedCarryMass n +
      gnomonCofactorSieveBudget n S + gnomonPascalShellHigherPrimePowerMass n <
        Real.log (GnomonPascalCell n : ℝ)) :
    ∃ p, p.Prime ∧ SquareCell n p := by
  apply (gnomonPascalOldLogBudget_lt_iff hn).mp
  have hbound' := gnomonCofactorWindowMass_le_sieveBudget hn hS hbound
  rw [gnomonPascalOldLogBudget_sieve_excess hn S] at hstrict
  linarith

end DkMath.NumberTheory.Legendre
