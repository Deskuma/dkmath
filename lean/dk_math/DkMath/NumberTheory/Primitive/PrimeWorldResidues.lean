/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic
import DkMath.NumberTheory.Primitive.PrimeWorldRefinement

#print "file: DkMath.NumberTheory.Primitive.PrimeWorldResidues"

/-!
## Canonical residue spaces of finite prime worlds

`primeWorldResidues S` is the finite reduced-residue space in one period of
the product modulus of `S`.  For a certified prime world it is exactly the
bounded support-disjoint part of that period.  A fresh-prime refinement is
proved here to be an equality with the canonical residue space of the enlarged
world, using Euclidean parent/index coordinates rather than a cardinality
argument or Euler's totient function.

These are finite divisibility-support statements.  Membership in a residue
space is not a primality assertion.
-/

namespace DkMath.NumberTheory.Primitive

open DkMath.NumberTheory.StructuralArithmetic

/-- The canonical reduced-residue space in one finite-world period. -/
def primeWorldResidues (S : Finset ℕ) : Finset ℕ :=
  (Finset.range (primeWorldModulus S)).filter
    (fun n => Nat.Coprime n (primeWorldModulus S))

/-- Membership exposes the canonical period bound and coprimality condition. -/
@[simp] theorem mem_primeWorldResidues
    {S : Finset ℕ} {n : ℕ} :
    n ∈ primeWorldResidues S ↔
      n < primeWorldModulus S ∧
      Nat.Coprime n (primeWorldModulus S) := by
  simp [primeWorldResidues]

/-- Certified worlds identify canonical residues with bounded support-disjoint seats. -/
theorem mem_primeWorldResidues_iff_supportDisjointFrom
    {S : Finset ℕ} (hS : KnownPrimeScales S) {n : ℕ} :
    n ∈ primeWorldResidues S ↔
      n < primeWorldModulus S ∧
      SupportDisjointFrom S n := by
  rw [mem_primeWorldResidues, supportDisjointFrom_iff_coprime_primeWorldModulus hS]

/-- A canonical residue is below the old product modulus. -/
theorem lt_primeWorldModulus_of_mem_primeWorldResidues
    {S : Finset ℕ} {n : ℕ} (hn : n ∈ primeWorldResidues S) :
    n < primeWorldModulus S :=
  (mem_primeWorldResidues.mp hn).1

/-- A canonical residue is support-disjoint in a certified old world. -/
theorem supportDisjointFrom_of_mem_primeWorldResidues
    {S : Finset ℕ} (hS : KnownPrimeScales S)
    {n : ℕ} (hn : n ∈ primeWorldResidues S) :
    SupportDisjointFrom S n :=
  (mem_primeWorldResidues_iff_supportDisjointFrom hS).mp hn |>.2

private theorem primeWorldModulus_pos_of_knownPrimeScales
    {S : Finset ℕ} (hS : KnownPrimeScales S) :
    0 < primeWorldModulus S := by
  simpa [primeWorldModulus] using
    (Finset.prod_pos (s := S) (f := fun p : ℕ => p)
      (fun p hp => (hS hp).pos))

/-
Euclidean division supplies canonical parent and child-index coordinates.

For `M = primeWorldModulus S`, the coordinates are `r = n % M` and
`j = n / M`.  The hypothesis bounds the quotient by the fresh-prime index
range; no primality assumption on `q` is needed for this arithmetic fact.
-/
theorem exists_primeWorldChild_coordinates_of_lt_mul_modulus
    {S : Finset ℕ} (hS : KnownPrimeScales S)
    {q n : ℕ}
    (hn : n < q * primeWorldModulus S) :
    ∃ r j,
      r < primeWorldModulus S ∧
      j < q ∧
      n = primeWorldChild S r j := by
  let M := primeWorldModulus S
  have hMpos : 0 < M := by
    simpa [M] using primeWorldModulus_pos_of_knownPrimeScales hS
  let r := n % M
  let j := n / M
  have hr : r < M := by
    simpa [r] using Nat.mod_lt n hMpos
  have hj : j < q := by
    apply (Nat.div_lt_iff_lt_mul hMpos).2
    simpa [j, M] using hn
  have hnrep : n = r + j * M := by
    simpa [r, j, M, Nat.mul_comm] using (Nat.mod_add_div n M).symm
  exact ⟨r, j, by simpa [M] using hr, hj, by simpa [primeWorldChild, M] using hnrep⟩

/-- Every refined seat lies below the enlarged product modulus. -/
theorem lt_insert_modulus_of_mem_refinedSurvivingSeats
    {S : Finset ℕ} (hS : KnownPrimeScales S)
    {q : ℕ} {R : Finset ℕ}
    (_hq : Nat.Prime q)
    (hqS : q ∉ S)
    (hR : ∀ r ∈ R, r < primeWorldModulus S)
    {n : ℕ}
    (hn : n ∈ refinedSurvivingSeats S q R) :
    n < primeWorldModulus (insert q S) := by
  rcases Finset.mem_image.mp hn with ⟨pair, hp, rfl⟩
  rcases pair with ⟨r, j⟩
  have hp' := mem_survivingChildPairs_iff.mp hp
  have hr : r < primeWorldModulus S := hR r hp'.1
  have hj : j < q := hp'.2.1
  have hMpos : 0 < primeWorldModulus S :=
    primeWorldModulus_pos_of_knownPrimeScales hS
  have hsmall : r + j * primeWorldModulus S <
      primeWorldModulus S + j * primeWorldModulus S :=
    Nat.add_lt_add_right hr (j * primeWorldModulus S)
  have hsucc : j + 1 ≤ q := Nat.succ_le_of_lt hj
  have hmul : (j + 1) * primeWorldModulus S ≤
      q * primeWorldModulus S :=
    Nat.mul_le_mul_right _ hsucc
  calc
    primeWorldChild S r j = r + j * primeWorldModulus S := by rfl
    _ < primeWorldModulus S + j * primeWorldModulus S := hsmall
    _ = (j + 1) * primeWorldModulus S := by ring
    _ ≤ q * primeWorldModulus S := hmul
    _ = primeWorldModulus (insert q S) :=
      (primeWorldModulus_insert hqS).symm

/-
The canonical refinement has exactly the bounded support-disjoint semantics
of the enlarged world.

The reverse implication explicitly uses `n % M` and `n / M` as the parent and
child coordinates, then places that pair in the refined image.  No counting
or cardinality argument is used to obtain the reverse inclusion.
-/
theorem mem_refined_primeWorldResidues_iff
    {S : Finset ℕ} (hS : KnownPrimeScales S)
    {q n : ℕ}
    (hq : Nat.Prime q)
    (hqS : q ∉ S) :
    n ∈ refinedSurvivingSeats S q (primeWorldResidues S) ↔
      n < primeWorldModulus (insert q S) ∧
      SupportDisjointFrom (insert q S) n := by
  constructor
  · intro hn
    exact ⟨lt_insert_modulus_of_mem_refinedSurvivingSeats hS hq hqS
      (fun r hr => lt_primeWorldModulus_of_mem_primeWorldResidues hr) hn,
      supportDisjointFrom_of_mem_refinedSurvivingSeats hq
        (fun r hr => supportDisjointFrom_of_mem_primeWorldResidues hS hr) hn⟩
  · rintro ⟨hnlt, hnew⟩
    have hnlt' : n < q * primeWorldModulus S := by
      simpa [primeWorldModulus_insert hqS] using hnlt
    obtain ⟨r, j, hr, hj, hnrep⟩ :=
      exists_primeWorldChild_coordinates_of_lt_mul_modulus hS hnlt'
    have hsplit := (supportDisjointFrom_insert_prime_iff hq).mp hnew
    have hchild : SupportDisjointFrom S (primeWorldChild S r j) := by
      simpa [hnrep] using hsplit.1
    have hrseat : SupportDisjointFrom S r :=
      (supportDisjointFrom_add_mul_primeWorldModulus_iff (S := S)
        (m := r) (k := j)).mp hchild
    have hrmem : r ∈ primeWorldResidues S :=
      (mem_primeWorldResidues_iff_supportDisjointFrom hS).mpr ⟨hr, hrseat⟩
    have havoid : ¬ q ∣ primeWorldChild S r j := by
      intro hdiv
      apply hsplit.2
      simpa [hnrep] using hdiv
    have hpairs : (r, j) ∈ survivingChildPairs S q (primeWorldResidues S) :=
      mem_survivingChildPairs_iff.mpr ⟨hrmem, hj, havoid⟩
    exact Finset.mem_image.mpr ⟨(r, j), hpairs, hnrep.symm⟩

/-- The refined canonical old residue space equals the canonical new one. -/
theorem refinedSurvivingSeats_primeWorldResidues_eq
    {S : Finset ℕ} (hS : KnownPrimeScales S)
    {q : ℕ}
    (hq : Nat.Prime q)
    (hqS : q ∉ S) :
    refinedSurvivingSeats S q (primeWorldResidues S) =
      primeWorldResidues (insert q S) := by
  ext n
  rw [mem_refined_primeWorldResidues_iff hS hq hqS,
    mem_primeWorldResidues_iff_supportDisjointFrom
      (knownPrimeScales_insert hS hq)]

/-- The canonical residue cardinality obeys the fresh-prime refinement recurrence. -/
theorem card_primeWorldResidues_insert
    {S : Finset ℕ} (hS : KnownPrimeScales S)
    {q : ℕ}
    (hq : Nat.Prime q)
    (hqS : q ∉ S) :
    (primeWorldResidues (insert q S)).card =
      (primeWorldResidues S).card * (q - 1) := by
  rw [← refinedSurvivingSeats_primeWorldResidues_eq hS hq hqS]
  apply card_refinedSurvivingSeats hS hq hqS
  intro r hr
  exact lt_primeWorldModulus_of_mem_primeWorldResidues hr

end DkMath.NumberTheory.Primitive
