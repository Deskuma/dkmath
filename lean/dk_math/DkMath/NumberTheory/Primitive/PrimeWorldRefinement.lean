/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic
import DkMath.NumberTheory.Primitive.PeriodicPrimeWorld

#print "file: DkMath.NumberTheory.Primitive.PrimeWorldRefinement"

/-!
## Refinement of a finite prime-direction observer

Inserting one new prime direction refines the old support observer by adding
one new divisibility wave.  An old support-disjoint position therefore
survives exactly when it also avoids the new prime.  For a canonical old
period representative, the children `r + j * M` with `j < q` contain exactly
one position on the new `q`-wave when `q` is fresh and `M` is the old product
modulus.

These are finite observer statements.  A surviving child is still only a
candidate seat; this module makes no primality, Legendre, CRT-provider, or
application-level claim beyond the modular arithmetic used in the proof.
-/

namespace DkMath.NumberTheory.Primitive

open DkMath.NumberTheory.StructuralArithmetic

/-
The semantic observer update is valid even when inserting a direction already
present in the finite world.  The separate modulus theorem below retains the
genuine-freshness hypothesis because it uses `Finset.prod_insert`.
-/

/-- Support disjointness after insertion is old support disjointness plus avoidance of `q`. -/
theorem supportDisjointFrom_insert_prime_iff
    {S : Finset ℕ} {q n : ℕ}
    (hq : Nat.Prime q) :
    SupportDisjointFrom (insert q S) n ↔
      SupportDisjointFrom S n ∧ ¬ q ∣ n := by
  constructor
  · intro hnew
    refine ⟨?_, ?_⟩
    · intro p hp hpn hpS
      exact hnew hp hpn (Finset.mem_insert_of_mem hpS)
    · intro hqn
      exact hnew hq hqn (Finset.mem_insert_self q S)
  · rintro ⟨hold, hqavoid⟩ p hp hpn hpins
    rcases Finset.mem_insert.mp hpins with rfl | hpS
    · exact hqavoid hpn
    · exact hold hp hpn hpS

/-- A genuinely fresh insertion multiplies the finite-world product modulus by `q`. -/
theorem primeWorldModulus_insert
    {S : Finset ℕ} {q : ℕ}
    (hqS : q ∉ S) :
    primeWorldModulus (insert q S) = q * primeWorldModulus S := by
  simp [primeWorldModulus, hqS]

/-- A fresh prime direction is coprime to the product modulus of a certified old world. -/
theorem prime_coprime_primeWorldModulus_of_not_mem
    {S : Finset ℕ} (hS : KnownPrimeScales S)
    {q : ℕ} (hq : Nat.Prime q) (hqS : q ∉ S) :
    Nat.Coprime q (primeWorldModulus S) := by
  apply (supportDisjointFrom_iff_coprime_primeWorldModulus hS).mp
  intro p hp hpd hpS
  have hpq : p = q :=
    ((Nat.dvd_prime hq).mp hpd).resolve_left hp.ne_one
  exact hqS (by simpa [hpq] using hpS)

/-- The child of an old seat `r` with child index `j`. -/
def primeWorldChild (S : Finset ℕ) (r j : ℕ) : ℕ :=
  r + j * primeWorldModulus S

/-- Every child has the same old-world support state as its parent seat. -/
theorem supportDisjointFrom_child_iff
    {S : Finset ℕ} {r j : ℕ} :
    SupportDisjointFrom S (primeWorldChild S r j) ↔
      SupportDisjointFrom S r := by
  exact supportDisjointFrom_add_mul_primeWorldModulus_iff

/-- The refined child criterion combines the semantic update with old periodicity. -/
theorem supportDisjointFrom_insert_prime_child_iff
    {S : Finset ℕ} {q r j : ℕ}
    (hq : Nat.Prime q) :
    SupportDisjointFrom (insert q S) (primeWorldChild S r j) ↔
      SupportDisjointFrom S r ∧
        ¬ q ∣ primeWorldChild S r j := by
  rw [supportDisjointFrom_insert_prime_iff hq,
    supportDisjointFrom_child_iff]

/-
The certified old modulus is positive.  This is needed only to turn the CRT
representative bound into a child-index bound.
-/
private theorem primeWorldModulus_pos
    {S : Finset ℕ} (hS : KnownPrimeScales S) :
    0 < primeWorldModulus S := by
  simpa [primeWorldModulus] using
    (Finset.prod_pos (s := S) (f := fun p : ℕ => p)
      (fun p hp => (hS hp).pos))

/--
Exactly one bounded child of an old-period representative lies on the new
prime wave.

The CRT representative is congruent to `0` modulo `q` and to `r` modulo the
old modulus.  Its bound below `q * M` produces a unique index `j < q` in the
coordinate `r + j * M`.
-/
theorem existsUnique_child_dvd_new_prime
    {S : Finset ℕ} (hS : KnownPrimeScales S)
    {q r : ℕ}
    (hq : Nat.Prime q)
    (hqS : q ∉ S)
    (hr : r < primeWorldModulus S) :
    ∃! j : ℕ,
      j < q ∧
      q ∣ primeWorldChild S r j := by
  let M := primeWorldModulus S
  have hMpos : 0 < M := by
    simpa [M] using primeWorldModulus_pos hS
  have hqcop : Nat.Coprime q M := by
    simpa [M] using prime_coprime_primeWorldModulus_of_not_mem hS hq hqS
  let z : ℕ := Nat.chineseRemainder hqcop 0 r
  have hzlt : z < q * M := by
    simpa [z] using
      (Nat.chineseRemainder_lt_mul hqcop 0 r hq.ne_zero hMpos.ne')
  have hzq : z ≡ 0 [MOD q] := by
    simpa [z] using (Nat.chineseRemainder hqcop 0 r).prop.1
  have hzM : z ≡ r [MOD M] := by
    simpa [z] using (Nat.chineseRemainder hqcop 0 r).prop.2
  have hrM : r < M := by simpa [M] using hr
  have hrz : r ≤ z := by
    apply hzM.symm.le_of_lt_add
    omega
  obtain ⟨j, hzj⟩ := (Nat.modEq_iff_exists_eq_add hrz).mp hzM.symm
  have hzrep : z = r + j * M := by
    simpa [Nat.mul_comm] using hzj
  have hjmul : j * M < q * M := by
    calc
      j * M ≤ r + j * M := Nat.le_add_left _ _
      _ = z := hzrep.symm
      _ < q * M := hzlt
  have hjq : j < q := (Nat.mul_lt_mul_right hMpos).mp hjmul
  have hqdiv : q ∣ z := Nat.modEq_zero_iff_dvd.mp hzq
  have hqchild : q ∣ primeWorldChild S r j := by
    simpa [primeWorldChild, M, hzrep, Nat.mul_comm] using hqdiv
  refine ⟨j, ⟨hjq, hqchild⟩, ?_⟩
  intro i hi
  have hchild : q ∣ primeWorldChild S r i := hi.2
  have hchildren :
      primeWorldChild S r i ≡ primeWorldChild S r j [MOD q] := by
    exact hchild.modEq_zero_nat.trans hqchild.modEq_zero_nat.symm
  have hijM : i * M ≡ j * M [MOD q] := by
    apply (Nat.ModEq.rfl (n := q) (a := r)).add_left_cancel
    simpa [primeWorldChild, M] using hchildren
  have hij : i ≡ j [MOD q] :=
    Nat.ModEq.cancel_right_of_coprime hqcop hijM
  exact hij.eq_of_lt_of_lt hi.1 hjq

/--
For a support-disjoint old seat, the bounded children split into one reserved
child on the new `q`-wave and `q - 1` children that remain support-disjoint in
the enlarged world.
-/
theorem exists_unique_reserved_child_and_other_children_survive
    {S : Finset ℕ} (hS : KnownPrimeScales S)
    {q r : ℕ}
    (hq : Nat.Prime q)
    (hqS : q ∉ S)
    (hrPeriod : r < primeWorldModulus S)
    (hrSeat : SupportDisjointFrom S r) :
    ∃ j0,
      j0 < q ∧
      q ∣ primeWorldChild S r j0 ∧
      ∀ j, j < q → j ≠ j0 →
        SupportDisjointFrom (insert q S) (primeWorldChild S r j) := by
  obtain ⟨j0, hj0, hj0uniq⟩ :=
    existsUnique_child_dvd_new_prime hS hq hqS hrPeriod
  refine ⟨j0, hj0.1, hj0.2, ?_⟩
  intro j hj hjne
  apply (supportDisjointFrom_insert_prime_child_iff hq).2
  refine ⟨hrSeat, ?_⟩
  intro hjdvd
  exact hjne (hj0uniq j ⟨hj, hjdvd⟩)

end DkMath.NumberTheory.Primitive
