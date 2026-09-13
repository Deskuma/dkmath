/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/
import DkMath.NumberTheory.Goldbach.PrimeWorld
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Data.Fintype.BigOperators

#print "file: DkMath.NumberTheory.Goldbach.Cardinality"

/-!
# Exact cardinality of a complete paired prime period

CRT gives a bijection with the product of the local avoiding sets. The exact
cardinality is `∏ r∈S, (r - if r ∣ 2*n then 1 else 2)` and is always positive
for a certified finite prime world. This statement concerns a whole product
period; it contains no bound placing the witness below the center.
-/

namespace DkMath.NumberTheory

open Primitive StructuralArithmetic
open scoped BigOperators

/-- Full-period paired cardinality, obtained from a CRT bijection of the actual residue sets. -/
theorem goldbach_card_primeWorld (n : ℕ) (W : GoldbachPrimeWorld) :
    (goldbachPrimeWorldResidues n W.primes).card =
      ∏ r ∈ W.primes, (r - if r ∣ 2 * n then 1 else 2) := by
  classical
  letI (r : W.primes) : NeZero (r : ℕ) := ⟨(W.isPrime r.property).ne_zero⟩
  let T := Fintype.piFinset (fun r : W.primes => goldbachLocalResidues n (r : ℕ))
  have hc : Pairwise (fun p q : W.primes => Nat.Coprime (p : ℕ) (q : ℕ)) := by
    intro p q hne
    apply (Nat.coprime_primes (W.isPrime p.property) (W.isPrime q.property)).mpr
    exact fun he => hne (Subtype.ext he)
  let M := ∏ r : W.primes, (r : ℕ)
  have hM : M = primeWorldModulus W.primes :=
    Finset.prod_coe_sort W.primes (fun r : ℕ => r)
  let e := ZMod.prodEquivPi (fun r : W.primes => (r : ℕ)) hc
  have hcast (u : ℕ) : e (u : ZMod M) = fun r : W.primes => (u : ZMod (r : ℕ)) :=
    map_natCast e u
  have hcard : (goldbachPrimeWorldResidues n W.primes).card = T.card := by
    apply Finset.card_bij (s := goldbachPrimeWorldResidues n W.primes) (t := T)
      (fun (u : ℕ) _ (r : W.primes) => (u : ZMod (r : ℕ)))
    · intro u hu
      apply Fintype.mem_piFinset.mpr
      intro r
      have hs := (mem_goldbachPrimeWorldResidues.mp hu).2 r r.property
      simpa [goldbachLocalResidues] using hs
    · intro u hu v hv heq
      have hzeq : (u : ZMod M) = (v : ZMod M) := e.injective (by
        rw [hcast, hcast]
        exact heq)
      have hmod := (ZMod.natCast_eq_natCast_iff u v M).mp hzeq
      exact hmod.eq_of_lt_of_lt
        (by simpa [hM] using (mem_goldbachPrimeWorldResidues.mp hu).1)
        (by simpa [hM] using (mem_goldbachPrimeWorldResidues.mp hv).1)
    · intro f hf
      let a : ℕ → ℕ := fun r => if hr : r ∈ W.primes then (f ⟨r, hr⟩).val else 0
      obtain ⟨u, hu, hlocal⟩ := goldbach_primeWorld_crt W a
      have hcoord (r : W.primes) : (u : ZMod (r : ℕ)) = f r := by
        simpa [a, r.property, ZMod.natCast_zmod_val] using hlocal r r.property
      have humem : u ∈ goldbachPrimeWorldResidues n W.primes := by
        refine mem_goldbachPrimeWorldResidues.mpr ⟨hu, ?_⟩
        intro r hr
        rw [hcoord ⟨r, hr⟩]
        have h := Fintype.mem_piFinset.mp hf ⟨r, hr⟩
        simpa [goldbachLocalResidues] using h
      exact ⟨u, humem, funext hcoord⟩
  rw [hcard]
  simp only [T, Fintype.card_piFinset, goldbach_card_local]
  exact Finset.prod_coe_sort W.primes (fun r => r - if r ∣ 2 * n then 1 else 2)

/-- Every prime direction leaves at least one residue: parity removes only one class. -/
theorem goldbach_local_capacity_pos (n : ℕ) {r : ℕ} (hr : Nat.Prime r) :
    0 < r - (if r ∣ 2 * n then 1 else 2) := by
  have hr2 := hr.two_le
  by_cases hd : r ∣ 2 * n
  · rw [if_pos hd]
    omega
  · rw [if_neg hd]
    have hne : r ≠ 2 := by
      intro he
      subst r
      exact hd (dvd_mul_right 2 n)
    omega

/-- Every certified prime world has a raw paired survivor somewhere in its full period. -/
theorem goldbach_primeWorld_nonempty (n : ℕ) (W : GoldbachPrimeWorld) :
    (goldbachPrimeWorldResidues n W.primes).Nonempty := by
  rw [← Finset.card_pos, goldbach_card_primeWorld]
  exact Finset.prod_pos (fun r hr => goldbach_local_capacity_pos n (W.isPrime hr))

/-- A fresh-prime refinement multiplies full-period capacity by its exact local capacity. -/
theorem goldbach_card_primeWorld_insert (n : ℕ) (W : GoldbachPrimeWorld)
    {q : ℕ} (hq : Nat.Prime q) (hqS : q ∉ W.primes) :
    (goldbachPrimeWorldResidues n (insert q W.primes)).card =
      (goldbachPrimeWorldResidues n W.primes).card *
        (q - if q ∣ 2 * n then 1 else 2) := by
  let W' : GoldbachPrimeWorld := ⟨insert q W.primes, by
    intro r hr
    rcases Finset.mem_insert.mp hr with he | hr
    · exact he ▸ hq
    · exact W.isPrime hr⟩
  have h := goldbach_card_primeWorld n W'
  change (goldbachPrimeWorldResidues n (insert q W.primes)).card = _ at h
  rw [h, goldbach_card_primeWorld, Finset.prod_insert hqS]
  exact Nat.mul_comm _ _

/-- The paired counterpart of the familiar 30-wheel uses the existing product-period construction. -/
def goldbachPairedPHZ30 (n : ℕ) : Finset ℕ := goldbachPrimeWorldResidues n {2, 3, 5}

end DkMath.NumberTheory
