/-
Copyright (c) 2026 DkMath contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.NumberTheory.Goldbach.BalancedPascalOverlap
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sigma
import Mathlib.Tactic

#print "file: DkMath.NumberTheory.Goldbach.BalancedCRTOverlap"

/-!
# Balanced-window CRT overlap

This file records the bounded, left-oriented CRT witnesses used by the
balanced Pascal ledger.  Pair witnesses are counted only when their canonical
residue is in the chosen window.  The triple side is an executable arithmetic
upper-candidate: its progression estimate is local to a finite list of
strictly ordered prime triples.  No universal survivor or Strong Goldbach
provider is asserted here.
-/

namespace DkMath.NumberTheory

open DkMath.NumberTheory.Primitive
open DkMath.NumberTheory.StructuralArithmetic
open scoped BigOperators

/-- The canonical left residue for an unordered pair `p < q`. -/
def goldbachLeftPairWitness (n p q : ℕ) : ℕ := n % (p * q)

/-- The canonical left residue for a strictly ordered triple `p < q < r`. -/
def goldbachTripleWitness (n p q r : ℕ) : ℕ := n % (p * q * r)

private theorem dvd_sub_mod (n m : ℕ) (_hm : 0 < m) : m ∣ n - n % m := by
  refine ⟨n / m, ?_⟩
  have hn : n = n % m + m * (n / m) := (Nat.mod_add_div n m).symm
  calc
    n - n % m = (n % m + m * (n / m)) - n % m :=
      congrArg (fun x => x - n % m) hn
    _ = m * (n / m) := by omega

theorem goldbachLeftPairWitness_dvd_left
    {n p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q) :
    p ∣ n - goldbachLeftPairWitness n p q ∧
      q ∣ n - goldbachLeftPairWitness n p q := by
  have hprod : p * q ∣ n - n % (p * q) :=
    dvd_sub_mod n (p * q) (Nat.mul_pos hp.pos hq.pos)
  constructor
  · exact dvd_trans ⟨q, rfl⟩ hprod
  · exact dvd_trans ⟨p, by simp [mul_comm]⟩ hprod

theorem goldbachTripleWitness_dvd_left
    {n p q r : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hr : Nat.Prime r) :
    p ∣ n - goldbachTripleWitness n p q r ∧
      q ∣ n - goldbachTripleWitness n p q r ∧
      r ∣ n - goldbachTripleWitness n p q r := by
  have hprod : p * q * r ∣ n - n % (p * q * r) :=
    dvd_sub_mod n (p * q * r)
      (Nat.mul_pos (Nat.mul_pos hp.pos hq.pos) hr.pos)
  constructor
  · exact dvd_trans ⟨q * r, by ring⟩ hprod
  constructor
  · exact dvd_trans ⟨p * r, by ring⟩ hprod
  · exact dvd_trans ⟨p * q, by ring⟩ hprod

/-! ## Pair seats and the lower ledger -/

/-- Strictly ordered pairs whose canonical left witness is in the window. -/
def goldbachWindowEligibleLeftPairs (n w : ℕ) (S : Finset ℕ) :
    Finset (ℕ × ℕ) :=
  (S.product S).filter (fun pair =>
    pair.1 < pair.2 ∧
      goldbachLeftPairWitness n pair.1 pair.2 ∈ goldbachBalancedOffsets n w)

@[simp] theorem mem_goldbachWindowEligibleLeftPairs
    {n w p q : ℕ} {S : Finset ℕ} :
    (p, q) ∈ goldbachWindowEligibleLeftPairs n w S ↔
      p ∈ S ∧ q ∈ S ∧ p < q ∧
        goldbachLeftPairWitness n p q ∈ goldbachBalancedOffsets n w := by
  simp [goldbachWindowEligibleLeftPairs, and_assoc]

theorem goldbachWindowEligibleLeftPair_support
    {n w P : ℕ} {S : Finset ℕ} {p q : ℕ}
    (hS : KnownPrimeScales S) (hbound : ∀ ⦃r : ℕ⦄, r ∈ S → r ≤ P)
    (_hw : w ≤ n) (hanchor : P < n - w)
    (hpq : (p, q) ∈ goldbachWindowEligibleLeftPairs n w S) :
    p ∈ goldbachObstructionSupportIn n (goldbachLeftPairWitness n p q) S ∧
      q ∈ goldbachObstructionSupportIn n (goldbachLeftPairWitness n p q) S := by
  have hpS := (mem_goldbachWindowEligibleLeftPairs.mp hpq).1
  have hqS := (mem_goldbachWindowEligibleLeftPairs.mp hpq).2.1
  have ht := (mem_goldbachWindowEligibleLeftPairs.mp hpq).2.2.2
  have htw := (mem_goldbachBalancedOffsets.mp ht).2
  have hpqprime : Nat.Prime p ∧ Nat.Prime q :=
    ⟨hS hpS, hS hqS⟩
  have hdvd := goldbachLeftPairWitness_dvd_left (n := n) hpqprime.1 hpqprime.2
  have hproper : p < n - goldbachLeftPairWitness n p q ∧
      q < n - goldbachLeftPairWitness n p q := by
    have hsub : n - w ≤ n - goldbachLeftPairWitness n p q :=
      Nat.sub_le_sub_left htw n
    have hpP := hbound hpS
    have hqP := hbound hqS
    omega
  constructor
  · exact mem_goldbachObstructionSupportIn.mpr
      ⟨hpS, Or.inl ⟨hdvd.1, Nat.ne_of_gt hproper.1⟩⟩
  · exact mem_goldbachObstructionSupportIn.mpr
      ⟨hqS, Or.inl ⟨hdvd.2, Nat.ne_of_gt hproper.2⟩⟩

/- The lower quantity is deliberately exposed as a finite witness count. -/
def goldbachWindowPairLower (n w : ℕ) (S : Finset ℕ) : ℕ :=
  (goldbachWindowEligibleLeftPairs n w S).card

private def goldbachWindowEligibleLeftPairSeats
    (n w : ℕ) (S : Finset ℕ) : Finset (Σ _ : ℕ, Finset ℕ) :=
  (goldbachBalancedOffsets n w).sigma (fun t =>
    (goldbachObstructionSupportIn n t S).powersetCard 2)

theorem goldbachWindowPairLower_le_pairOverlap
    {n w P : ℕ} {S : Finset ℕ}
    (hS : KnownPrimeScales S) (hbound : ∀ ⦃r : ℕ⦄, r ∈ S → r ≤ P)
    (_hw : w ≤ n) (hanchor : P < n - w) :
    goldbachWindowPairLower n w S ≤ goldbachWindowPairOverlapCount n w S := by
  classical
  let seats := goldbachWindowEligibleLeftPairSeats n w S
  let f : (ℕ × ℕ) → (Σ _ : ℕ, Finset ℕ) := fun pair =>
    ⟨goldbachLeftPairWitness n pair.1 pair.2, {pair.1, pair.2}⟩
  have hfmem : ∀ pair ∈ goldbachWindowEligibleLeftPairs n w S,
      f pair ∈ seats := by
    intro pair hp
    rcases pair with ⟨p, q⟩
    have hsupport := goldbachWindowEligibleLeftPair_support
      hS hbound _hw hanchor hp
    have hwindow := (mem_goldbachWindowEligibleLeftPairs.mp hp).2.2.2
    have hlt := (mem_goldbachWindowEligibleLeftPairs.mp hp).2.2.1
    apply Finset.mem_sigma.mpr
    refine ⟨hwindow, Finset.mem_powersetCard.mpr ⟨?_, ?_⟩⟩
    · intro x hx
      rcases Finset.mem_insert.mp hx with hxp | hxq
      · simpa [hxp] using hsupport.1
      · have hxq' : x = q := Finset.mem_singleton.mp hxq
        simpa [hxq'] using hsupport.2
    · exact Finset.card_pair hlt.ne
  have hfinj : Set.InjOn f
      (goldbachWindowEligibleLeftPairs n w S : Set (ℕ × ℕ)) := by
    intro pair hp pair' hp' heq
    rcases pair with ⟨p, q⟩
    rcases pair' with ⟨a, b⟩
    have hset : ({p, q} : Finset ℕ) = {a, b} := congrArg Sigma.snd heq
    have hpq := (mem_goldbachWindowEligibleLeftPairs.mp hp).2.2.1
    have hab := (mem_goldbachWindowEligibleLeftPairs.mp hp').2.2.1
    have hpmem : p ∈ ({a, b} : Finset ℕ) := by rw [← hset]; simp
    have hqmem : q ∈ ({a, b} : Finset ℕ) := by rw [← hset]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hpmem hqmem
    rcases hpmem with rfl | rfl <;> rcases hqmem with rfl | rfl
    all_goals apply Prod.ext <;> omega
  have hcard : seats.card = goldbachWindowPairOverlapCount n w S := by
    dsimp [seats, goldbachWindowEligibleLeftPairSeats]
    simp [goldbachWindowPairOverlapCount, goldbachWindowLocalPairMultiplicity,
      Finset.card_sigma]
  have hle := Finset.card_le_card_of_injOn f hfmem hfinj
  exact hle.trans_eq hcard

/-! ## Center alignment and the triple progression estimate -/

/-- Every scale in `S` identifies the two signed obstruction classes. -/
def GoldbachCenterAlignedWorld (n : ℕ) (S : Finset ℕ) : Prop :=
  ∀ r ∈ S, r ∣ 2 * n

theorem goldbachCenterAlignedWorld_forbiddenResidues
    {n : ℕ} {S : Finset ℕ} (hcenter : GoldbachCenterAlignedWorld n S)
    {r : ℕ} (hr : r ∈ S) :
    goldbachForbiddenResidues n r = {(n : ZMod r)} := by
  have heq : (n : ZMod r) = -(n : ZMod r) :=
    (goldbach_residue_eq_neg_iff n r).mpr (hcenter r hr)
  unfold goldbachForbiddenResidues
  rw [Finset.insert_eq_of_mem (Finset.mem_singleton.mpr heq)]
  exact congrArg (fun x : ZMod r => ({x} : Finset (ZMod r))) heq.symm

theorem goldbach_center_aligned_obstruction_left
    {n t : ℕ} {S : Finset ℕ}
    (hcenter : GoldbachCenterAlignedWorld n S) (hw : t ≤ n)
    {r : ℕ} (hr : r ∈ S) (hobs : GoldbachProperObstructed n r t) :
    r ∣ n - t := by
  have hraw : GoldbachObstructed n r t := hobs.elim
    (fun h => Or.inl h.1) (fun h => Or.inr h.1)
  have hres := (goldbach_obstructed_iff_mem_forbidden hw).mp hraw
  have hres' : (t : ZMod r) = (n : ZMod r) := by
    rw [goldbachCenterAlignedWorld_forbiddenResidues hcenter hr] at hres
    simpa using hres
  exact (goldbach_left_obstructed_iff hw).mpr hres'

/-- Strictly ordered prime triples in a finite world. -/
def goldbachPrimeTriples (S : Finset ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (S.product (S.product S)).filter (fun triple =>
    triple.1 < triple.2.1 ∧ triple.2.1 < triple.2.2)

@[simp] theorem mem_goldbachPrimeTriples {S : Finset ℕ} {p q r : ℕ} :
    (p, q, r) ∈ goldbachPrimeTriples S ↔
      p ∈ S ∧ q ∈ S ∧ r ∈ S ∧ p < q ∧ q < r := by
  simp [goldbachPrimeTriples, and_assoc]

/-- Safe count for the arithmetic progression `t₀ + k * (p*q*r)`. -/
def goldbachTripleCRTUpper (n w p q r : ℕ) : ℕ :=
  let m := p * q * r
  let t₀ := n % m
  if t₀ ≤ w then w / m + 1 else 0

/-- Executable sum of the per-triple progression bounds. -/
def goldbachTripleCRTUpperSum (n w : ℕ) (S : Finset ℕ) : ℕ :=
  ∑ triple ∈ goldbachPrimeTriples S,
    goldbachTripleCRTUpper n w triple.1 triple.2.1 triple.2.2

theorem goldbachTripleWitness_center_aligned_progression
    {n w : ℕ} {S : Finset ℕ} (hcenter : GoldbachCenterAlignedWorld n S)
    (hS : KnownPrimeScales S) (_hw : w ≤ n) {p q r : ℕ}
    (htriple : (p, q, r) ∈ goldbachPrimeTriples S)
    {t : ℕ} (ht : t ∈ goldbachBalancedOffsets n w)
    (hpt : p ∈ goldbachObstructionSupportIn n t S)
    (hqt : q ∈ goldbachObstructionSupportIn n t S)
    (hrt : r ∈ goldbachObstructionSupportIn n t S) :
    p * q * r ∣ n - t := by
  have htw : t ≤ n := reflection_offset_le_center ht
  have hp := goldbach_center_aligned_obstruction_left hcenter htw
    (mem_goldbachPrimeTriples.mp htriple).1 (mem_goldbachObstructionSupportIn.mp hpt).2
  have hq := goldbach_center_aligned_obstruction_left hcenter htw
    (mem_goldbachPrimeTriples.mp htriple).2.1 (mem_goldbachObstructionSupportIn.mp hqt).2
  have hr := goldbach_center_aligned_obstruction_left hcenter htw
    (mem_goldbachPrimeTriples.mp htriple).2.2.1 (mem_goldbachObstructionSupportIn.mp hrt).2
  have htr := mem_goldbachPrimeTriples.mp htriple
  have hpp : Nat.Prime p := hS htr.1
  have hqq : Nat.Prime q := hS htr.2.1
  have hrr : Nat.Prime r := hS htr.2.2.1
  have hpq : Nat.Coprime p q := (Nat.coprime_primes hpp hqq).mpr (by omega)
  have hpr : Nat.Coprime p r := (Nat.coprime_primes hpp hrr).mpr (by omega)
  have hqr : Nat.Coprime q r := (Nat.coprime_primes hqq hrr).mpr (by omega)
  exact (hpr.mul_left hqr).mul_dvd_of_dvd_of_dvd
    (hpq.mul_dvd_of_dvd_of_dvd hp hq) hr

theorem goldbachTriple_progression_residue
    {n t M : ℕ} (ht : t ≤ n) (hdiv : M ∣ n - t) :
    t % M = n % M := by
  have hmod : t ≡ n [MOD M] := (Nat.modEq_iff_dvd' ht).mpr hdiv
  simpa [Nat.ModEq] using hmod

theorem goldbachTriple_progression_form
    {n t M : ℕ} (ht : t ≤ n) (hdiv : M ∣ n - t) :
    ∃ k : ℕ, t = n % M + M * k := by
  have hres := goldbachTriple_progression_residue ht hdiv
  refine ⟨t / M, ?_⟩
  calc
    t = t % M + M * (t / M) := (Nat.mod_add_div t M).symm
    _ = n % M + M * (t / M) := by rw [hres]

end DkMath.NumberTheory
