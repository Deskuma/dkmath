/-
Copyright (c) 2026 DkMath contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.NumberTheory.Goldbach.BalancedCRTOverlap
import Mathlib.Data.Finset.Sigma
import Mathlib.Tactic

#print "file: DkMath.NumberTheory.Goldbach.BalancedSignedCRTOverlap"

/-!
# Balanced signed CRT residues

This file gives the finite signed pair/triple residue families behind the
cross-gap ledger.  A family is the set of canonical representatives in one
product period whose local coordinates lie in the existing Goldbach
forbidden classes.  The development is deliberately finite and local: it
does not provide a universal survivor inequality or a prime provider.
-/

namespace DkMath.NumberTheory

open DkMath.NumberTheory.StructuralArithmetic
open scoped BigOperators

/-! ## Canonical signed residue families -/

/-- Canonical representatives of the simultaneous signed pair classes. -/
def signedPairResidues (n p q : ℕ) : Finset ℕ :=
  (Finset.range (p * q)).filter (fun t =>
    (t : ZMod p) ∈ goldbachForbiddenResidues n p ∧
      (t : ZMod q) ∈ goldbachForbiddenResidues n q)

@[simp] theorem mem_signedPairResidues {n p q t : ℕ} :
    t ∈ signedPairResidues n p q ↔
      t < p * q ∧
        (t : ZMod p) ∈ goldbachForbiddenResidues n p ∧
          (t : ZMod q) ∈ goldbachForbiddenResidues n q := by
  simp [signedPairResidues]

/-- Canonical representatives of the simultaneous signed triple classes. -/
def signedTripleResidues (n p q r : ℕ) : Finset ℕ :=
  (Finset.range (p * q * r)).filter (fun t =>
    (t : ZMod p) ∈ goldbachForbiddenResidues n p ∧
      (t : ZMod q) ∈ goldbachForbiddenResidues n q ∧
        (t : ZMod r) ∈ goldbachForbiddenResidues n r)

@[simp] theorem mem_signedTripleResidues {n p q r t : ℕ} :
    t ∈ signedTripleResidues n p q r ↔
      t < p * q * r ∧
        (t : ZMod p) ∈ goldbachForbiddenResidues n p ∧
          (t : ZMod q) ∈ goldbachForbiddenResidues n q ∧
            (t : ZMod r) ∈ goldbachForbiddenResidues n r := by
  simp [signedTripleResidues]

private theorem nat_eq_of_mod_eq_of_lt_mul
    {a b p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (hcop : Nat.Coprime p q) (ha : a < p * q) (hb : b < p * q)
    (hpm : a % p = b % p) (hqm : a % q = b % q) : a = b := by
  have hpos : 0 < p * q := Nat.mul_pos hp hq
  rcases le_total a b with hab | hba
  · have hpd : p ∣ b - a :=
      (Nat.modEq_iff_dvd' hab).mp (by simpa [Nat.ModEq] using hpm)
    have hqd : q ∣ b - a :=
      (Nat.modEq_iff_dvd' hab).mp (by simpa [Nat.ModEq] using hqm)
    have hd : p * q ∣ b - a := hcop.mul_dvd_of_dvd_of_dvd hpd hqd
    have hlt : b - a < p * q := by omega
    have hzero : b - a = 0 := Nat.eq_zero_of_dvd_of_lt hd hlt
    omega
  · have hpd : p ∣ a - b :=
      (Nat.modEq_iff_dvd' hba).mp (by simpa [Nat.ModEq] using hpm.symm)
    have hqd : q ∣ a - b :=
      (Nat.modEq_iff_dvd' hba).mp (by simpa [Nat.ModEq] using hqm.symm)
    have hd : p * q ∣ a - b := hcop.mul_dvd_of_dvd_of_dvd hpd hqd
    have hlt : a - b < p * q := by omega
    have hzero : a - b = 0 := Nat.eq_zero_of_dvd_of_lt hd hlt
    omega

private theorem nat_eq_of_three_mod_eq_of_lt_mul
    {a b p q r : ℕ} (hpq : Nat.Coprime p q) (hpr : Nat.Coprime p r)
    (hqr : Nat.Coprime q r) (ha : a < p * q * r) (hb : b < p * q * r)
    (hpm : a % p = b % p) (hqm : a % q = b % q)
    (hrm : a % r = b % r) : a = b := by
  rcases le_total a b with hab | hba
  · have hpd : p ∣ b - a :=
      (Nat.modEq_iff_dvd' hab).mp (by simpa [Nat.ModEq] using hpm)
    have hqd : q ∣ b - a :=
      (Nat.modEq_iff_dvd' hab).mp (by simpa [Nat.ModEq] using hqm)
    have hrd : r ∣ b - a :=
      (Nat.modEq_iff_dvd' hab).mp (by simpa [Nat.ModEq] using hrm)
    have hpqd : p * q ∣ b - a := hpq.mul_dvd_of_dvd_of_dvd hpd hqd
    have hd : p * q * r ∣ b - a :=
      (hpr.mul_left hqr).mul_dvd_of_dvd_of_dvd hpqd hrd
    have hlt : b - a < p * q * r := by omega
    have hzero : b - a = 0 := Nat.eq_zero_of_dvd_of_lt hd hlt
    omega
  · have hpd : p ∣ a - b :=
      (Nat.modEq_iff_dvd' hba).mp (by simpa [Nat.ModEq] using hpm.symm)
    have hqd : q ∣ a - b :=
      (Nat.modEq_iff_dvd' hba).mp (by simpa [Nat.ModEq] using hqm.symm)
    have hrd : r ∣ a - b :=
      (Nat.modEq_iff_dvd' hba).mp (by simpa [Nat.ModEq] using hrm.symm)
    have hpqd : p * q ∣ a - b := hpq.mul_dvd_of_dvd_of_dvd hpd hqd
    have hd : p * q * r ∣ a - b :=
      (hpr.mul_left hqr).mul_dvd_of_dvd_of_dvd hpqd hrd
    have hlt : a - b < p * q * r := by omega
    have hzero : a - b = 0 := Nat.eq_zero_of_dvd_of_lt hd hlt
    omega

theorem signedPairResidues_card_le_product
    {n p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p ≠ q) :
    (signedPairResidues n p q).card ≤
      (goldbachForbiddenResidues n p).card *
        (goldbachForbiddenResidues n q).card := by
  classical
  let T := (goldbachForbiddenResidues n p).product
    (goldbachForbiddenResidues n q)
  have hcard : (signedPairResidues n p q).card ≤ T.card := by
    refine Finset.card_le_card_of_injOn
      (fun t : ℕ => ((t : ZMod p), (t : ZMod q))) ?_ ?_
    · intro t ht
      have ht' := mem_signedPairResidues.mp ht
      exact Finset.mem_product.mpr ⟨ht'.2.1, ht'.2.2⟩
    · intro a ha b hb he
      have ha' := mem_signedPairResidues.mp ha
      have hb' := mem_signedPairResidues.mp hb
      have hpm := (ZMod.natCast_eq_natCast_iff' a b p).mp
        (congrArg Prod.fst he)
      have hqm := (ZMod.natCast_eq_natCast_iff' a b q).mp
        (congrArg Prod.snd he)
      exact nat_eq_of_mod_eq_of_lt_mul hp.pos hq.pos
        ((Nat.coprime_primes hp hq).mpr hpq) ha'.1 hb'.1 hpm hqm
  simpa [T, Finset.card_product] using hcard

theorem signedPairResidues_card_le_four
    {n p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p ≠ q) :
    (signedPairResidues n p q).card ≤ 4 := by
  calc
    (signedPairResidues n p q).card ≤
        (goldbachForbiddenResidues n p).card *
          (goldbachForbiddenResidues n q).card :=
      signedPairResidues_card_le_product hp hq hpq
    _ ≤ 4 := by
      simp only [goldbach_card_forbidden]
      split <;> split <;> omega

theorem signedTripleResidues_card_le_product
    {n p q r : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hr : Nat.Prime r) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    (signedTripleResidues n p q r).card ≤
      (goldbachForbiddenResidues n p).card *
        ((goldbachForbiddenResidues n q).card *
          (goldbachForbiddenResidues n r).card) := by
  classical
  let T := (goldbachForbiddenResidues n p).product
    ((goldbachForbiddenResidues n q).product (goldbachForbiddenResidues n r))
  have hcard : (signedTripleResidues n p q r).card ≤ T.card := by
    refine Finset.card_le_card_of_injOn
      (fun t : ℕ => ((t : ZMod p), ((t : ZMod q), (t : ZMod r)))) ?_ ?_
    · intro t ht
      have ht' := mem_signedTripleResidues.mp ht
      exact Finset.mem_product.mpr ⟨ht'.2.1,
        Finset.mem_product.mpr ⟨ht'.2.2.1, ht'.2.2.2⟩⟩
    · intro a ha b hb he
      have ha' := mem_signedTripleResidues.mp ha
      have hb' := mem_signedTripleResidues.mp hb
      have hpm := (ZMod.natCast_eq_natCast_iff' a b p).mp
        (congrArg Prod.fst he)
      have hqm := (ZMod.natCast_eq_natCast_iff' a b q).mp
        (congrArg (fun x => x.2.1) he)
      have hrm := (ZMod.natCast_eq_natCast_iff' a b r).mp
        (congrArg (fun x => x.2.2) he)
      have hpq : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq
      have hpr : Nat.Coprime p r := (Nat.coprime_primes hp hr).mpr hpr
      have hqr : Nat.Coprime q r := (Nat.coprime_primes hq hr).mpr hqr
      rcases le_total a b with hab | hba
      · have hpd : p ∣ b - a :=
          (Nat.modEq_iff_dvd' hab).mp (by simpa [Nat.ModEq] using hpm)
        have hqd : q ∣ b - a :=
          (Nat.modEq_iff_dvd' hab).mp (by simpa [Nat.ModEq] using hqm)
        have hrd : r ∣ b - a :=
          (Nat.modEq_iff_dvd' hab).mp (by simpa [Nat.ModEq] using hrm)
        have hpqd : p * q ∣ b - a := hpq.mul_dvd_of_dvd_of_dvd hpd hqd
        have hd : p * q * r ∣ b - a :=
          (hpr.mul_left hqr).mul_dvd_of_dvd_of_dvd hpqd hrd
        have hlt : b - a < p * q * r := by omega
        have hzero : b - a = 0 := Nat.eq_zero_of_dvd_of_lt hd hlt
        omega
      · have hpd : p ∣ a - b :=
          (Nat.modEq_iff_dvd' hba).mp (by simpa [Nat.ModEq] using hpm.symm)
        have hqd : q ∣ a - b :=
          (Nat.modEq_iff_dvd' hba).mp (by simpa [Nat.ModEq] using hqm.symm)
        have hrd : r ∣ a - b :=
          (Nat.modEq_iff_dvd' hba).mp (by simpa [Nat.ModEq] using hrm.symm)
        have hpqd : p * q ∣ a - b := hpq.mul_dvd_of_dvd_of_dvd hpd hqd
        have hd : p * q * r ∣ a - b :=
          (hpr.mul_left hqr).mul_dvd_of_dvd_of_dvd hpqd hrd
        have hlt : a - b < p * q * r := by omega
        have hzero : a - b = 0 := Nat.eq_zero_of_dvd_of_lt hd hlt
        omega
  simpa [T, Finset.card_product] using hcard

theorem signedTripleResidues_card_le_eight
    {n p q r : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hr : Nat.Prime r) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    (signedTripleResidues n p q r).card ≤ 8 := by
  calc
    (signedTripleResidues n p q r).card ≤
        (goldbachForbiddenResidues n p).card *
          ((goldbachForbiddenResidues n q).card *
            (goldbachForbiddenResidues n r).card) :=
      signedTripleResidues_card_le_product hp hq hr hpq hpr hqr
    _ ≤ 8 := by
      simp only [goldbach_card_forbidden]
      split <;> split <;> split <;> omega

theorem signedTripleResidues_center_aligned_eq_singleton
    {n p q r : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hr : Nat.Prime r) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hpc : p ∣ 2 * n) (hqc : q ∣ 2 * n) (hrc : r ∣ 2 * n) :
    signedTripleResidues n p q r =
      ({goldbachTripleWitness n p q r} : Finset ℕ) := by
  classical
  have hfp : goldbachForbiddenResidues n p = {(n : ZMod p)} := by
    unfold goldbachForbiddenResidues
    have heq : (n : ZMod p) = -(n : ZMod p) :=
      (goldbach_residue_eq_neg_iff n p).mpr hpc
    rw [Finset.insert_eq_of_mem (Finset.mem_singleton.mpr heq)]
    exact congrArg (fun x : ZMod p => ({x} : Finset (ZMod p))) heq.symm
  have hfq : goldbachForbiddenResidues n q = {(n : ZMod q)} := by
    unfold goldbachForbiddenResidues
    have heq : (n : ZMod q) = -(n : ZMod q) :=
      (goldbach_residue_eq_neg_iff n q).mpr hqc
    rw [Finset.insert_eq_of_mem (Finset.mem_singleton.mpr heq)]
    exact congrArg (fun x : ZMod q => ({x} : Finset (ZMod q))) heq.symm
  have hfr : goldbachForbiddenResidues n r = {(n : ZMod r)} := by
    unfold goldbachForbiddenResidues
    have heq : (n : ZMod r) = -(n : ZMod r) :=
      (goldbach_residue_eq_neg_iff n r).mpr hrc
    rw [Finset.insert_eq_of_mem (Finset.mem_singleton.mpr heq)]
    exact congrArg (fun x : ZMod r => ({x} : Finset (ZMod r))) heq.symm
  let M := p * q * r
  let t₀ := n % M
  have hM : 0 < M := by
    dsimp [M]
    exact Nat.mul_pos (Nat.mul_pos hp.pos hq.pos) hr.pos
  have hpm0 : t₀ % p = n % p := by
    dsimp [t₀, M]
    rw [Nat.mod_mod_of_dvd n ⟨q * r, by ring⟩]
  have hqm0 : t₀ % q = n % q := by
    dsimp [t₀, M]
    rw [Nat.mod_mod_of_dvd n ⟨p * r, by ring⟩]
  have hrm0 : t₀ % r = n % r := by
    dsimp [t₀, M]
    rw [Nat.mod_mod_of_dvd n ⟨p * q, by ring⟩]
  have ht₀lt : t₀ < M := by
    exact Nat.mod_lt n hM
  have hcop_pq : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq
  have hcop_pr : Nat.Coprime p r := (Nat.coprime_primes hp hr).mpr hpr
  have hcop_qr : Nat.Coprime q r := (Nat.coprime_primes hq hr).mpr hqr
  ext t
  constructor
  · intro ht
    have ht' := mem_signedTripleResidues.mp ht
    apply Finset.mem_singleton.mpr
    apply nat_eq_of_three_mod_eq_of_lt_mul hcop_pq hcop_pr hcop_qr
      ht'.1 ht₀lt
    · exact ((ZMod.natCast_eq_natCast_iff' t n p).mp
        (by simpa [hfp] using ht'.2.1)).trans hpm0.symm
    · exact ((ZMod.natCast_eq_natCast_iff' t n q).mp
        (by simpa [hfq] using ht'.2.2.1)).trans hqm0.symm
    · exact ((ZMod.natCast_eq_natCast_iff' t n r).mp
        (by simpa [hfr] using ht'.2.2.2)).trans hrm0.symm
  · intro ht
    have ht' := Finset.mem_singleton.mp ht
    rw [ht']
    change t₀ ∈ signedTripleResidues n p q r
    apply mem_signedTripleResidues.mpr
    refine ⟨ht₀lt, ?_, ?_, ?_⟩
    · rw [hfp]
      exact Finset.mem_singleton.mpr
        ((ZMod.natCast_eq_natCast_iff' t₀ n p).mpr hpm0)
    · rw [hfq]
      exact Finset.mem_singleton.mpr
        ((ZMod.natCast_eq_natCast_iff' t₀ n q).mpr hqm0)
    · rw [hfr]
      exact Finset.mem_singleton.mpr
        ((ZMod.natCast_eq_natCast_iff' t₀ n r).mpr hrm0)

/-! ## Explicit finite progressions -/

/-- The seats generated by one canonical residue in a plain interval. -/
def goldbachProgressionSeats (w t₀ M : ℕ) : Finset ℕ :=
  if t₀ ≤ w then
    (Finset.range ((w - t₀) / M + 1)).image (fun k => t₀ + M * k)
  else ∅

theorem goldbachProgressionSeats_card
    {w t₀ M : ℕ} (hM : 0 < M) (ht₀ : t₀ ≤ w) :
    (goldbachProgressionSeats w t₀ M).card = (w - t₀) / M + 1 := by
  classical
  rw [goldbachProgressionSeats, ite_eq_left ht₀]
  have hinj : Set.InjOn (fun k => t₀ + M * k)
      (Finset.range ((w - t₀) / M + 1) : Set ℕ) := by
    intro a ha b hb hab
    have hmul : M * a = M * b := Nat.add_left_cancel hab
    exact Nat.mul_left_cancel hM hmul
  simpa using (Finset.card_image_iff.mpr hinj)

theorem mem_goldbachProgressionSeats
    {w t₀ M t : ℕ} (ht : t ∈ goldbachProgressionSeats w t₀ M) :
    ∃ k < (w - t₀) / M + 1, t = t₀ + M * k := by
  classical
  simp only [goldbachProgressionSeats] at ht
  split at ht
  · rcases (Finset.mem_image.mp ht) with ⟨k, hk, rfl⟩
    exact ⟨k, Finset.mem_range.mp hk, rfl⟩
  · simp at ht

def goldbachProgressionWindowCount (w t₀ M : ℕ) : ℕ :=
  if t₀ ≤ w then (w - t₀) / M + 1 else 0

theorem goldbachProgressionWindowCount_eq_card
    {w t₀ M : ℕ} (hM : 0 < M) :
    goldbachProgressionWindowCount w t₀ M =
      (goldbachProgressionSeats w t₀ M).card := by
  unfold goldbachProgressionWindowCount
  split
  · exact (goldbachProgressionSeats_card hM ‹t₀ ≤ w›).symm
  · rw [goldbachProgressionSeats, ite_eq_right ‹¬t₀ ≤ w›]
    simp

/-! ## Window sums and the anchor-local support bridge -/

def goldbachSignedPairCRTCount (n w p q : ℕ) : ℕ :=
  ∑ t₀ ∈ signedPairResidues n p q,
    goldbachProgressionWindowCount (min (n - 2) w) t₀ (p * q)

def goldbachSignedTripleCRTCount (n w p q r : ℕ) : ℕ :=
  ∑ t₀ ∈ signedTripleResidues n p q r,
    goldbachProgressionWindowCount (min (n - 2) w) t₀ (p * q * r)

def goldbachStrictPrimePairs (S : Finset ℕ) : Finset (ℕ × ℕ) :=
  (S.product S).filter (fun pair => pair.1 < pair.2)

@[simp] theorem mem_goldbachStrictPrimePairs {S : Finset ℕ} {p q : ℕ} :
    (p, q) ∈ goldbachStrictPrimePairs S ↔ p ∈ S ∧ q ∈ S ∧ p < q := by
  simp [goldbachStrictPrimePairs, and_assoc]

def goldbachSignedPairCRTSum (n w : ℕ) (S : Finset ℕ) : ℕ :=
  ∑ pair ∈ goldbachStrictPrimePairs S,
    goldbachSignedPairCRTCount n w pair.1 pair.2

def goldbachSignedTripleCRTSum (n w : ℕ) (S : Finset ℕ) : ℕ :=
  ∑ triple ∈ goldbachPrimeTriples S,
    goldbachSignedTripleCRTCount n w triple.1 triple.2.1 triple.2.2

/-!
The provider-facing comparison hypotheses remain explicit.  The signed sums
are not silently identified with Pascal overlap counts for arbitrary worlds.
-/

theorem goldbachWindowSurvivor_of_signed_crt_budget
    {n w : ℕ} {S : Finset ℕ} {C : ℕ}
    (hincidence : goldbachWindowIncidence n w S ≤ C)
    (hpair : goldbachSignedPairCRTSum n w S ≤
      goldbachWindowPairOverlapCount n w S)
    (htriple : goldbachWindowTripleOverlapCount n w S ≤
      goldbachSignedTripleCRTSum n w S)
    (hbudget : C < (goldbachBalancedOffsets n w).card +
      (goldbachSignedPairCRTSum n w S - goldbachSignedTripleCRTSum n w S)) :
    (goldbachWindowSurvivors n w S).Nonempty := by
  apply goldbachWindowSurvivor_of_incidence_le_of_pairMinusTriple_budget
    hincidence
  have hpay : goldbachSignedPairCRTSum n w S -
      goldbachSignedTripleCRTSum n w S ≤
      goldbachWindowPairOverlapCount n w S -
        goldbachWindowTripleOverlapCount n w S := by
    omega
  omega

theorem goldbach_signed_pair_count_eq_progression_sum
    {n w p q : ℕ} (hM : 0 < p * q) :
    goldbachSignedPairCRTCount n w p q =
      ∑ t₀ ∈ signedPairResidues n p q,
        (goldbachProgressionSeats (min (n - 2) w) t₀ (p * q)).card := by
  unfold goldbachSignedPairCRTCount
  apply Finset.sum_congr rfl
  intro t₀ ht₀
  exact goldbachProgressionWindowCount_eq_card hM

theorem goldbach_signed_triple_count_eq_progression_sum
    {n w p q r : ℕ} (hM : 0 < p * q * r) :
    goldbachSignedTripleCRTCount n w p q r =
      ∑ t₀ ∈ signedTripleResidues n p q r,
        (goldbachProgressionSeats (min (n - 2) w) t₀ (p * q * r)).card := by
  unfold goldbachSignedTripleCRTCount
  apply Finset.sum_congr rfl
  intro t₀ ht₀
  exact goldbachProgressionWindowCount_eq_card hM

theorem goldbach_signed_pair_raw_iff_support
    {n w P : ℕ} {S : Finset ℕ} (_hS : KnownPrimeScales S)
    (hbound : ∀ ⦃r : ℕ⦄, r ∈ S → r ≤ P) (hanchor : P < n - w)
    {t r : ℕ} (ht : t ∈ goldbachBalancedOffsets n w) (hr : r ∈ S) :
    (t : ZMod r) ∈ goldbachForbiddenResidues n r ↔
      r ∈ goldbachObstructionSupportIn n t S := by
  have htw : t ≤ n := reflection_offset_le_center ht
  constructor
  · intro hraw
    have hobs : GoldbachObstructed n r t :=
      (goldbach_obstructed_iff_mem_forbidden htw).mpr hraw
    rcases hobs with hleft | hright
    · exact mem_goldbachObstructionSupportIn.mpr
        ⟨hr, Or.inl ⟨hleft, by
          have := hbound hr
          have := (mem_goldbachBalancedOffsets.mp ht).2
          omega⟩⟩
    · exact mem_goldbachObstructionSupportIn.mpr
        ⟨hr, Or.inr ⟨hright, by
          have := hbound hr
          have := (mem_goldbachBalancedOffsets.mp ht).2
          omega⟩⟩
  · intro hs
    have hobs := (mem_goldbachObstructionSupportIn.mp hs).2
    exact (goldbach_obstructed_iff_mem_forbidden htw).mp
      (hobs.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1))

/-! ## Target-15 executable checks -/

theorem signedTripleResidues_target_eq_existing_witness :
    signedTripleResidues 15 2 3 5 =
      ({goldbachTripleWitness 15 2 3 5} : Finset ℕ) := by
  decide

theorem signedPairResidues_target_card :
    (signedPairResidues 15 2 3).card = 1 ∧
      (signedPairResidues 15 2 5).card = 1 ∧
      (signedPairResidues 15 3 5).card = 1 := by decide

theorem signedTripleResidues_target_card :
    (signedTripleResidues 15 2 3 5).card = 1 := by decide

theorem goldbachSignedPairCRTSum_target :
    goldbachSignedPairCRTSum 15 8 {2, 3, 5} = 3 := by decide

theorem goldbachSignedTripleCRTSum_target :
    goldbachSignedTripleCRTSum 15 8 {2, 3, 5} = 0 := by decide

end DkMath.NumberTheory
