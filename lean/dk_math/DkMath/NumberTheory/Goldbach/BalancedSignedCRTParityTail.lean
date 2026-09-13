/-
Copyright (c) 2026 DkMath contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.NumberTheory.Goldbach.BalancedSignedCRTQuadruple
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic

#print "file: DkMath.NumberTheory.Goldbach.BalancedSignedCRTParityTail"

/-!
# Full finite Pascal tail / parity-split signed CRT

This module generalizes the bounded signed CRT layers to arbitrary finite
prime subsets.  It remains a balanced-window, anchor-local accounting API;
no universal survivor inequality or prime-realization theorem is asserted.
-/

namespace DkMath.NumberTheory

open DkMath.NumberTheory.Primitive
open DkMath.NumberTheory.StructuralArithmetic
open scoped BigOperators

/-! ## Generic signed subset CRT -/

/-- Canonical representatives of all signed forbidden classes for a finite
prime subset.  The product of the empty subset is the unit modulus. -/
def signedSubsetResidues (n : ℕ) (Q : Finset ℕ) : Finset ℕ :=
  (Finset.range (Q.prod id)).filter (fun t =>
    ∀ r ∈ Q, (t : ZMod r) ∈ goldbachForbiddenResidues n r)

@[simp] theorem mem_signedSubsetResidues {n t : ℕ} {Q : Finset ℕ} :
    t ∈ signedSubsetResidues n Q ↔
      t < Q.prod id ∧ ∀ r ∈ Q,
        (t : ZMod r) ∈ goldbachForbiddenResidues n r := by
  simp [signedSubsetResidues]

private theorem natCast_mod_subset_prod_eq {t r : ℕ} {Q : Finset ℕ}
    (hr : r ∈ Q) :
    ((t % Q.prod id : ℕ) : ZMod r) = (t : ZMod r) := by
  apply (ZMod.natCast_eq_natCast_iff' (t % Q.prod id) t r).mpr
  exact Nat.mod_mod_of_dvd t (Finset.dvd_prod_of_mem (fun q : ℕ => q) hr)

/-- Balanced seats carrying every obstruction in a finite subset. -/
def goldbachWindowSubsetSupportSeats
    (n w : ℕ) (S Q : Finset ℕ) : Finset ℕ :=
  (goldbachBalancedOffsets n w).filter (fun t =>
    ∀ r ∈ Q, r ∈ goldbachObstructionSupportIn n t S)

@[simp] theorem mem_goldbachWindowSubsetSupportSeats
    {n w : ℕ} {S Q : Finset ℕ} {t : ℕ} :
    t ∈ goldbachWindowSubsetSupportSeats n w S Q ↔
      t ∈ goldbachBalancedOffsets n w ∧
        ∀ r ∈ Q, r ∈ goldbachObstructionSupportIn n t S := by
  simp [goldbachWindowSubsetSupportSeats]

/-- The progression lift of one finite signed subset family. -/
def goldbachSignedSubsetCRTCount
    (n w : ℕ) (Q : Finset ℕ) : ℕ :=
  ∑ t₀ ∈ signedSubsetResidues n Q,
    goldbachProgressionWindowCount (min (n - 2) w) t₀ (Q.prod id)

theorem goldbach_signed_subset_count_eq_progression_sum
    {n w : ℕ} {Q : Finset ℕ} (hM : 0 < Q.prod id) :
    goldbachSignedSubsetCRTCount n w Q =
      ∑ t₀ ∈ signedSubsetResidues n Q,
        (goldbachProgressionSeats (min (n - 2) w) t₀ (Q.prod id)).card := by
  unfold goldbachSignedSubsetCRTCount
  apply Finset.sum_congr rfl
  intro t₀ ht₀
  exact goldbachProgressionWindowCount_eq_card hM

theorem goldbachSignedSubsetCRTCount_eq_supportSeats_card
    {n w P : ℕ} {S Q : Finset ℕ}
    (hn : 2 ≤ n) (hS : KnownPrimeScales S)
    (hbound : ∀ ⦃r : ℕ⦄, r ∈ S → r ≤ P) (hanchor : P < n - w)
    (hQ : Q ⊆ S) :
    goldbachSignedSubsetCRTCount n w Q =
      (goldbachWindowSubsetSupportSeats n w S Q).card := by
  classical
  have hprime : ∀ r ∈ Q, Nat.Prime r := fun r hr => hS (hQ hr)
  have hM : 0 < Q.prod id := Finset.prod_pos (fun r hr => (hprime r hr).pos)
  let A := signedSubsetResidues n Q
  let L := A.sigma (fun t₀ =>
    goldbachProgressionSeats (min (n - 2) w) t₀ (Q.prod id))
  let B := goldbachWindowSubsetSupportSeats n w S Q
  have hcount : goldbachSignedSubsetCRTCount n w Q = L.card := by
    calc
      goldbachSignedSubsetCRTCount n w Q =
          ∑ t₀ ∈ A,
            (goldbachProgressionSeats (min (n - 2) w) t₀ (Q.prod id)).card := by
        simpa [A] using goldbach_signed_subset_count_eq_progression_sum hM
      _ = L.card := by simp [L, Finset.card_sigma]
  have hLB : L.card ≤ B.card := by
    let f : (Σ _ : ℕ, ℕ) → ℕ := Sigma.snd
    have hfmem : ∀ z ∈ L, f z ∈ B := by
      intro z hz
      rcases z with ⟨t₀, t⟩
      rcases Finset.mem_sigma.mp hz with ⟨ht₀, ht⟩
      change t₀ ∈ A at ht₀
      change t ∈ goldbachProgressionSeats (min (n - 2) w) t₀ (Q.prod id) at ht
      have ht₀' := mem_signedSubsetResidues.mp ht₀
      have hprog := (mem_goldbachProgressionSeats_iff_balanced_modEq
        hn hM ht₀'.1).mp ht
      have hsupport : ∀ r ∈ Q, r ∈ goldbachObstructionSupportIn n t S := by
        intro r hr
        have hres : (t : ZMod r) ∈ goldbachForbiddenResidues n r := by
          have hmod := natCast_mod_subset_prod_eq (Q := Q) (t := t) hr
          rw [← hmod, hprog.2]
          exact ht₀'.2 r hr
        exact (goldbach_signed_pair_raw_iff_support hS hbound hanchor
          hprog.1 (hQ hr)).mp hres
      exact mem_goldbachWindowSubsetSupportSeats.mpr ⟨hprog.1, hsupport⟩
    have hfinj : Set.InjOn f (L : Set (Σ _ : ℕ, ℕ)) := by
      intro z hz z' hz' heq
      rcases z with ⟨t₀, t⟩
      rcases z' with ⟨u₀, u⟩
      dsimp [f] at heq
      have htu : t = u := by simpa using heq
      subst u
      have ht₀' := mem_signedSubsetResidues.mp
        (Finset.mem_sigma.mp hz).1
      have hu₀' := mem_signedSubsetResidues.mp
        (Finset.mem_sigma.mp hz').1
      have htp' := (mem_goldbachProgressionSeats_iff_balanced_modEq
        hn hM ht₀'.1).mp (Finset.mem_sigma.mp hz).2
      have hup' := (mem_goldbachProgressionSeats_iff_balanced_modEq
        hn hM hu₀'.1).mp (Finset.mem_sigma.mp hz').2
      have hidx : t₀ = u₀ := by
        calc
          t₀ = t % Q.prod id := by simpa using htp'.2.symm
          _ = u₀ := by simpa using hup'.2
      apply Sigma.ext
      · exact hidx
      · rfl
    exact Finset.card_le_card_of_injOn f hfmem hfinj
  have hBL : B.card ≤ L.card := by
    let g : ℕ → (Σ _ : ℕ, ℕ) := fun t => ⟨t % Q.prod id, t⟩
    have hgmem : ∀ t ∈ B, g t ∈ L := by
      intro t ht
      have ht' := mem_goldbachWindowSubsetSupportSeats.mp ht
      have hsupport := ht'.2
      have hres : ∀ r ∈ Q, (t : ZMod r) ∈ goldbachForbiddenResidues n r := by
        intro r hr
        exact (goldbach_signed_pair_raw_iff_support hS hbound hanchor
          ht'.1 (hQ hr)).mpr (hsupport r hr)
      dsimp [g]
      change (⟨t % Q.prod id, t⟩ : (Σ _ : ℕ, ℕ)) ∈ L
      dsimp [L, A]
      rw [Finset.mem_sigma]
      constructor
      · exact mem_signedSubsetResidues.mpr ⟨Nat.mod_lt t hM, by
          intro r hr
          have hmod := natCast_mod_subset_prod_eq (Q := Q) (t := t) hr
          change (t % Q.prod id : ZMod r) ∈ goldbachForbiddenResidues n r
          rw [hmod]
          exact hres r hr⟩
      · exact (mem_goldbachProgressionSeats_iff_balanced_modEq
          hn hM (Nat.mod_lt t hM)).mpr ⟨ht'.1, rfl⟩
    have hginj : Set.InjOn g (B : Set ℕ) := by
      intro t ht u hu heq
      exact congrArg (fun z : (Σ _ : ℕ, ℕ) => z.2) heq
    exact Finset.card_le_card_of_injOn g hgmem hginj
  exact hcount.trans (Nat.le_antisymm hLB hBL)

/-! ## Generic Pascal layers -/

def goldbachWindowJOverlapCount
    (n w : ℕ) (S : Finset ℕ) (j : ℕ) : ℕ :=
  ∑ t ∈ goldbachBalancedOffsets n w,
    Nat.choose (goldbachObstructionSupportIn n t S).card j

def goldbachSignedJCRTSum
    (n w : ℕ) (S : Finset ℕ) (j : ℕ) : ℕ :=
  ∑ Q ∈ S.powersetCard j,
    goldbachSignedSubsetCRTCount n w Q

theorem goldbachSignedJCRTSum_eq_windowJOverlapCount
    {n w P j : ℕ} {S : Finset ℕ}
    (hn : 2 ≤ n) (hS : KnownPrimeScales S)
    (hbound : ∀ ⦃r : ℕ⦄, r ∈ S → r ≤ P) (hanchor : P < n - w) :
    goldbachSignedJCRTSum n w S j = goldbachWindowJOverlapCount n w S j := by
  classical
  let U := S.powersetCard j
  have hset (t : ℕ) :
      U.filter (fun Q => ∀ r ∈ Q,
        r ∈ goldbachObstructionSupportIn n t S) =
        (goldbachObstructionSupportIn n t S).powersetCard j := by
    ext Q
    constructor
    · intro h
      have h' := Finset.mem_filter.mp h
      have hQ := Finset.mem_powersetCard.mp h'.1
      exact Finset.mem_powersetCard.mpr
        ⟨fun r hr => h'.2 r hr, hQ.2⟩
    · intro h
      have hQ := Finset.mem_powersetCard.mp h
      apply Finset.mem_filter.mpr
      constructor
      · exact Finset.mem_powersetCard.mpr
          ⟨Finset.Subset.trans hQ.1 (Finset.filter_subset _ _), hQ.2⟩
      · exact hQ.1
  calc
    goldbachSignedJCRTSum n w S j =
        ∑ Q ∈ U, (goldbachWindowSubsetSupportSeats n w S Q).card := by
      apply Finset.sum_congr rfl
      intro Q hQ
      exact goldbachSignedSubsetCRTCount_eq_supportSeats_card
        hn hS hbound hanchor (Finset.mem_powersetCard.mp hQ).1
    _ = ∑ Q ∈ U, ∑ t ∈ goldbachBalancedOffsets n w,
          if (∀ r ∈ Q, r ∈ goldbachObstructionSupportIn n t S) then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro Q hQ
      unfold goldbachWindowSubsetSupportSeats
      rw [Finset.card_filter]
    _ = ∑ t ∈ goldbachBalancedOffsets n w, ∑ Q ∈ U,
          if (∀ r ∈ Q, r ∈ goldbachObstructionSupportIn n t S) then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ t ∈ goldbachBalancedOffsets n w,
          (U.filter (fun Q => ∀ r ∈ Q,
            r ∈ goldbachObstructionSupportIn n t S)).card := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [Finset.card_filter]
    _ = ∑ t ∈ goldbachBalancedOffsets n w,
          ((goldbachObstructionSupportIn n t S).powersetCard j).card := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [hset]
    _ = goldbachWindowJOverlapCount n w S j := by
      unfold goldbachWindowJOverlapCount
      apply Finset.sum_congr rfl
      intro t ht
      rw [Finset.card_powersetCard]

/-! ## Nonnegative parity tails -/

private theorem card_even_powerset_eq_card_odd_powerset
    {U : Finset ℕ} (hU : U.Nonempty) :
    (U.powerset.filter (fun A => Even A.card)).card =
      (U.powerset.filter (fun A => Odd A.card)).card := by
  classical
  obtain ⟨a, ha⟩ := hU
  apply Finset.card_bij
    (fun A _ => if a ∈ A then A.erase a else insert a A)
  · intro A hA
    simp only [Finset.mem_filter] at hA ⊢
    rcases hA with ⟨hA, hpar⟩
    have hsub := Finset.mem_powerset.mp hA
    constructor
    · apply Finset.mem_powerset.mpr
      by_cases hmem : a ∈ A
      · simp only [if_pos hmem]
        exact Finset.erase_subset _ _ |>.trans hsub
      · simp only [if_neg hmem]
        exact Finset.insert_subset ha hsub
    · by_cases hmem : a ∈ A
      · have hcard : (A.erase a).card + 1 = A.card :=
          Finset.card_erase_add_one hmem
        have hnot : ¬ Even (A.erase a).card := by
          intro he
          exact (Nat.even_add_one.mp (by simpa [hcard] using hpar)) he
        simp only [if_pos hmem]
        exact Nat.not_even_iff_odd.mp hnot
      · simp only [if_neg hmem]
        simpa [hmem] using hpar.add_one
  · intro A hA B hB hEq
    by_cases hA_mem : a ∈ A <;> by_cases hB_mem : a ∈ B
    · simp [hA_mem, hB_mem] at hEq
      simpa [Finset.insert_erase hA_mem, Finset.insert_erase hB_mem] using
        congrArg (insert a) hEq
    · simp only [if_pos hA_mem, if_neg hB_mem] at hEq
      have : a ∈ A.erase a := hEq ▸ Finset.mem_insert_self a B
      simp at this
    · simp only [if_neg hA_mem, if_pos hB_mem] at hEq
      have : a ∈ B.erase a := hEq ▸ Finset.mem_insert_self a A
      simp at this
    · simp [hA_mem, hB_mem] at hEq
      apply Finset.ext
      intro x
      by_cases hx : x = a
      · subst x
        simp [hA_mem, hB_mem]
      · simpa [hx] using
          (show x ∈ insert a A ↔ x ∈ insert a B by rw [hEq])
  · intro B hB
    simp only [Finset.mem_filter] at hB
    rcases hB with ⟨hB, hpar⟩
    have hsub := Finset.mem_powerset.mp hB
    by_cases hmem : a ∈ B
    · refine ⟨B.erase a, ?_, ?_⟩
      · simp only [Finset.mem_filter]
        constructor
        · exact Finset.mem_powerset.mpr (Finset.erase_subset _ _ |>.trans hsub)
        · have hcard : (B.erase a).card + 1 = B.card :=
            Finset.card_erase_add_one hmem
          have hnot : ¬ Odd (B.erase a).card := by
            intro he
            exact (Nat.odd_add_one.mp (by simpa [hcard] using hpar)) he
          exact Nat.not_odd_iff_even.mp hnot
      · simp [hmem]
    · refine ⟨insert a B, ?_, ?_⟩
      · simp only [Finset.mem_filter]
        constructor
        · exact Finset.mem_powerset.mpr (Finset.insert_subset ha hsub)
        · simpa [hmem] using hpar.add_one
      · simp [hmem]

def goldbachWindowLocalEvenTailMass
    (n _w : ℕ) (S : Finset ℕ) (t : ℕ) : ℕ :=
  ((goldbachObstructionSupportIn n t S).powerset.filter
    (fun A => 2 ≤ A.card ∧ Even A.card)).card

def goldbachWindowLocalOddTailMass
    (n _w : ℕ) (S : Finset ℕ) (t : ℕ) : ℕ :=
  ((goldbachObstructionSupportIn n t S).powerset.filter
    (fun A => 3 ≤ A.card ∧ Odd A.card)).card

def goldbachWindowEvenTailMass (n w : ℕ) (S : Finset ℕ) : ℕ :=
  ∑ t ∈ goldbachBalancedOffsets n w,
    goldbachWindowLocalEvenTailMass n w S t

def goldbachWindowOddTailMass (n w : ℕ) (S : Finset ℕ) : ℕ :=
  ∑ t ∈ goldbachBalancedOffsets n w,
    goldbachWindowLocalOddTailMass n w S t

theorem goldbachWindowLocalEvenTailMass_eq_overlapExcess_add_oddTail
    {n w : ℕ} {S : Finset ℕ} {t : ℕ} :
    goldbachWindowLocalEvenTailMass n w S t =
      goldbachWindowLocalOverlapExcess n w S t +
        goldbachWindowLocalOddTailMass n w S t := by
  classical
  let U := goldbachObstructionSupportIn n t S
  let E := U.powerset.filter (fun A => Even A.card)
  let O := U.powerset.filter (fun A => Odd A.card)
  let Et := U.powerset.filter (fun A => 2 ≤ A.card ∧ Even A.card)
  let Ot := U.powerset.filter (fun A => 3 ≤ A.card ∧ Odd A.card)
  by_cases hU : U.Nonempty
  · have hEO : E.card = O.card := card_even_powerset_eq_card_odd_powerset hU
    have hE : Et.card + 1 = E.card := by
      have hfilter : E.filter (fun A => 2 ≤ A.card) = Et := by
        ext A
        simp [E, Et, and_left_comm, and_assoc, and_comm]
      have hnot0 :
          (U.powerset.filter (fun A => Even A.card)).filter
              (fun A => ¬2 ≤ A.card) = {∅} := by
        ext A
        simp only [not_le, Order.lt_two_iff, Finset.mem_filter, Finset.mem_singleton]
        constructor
        · rintro ⟨⟨hsub, hpar⟩, hsmall⟩
          rcases hpar with ⟨k, hk⟩
          apply Finset.card_eq_zero.mp
          omega
        · rintro rfl
          simp
      have hnot : E.filter (fun A => ¬2 ≤ A.card) = {∅} := by
        simpa [E] using hnot0
      have hcard := Finset.card_filter_add_card_filter_not (s := E)
        (fun A => 2 ≤ A.card)
      rw [hfilter, hnot] at hcard
      simpa using hcard
    have hO : Ot.card + U.card = O.card := by
      have hfilter : O.filter (fun A => 3 ≤ A.card) = Ot := by
        ext A
        simp [O, Ot, and_left_comm, and_assoc, and_comm]
      have hnot : O.filter (fun A => ¬3 ≤ A.card) = U.powersetCard 1 := by
        ext A
        simp only [Finset.mem_filter, Finset.mem_powersetCard]
        dsimp [O]
        constructor
        · rintro ⟨hA, hsmall⟩
          have hpar := (Finset.mem_filter.mp hA).2
          have hsub := (Finset.mem_powerset.mp (Finset.mem_filter.mp hA).1)
          rcases hpar with ⟨k, hk⟩
          apply And.intro hsub
          omega
        · rintro ⟨hsub, hcard⟩
          refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hsub, ?_⟩,
            ?_⟩
          · exact ⟨0, by omega⟩
          · omega
      have hcard := Finset.card_filter_add_card_filter_not (s := O)
        (fun A => 3 ≤ A.card)
      rw [hfilter, hnot, Finset.card_powersetCard] at hcard
      simpa only [Nat.choose_one_right] using hcard
    unfold goldbachWindowLocalEvenTailMass goldbachWindowLocalOddTailMass
      goldbachWindowLocalOverlapExcess
    dsimp [U, Et, Ot, E, O] at hEO hE hO ⊢
    have hUcard : 0 < U.card := Finset.card_pos.mpr hU
    dsimp [U] at hUcard
    omega
  · have hempty : U = ∅ := Finset.not_nonempty_iff_eq_empty.mp hU
    change Et.card = U.card - 1 + Ot.card
    dsimp [Et, Ot]
    rw [hempty]
    decide

theorem goldbachWindowEvenTailMass_eq_overlapExcess_add_oddTail
    (n w : ℕ) (S : Finset ℕ) :
    goldbachWindowEvenTailMass n w S =
      goldbachWindowOverlapExcess n w S + goldbachWindowOddTailMass n w S := by
  unfold goldbachWindowEvenTailMass goldbachWindowOddTailMass
    goldbachWindowOverlapExcess
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t ht
  exact goldbachWindowLocalEvenTailMass_eq_overlapExcess_add_oddTail

/-! ## Signed parity-tail CRT sums -/

def goldbachSignedSubsetCRTSumBy
    (n w : ℕ) (S : Finset ℕ) (p : Finset ℕ → Prop) [DecidablePred p] : ℕ :=
  ∑ Q ∈ S.powerset.filter p,
    goldbachSignedSubsetCRTCount n w Q

private theorem goldbachSignedSubsetCRTSumBy_eq_supportFilterCard
    {n w P : ℕ} {S : Finset ℕ} {p : Finset ℕ → Prop}
    [DecidablePred p]
    (hn : 2 ≤ n) (hS : KnownPrimeScales S)
    (hbound : ∀ ⦃r : ℕ⦄, r ∈ S → r ≤ P) (hanchor : P < n - w) :
    goldbachSignedSubsetCRTSumBy n w S p =
      ∑ t ∈ goldbachBalancedOffsets n w,
        ((goldbachObstructionSupportIn n t S).powerset.filter p).card := by
  classical
  let U := S.powerset.filter p
  have hset (t : ℕ) :
      U.filter (fun Q => ∀ r ∈ Q,
        r ∈ goldbachObstructionSupportIn n t S) =
        (goldbachObstructionSupportIn n t S).powerset.filter p := by
    ext Q
    constructor
    · intro h
      have h' := Finset.mem_filter.mp h
      have hU := Finset.mem_filter.mp h'.1
      have hQ := Finset.mem_powerset.mp hU.1
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_powerset.mpr
        (fun r hr => h'.2 r hr), hU.2⟩
    · intro h
      have hQ := Finset.mem_filter.mp h
      apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_powerset.mpr
          (Finset.Subset.trans (Finset.mem_powerset.mp hQ.1)
            (Finset.filter_subset _ _)), hQ.2⟩
      · exact Finset.mem_powerset.mp hQ.1
  calc
    goldbachSignedSubsetCRTSumBy n w S p =
        ∑ Q ∈ U, (goldbachWindowSubsetSupportSeats n w S Q).card := by
      apply Finset.sum_congr rfl
      intro Q hQ
      exact goldbachSignedSubsetCRTCount_eq_supportSeats_card
        hn hS hbound hanchor (Finset.mem_powerset.mp
          (Finset.mem_filter.mp hQ).1)
    _ = ∑ Q ∈ U, ∑ t ∈ goldbachBalancedOffsets n w,
          if (∀ r ∈ Q, r ∈ goldbachObstructionSupportIn n t S) then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro Q hQ
      unfold goldbachWindowSubsetSupportSeats
      rw [Finset.card_filter]
    _ = ∑ t ∈ goldbachBalancedOffsets n w, ∑ Q ∈ U,
          if (∀ r ∈ Q, r ∈ goldbachObstructionSupportIn n t S) then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ t ∈ goldbachBalancedOffsets n w,
          (U.filter (fun Q => ∀ r ∈ Q,
            r ∈ goldbachObstructionSupportIn n t S)).card := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [Finset.card_filter]
    _ = ∑ t ∈ goldbachBalancedOffsets n w,
          ((goldbachObstructionSupportIn n t S).powerset.filter p).card := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [hset]

def goldbachSignedEvenTailCRTSum (n w : ℕ) (S : Finset ℕ) : ℕ :=
  goldbachSignedSubsetCRTSumBy n w S
    (fun Q => 2 ≤ Q.card ∧ Even Q.card)

def goldbachSignedOddTailCRTSum (n w : ℕ) (S : Finset ℕ) : ℕ :=
  goldbachSignedSubsetCRTSumBy n w S
    (fun Q => 3 ≤ Q.card ∧ Odd Q.card)

theorem goldbachSignedEvenTailCRTSum_eq_windowEvenTailMass
    {n w P : ℕ} {S : Finset ℕ}
    (hn : 2 ≤ n) (hS : KnownPrimeScales S)
    (hbound : ∀ ⦃r : ℕ⦄, r ∈ S → r ≤ P) (hanchor : P < n - w) :
    goldbachSignedEvenTailCRTSum n w S = goldbachWindowEvenTailMass n w S := by
  simpa [goldbachSignedEvenTailCRTSum, goldbachWindowEvenTailMass,
    goldbachWindowLocalEvenTailMass] using
    (goldbachSignedSubsetCRTSumBy_eq_supportFilterCard
      (p := fun Q => 2 ≤ Q.card ∧ Even Q.card) hn hS hbound hanchor)

theorem goldbachSignedOddTailCRTSum_eq_windowOddTailMass
    {n w P : ℕ} {S : Finset ℕ}
    (hn : 2 ≤ n) (hS : KnownPrimeScales S)
    (hbound : ∀ ⦃r : ℕ⦄, r ∈ S → r ≤ P) (hanchor : P < n - w) :
    goldbachSignedOddTailCRTSum n w S = goldbachWindowOddTailMass n w S := by
  simpa [goldbachSignedOddTailCRTSum, goldbachWindowOddTailMass,
    goldbachWindowLocalOddTailMass] using
    (goldbachSignedSubsetCRTSumBy_eq_supportFilterCard
      (p := fun Q => 3 ≤ Q.card ∧ Odd Q.card) hn hS hbound hanchor)

theorem goldbachSignedEvenTailCRTSum_eq_overlapExcess_add_oddTailCRT
    {n w P : ℕ} {S : Finset ℕ}
    (hn : 2 ≤ n) (hS : KnownPrimeScales S)
    (hbound : ∀ ⦃r : ℕ⦄, r ∈ S → r ≤ P) (hanchor : P < n - w) :
    goldbachSignedEvenTailCRTSum n w S =
      goldbachWindowOverlapExcess n w S +
        goldbachSignedOddTailCRTSum n w S := by
  rw [goldbachSignedEvenTailCRTSum_eq_windowEvenTailMass hn hS hbound hanchor,
    goldbachSignedOddTailCRTSum_eq_windowOddTailMass hn hS hbound hanchor]
  exact goldbachWindowEvenTailMass_eq_overlapExcess_add_oddTail n w S

/-! ## Exact parity-budget normal form -/

theorem goldbachWindowSurvivors_nonempty_iff_exact_signed_parity_budget
    {n w P : ℕ} {S : Finset ℕ}
    (hn : 2 ≤ n) (hS : KnownPrimeScales S)
    (hbound : ∀ ⦃r : ℕ⦄, r ∈ S → r ≤ P) (hanchor : P < n - w) :
    (goldbachWindowSurvivors n w S).Nonempty ↔
      goldbachSignedSingleCRTSum n w S +
          goldbachSignedOddTailCRTSum n w S <
        (goldbachBalancedOffsets n w).card +
          goldbachSignedEvenTailCRTSum n w S := by
  rw [goldbachWindowSurvivors_nonempty_iff_incidence_lt]
  rw [goldbachSignedSingleCRTSum_eq_windowIncidence hn hS hbound hanchor,
    goldbachSignedEvenTailCRTSum_eq_overlapExcess_add_oddTailCRT
      hn hS hbound hanchor]
  omega

theorem goldbachPairAt_of_exact_signed_parity_budget
    {n w P : ℕ} (hn : 2 ≤ n) (hw : w ≤ n)
    (hanchor : P < n - w) (hhorizon : n + w ≤ squareBody P)
    (hbudget :
      goldbachSignedSingleCRTSum n w (primeScalesUpTo P) +
          goldbachSignedOddTailCRTSum n w (primeScalesUpTo P) <
        (goldbachBalancedOffsets n w).card +
          goldbachSignedEvenTailCRTSum n w (primeScalesUpTo P)) :
    GoldbachPairAt n := by
  have hsurv :=
    (goldbachWindowSurvivors_nonempty_iff_exact_signed_parity_budget
      (n := n) (w := w) (P := P) (S := primeScalesUpTo P) hn
      (knownPrimeScales_primeScalesUpTo P)
      (hbound := fun {_} hr => (mem_primeScalesUpTo.mp hr).2)
      hanchor).mpr hbudget
  obtain ⟨t, ht⟩ := hsurv
  exact goldbachPairAt_of_goldbachWindowSurvivor hw
    (mem_goldbachWindowSurvivors.mp ht).1 hanchor hhorizon
    (mem_goldbachWindowSurvivors.mp ht).2


end DkMath.NumberTheory
