/-
Copyright (c) 2026 DkMath contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.NumberTheory.Goldbach.BalancedSignedCRTIncidence
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic

#print "file: DkMath.NumberTheory.Goldbach.BalancedSignedCRTQuadruple"

/-!
# Bounded quadruple signed CRT / Pascal payment

This module adds the fourth finite overlap layer.  Its payment identity is
proved only under the visible support-card bound `≤ 4`; no unconditional
four-layer inequality is asserted.
-/

namespace DkMath.NumberTheory

open DkMath.NumberTheory.Primitive
open DkMath.NumberTheory.StructuralArithmetic
open scoped BigOperators

/-! ## Fourth local Pascal layer -/

/-- The fourth Pascal multiplicity at one balanced seat. -/
def goldbachWindowLocalQuadrupleMultiplicity
    (n _w : ℕ) (S : Finset ℕ) (t : ℕ) : ℕ :=
  Nat.choose (goldbachObstructionSupportIn n t S).card 4

/-- The fourth Pascal multiplicity summed over the balanced window. -/
def goldbachWindowQuadrupleOverlapCount
    (n w : ℕ) (S : Finset ℕ) : ℕ :=
  ∑ t ∈ goldbachBalancedOffsets n w,
    goldbachWindowLocalQuadrupleMultiplicity n w S t

/-- The bounded local Pascal identity at support size at most four. -/
theorem choose_sub_one_eq_pair_sub_triple_add_quadruple_of_le_four
    {k : ℕ} (hk : k ≤ 4) :
    k - 1 = (Nat.choose k 2 - Nat.choose k 3) + Nat.choose k 4 := by
  interval_cases k <;> decide

/-- A support set is bounded by the finite world that defines it. -/
theorem goldbachObstructionSupportIn_card_le_world_card
    (n t : ℕ) (S : Finset ℕ) :
    (goldbachObstructionSupportIn n t S).card ≤ S.card := by
  exact Finset.card_le_card (Finset.filter_subset _ _)

/-- A finite world of cardinality at most four supplies the local support bound. -/
theorem goldbach_support_card_le_four_of_world_card_le_four
    {n w : ℕ} {S : Finset ℕ} (hS4 : S.card ≤ 4) :
    ∀ t ∈ goldbachBalancedOffsets n w,
      (goldbachObstructionSupportIn n t S).card ≤ 4 := by
  intro t ht
  exact (goldbachObstructionSupportIn_card_le_world_card n t S).trans hS4

theorem goldbachWindowLocalOverlapExcess_eq_pair_sub_triple_add_quadruple
    {n w : ℕ} {S : Finset ℕ} {t : ℕ}
    (hsupport4 : (goldbachObstructionSupportIn n t S).card ≤ 4) :
    goldbachWindowLocalOverlapExcess n w S t =
      (goldbachWindowLocalPairMultiplicity n w S t -
        goldbachWindowLocalTripleMultiplicity n w S t) +
        goldbachWindowLocalQuadrupleMultiplicity n w S t := by
  let k := (goldbachObstructionSupportIn n t S).card
  have hlocal : goldbachWindowLocalOverlapExcess n w S t = k - 1 := by
    unfold goldbachWindowLocalOverlapExcess
    rfl
  rw [hlocal]
  change k - 1 = (Nat.choose k 2 - Nat.choose k 3) + Nat.choose k 4
  exact choose_sub_one_eq_pair_sub_triple_add_quadruple_of_le_four hsupport4

/-- Exact fourth-layer payment on a window with support size at most four. -/
theorem goldbachWindowOverlapExcess_eq_pair_sub_triple_add_quadruple
    {n w : ℕ} {S : Finset ℕ}
    (hsupport4 : ∀ t ∈ goldbachBalancedOffsets n w,
      (goldbachObstructionSupportIn n t S).card ≤ 4) :
    goldbachWindowOverlapExcess n w S =
      (goldbachWindowPairOverlapCount n w S -
        goldbachWindowTripleOverlapCount n w S) +
        goldbachWindowQuadrupleOverlapCount n w S := by
  unfold goldbachWindowOverlapExcess goldbachWindowPairOverlapCount
    goldbachWindowTripleOverlapCount goldbachWindowQuadrupleOverlapCount
  calc
    (∑ t ∈ goldbachBalancedOffsets n w,
        goldbachWindowLocalOverlapExcess n w S t) =
        ∑ t ∈ goldbachBalancedOffsets n w,
          ((goldbachWindowLocalPairMultiplicity n w S t -
            goldbachWindowLocalTripleMultiplicity n w S t) +
            goldbachWindowLocalQuadrupleMultiplicity n w S t) := by
      apply Finset.sum_congr rfl
      intro t ht
      exact goldbachWindowLocalOverlapExcess_eq_pair_sub_triple_add_quadruple
        (hsupport4 t ht)
    _ = (∑ t ∈ goldbachBalancedOffsets n w,
        (goldbachWindowLocalPairMultiplicity n w S t -
          goldbachWindowLocalTripleMultiplicity n w S t)) +
        ∑ t ∈ goldbachBalancedOffsets n w,
          goldbachWindowLocalQuadrupleMultiplicity n w S t := by
      rw [Finset.sum_add_distrib]
    _ = (∑ t ∈ goldbachBalancedOffsets n w,
        goldbachWindowLocalPairMultiplicity n w S t) -
          ∑ t ∈ goldbachBalancedOffsets n w,
            goldbachWindowLocalTripleMultiplicity n w S t +
        ∑ t ∈ goldbachBalancedOffsets n w,
          goldbachWindowLocalQuadrupleMultiplicity n w S t := by
      have hpair : ∀ t ∈ goldbachBalancedOffsets n w,
          goldbachWindowLocalTripleMultiplicity n w S t ≤
            goldbachWindowLocalPairMultiplicity n w S t := by
        intro t ht
        let k := (goldbachObstructionSupportIn n t S).card
        have hk : k ≤ 4 := hsupport4 t ht
        change Nat.choose k 3 ≤ Nat.choose k 2
        interval_cases k <;> decide
      have hsum_le :
          (∑ t ∈ goldbachBalancedOffsets n w,
            goldbachWindowLocalTripleMultiplicity n w S t) ≤
            ∑ t ∈ goldbachBalancedOffsets n w,
              goldbachWindowLocalPairMultiplicity n w S t := by
        apply Finset.sum_le_sum
        intro t ht
        exact hpair t ht
      have hleft :
          (∑ t ∈ goldbachBalancedOffsets n w,
            (goldbachWindowLocalPairMultiplicity n w S t -
              goldbachWindowLocalTripleMultiplicity n w S t)) +
            ∑ t ∈ goldbachBalancedOffsets n w,
              goldbachWindowLocalTripleMultiplicity n w S t =
            ∑ t ∈ goldbachBalancedOffsets n w,
              goldbachWindowLocalPairMultiplicity n w S t := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro t ht
        exact Nat.sub_add_cancel (hpair t ht)
      have hright :
          ((∑ t ∈ goldbachBalancedOffsets n w,
            goldbachWindowLocalPairMultiplicity n w S t) -
            ∑ t ∈ goldbachBalancedOffsets n w,
              goldbachWindowLocalTripleMultiplicity n w S t) +
            ∑ t ∈ goldbachBalancedOffsets n w,
              goldbachWindowLocalTripleMultiplicity n w S t =
            ∑ t ∈ goldbachBalancedOffsets n w,
              goldbachWindowLocalPairMultiplicity n w S t :=
        Nat.sub_add_cancel hsum_le
      have hsum_sub :
          (∑ t ∈ goldbachBalancedOffsets n w,
            (goldbachWindowLocalPairMultiplicity n w S t -
              goldbachWindowLocalTripleMultiplicity n w S t)) =
            (∑ t ∈ goldbachBalancedOffsets n w,
              goldbachWindowLocalPairMultiplicity n w S t) -
              ∑ t ∈ goldbachBalancedOffsets n w,
                goldbachWindowLocalTripleMultiplicity n w S t := by
        omega
      rw [hsum_sub]

/-! ## Fourth signed CRT family -/

/-- Four-element prime subsets of a finite world. -/
def goldbachPrimeQuadruples (S : Finset ℕ) : Finset (Finset ℕ) :=
  S.powersetCard 4

@[simp] theorem mem_goldbachPrimeQuadruples {S Q : Finset ℕ} :
    Q ∈ goldbachPrimeQuadruples S ↔ Q ⊆ S ∧ Q.card = 4 := by
  simp [goldbachPrimeQuadruples]

/-- Canonical representatives of all four signed forbidden classes. -/
def signedQuadrupleResidues (n : ℕ) (Q : Finset ℕ) : Finset ℕ :=
  (Finset.range (Q.prod id)).filter (fun t =>
    ∀ r ∈ Q, (t : ZMod r) ∈ goldbachForbiddenResidues n r)

@[simp] theorem mem_signedQuadrupleResidues {n t : ℕ} {Q : Finset ℕ} :
    t ∈ signedQuadrupleResidues n Q ↔
      t < Q.prod id ∧ ∀ r ∈ Q,
        (t : ZMod r) ∈ goldbachForbiddenResidues n r := by
  simp [signedQuadrupleResidues]

private theorem natCast_mod_prod_eq {t r : ℕ} {Q : Finset ℕ} (hr : r ∈ Q) :
    ((t % Q.prod id : ℕ) : ZMod r) = (t : ZMod r) := by
  apply (ZMod.natCast_eq_natCast_iff' (t % Q.prod id) t r).mpr
  exact Nat.mod_mod_of_dvd t (Finset.dvd_prod_of_mem (fun q : ℕ => q) hr)

/-- Seats carrying every obstruction in a four-element prime subset. -/
def goldbachWindowQuadrupleSupportSeats
    (n w : ℕ) (S Q : Finset ℕ) : Finset ℕ :=
  (goldbachBalancedOffsets n w).filter (fun t =>
    ∀ r ∈ Q, r ∈ goldbachObstructionSupportIn n t S)

@[simp] theorem mem_goldbachWindowQuadrupleSupportSeats
    {n w : ℕ} {S Q : Finset ℕ} {t : ℕ} :
    t ∈ goldbachWindowQuadrupleSupportSeats n w S Q ↔
      t ∈ goldbachBalancedOffsets n w ∧
        ∀ r ∈ Q, r ∈ goldbachObstructionSupportIn n t S := by
  simp [goldbachWindowQuadrupleSupportSeats]

/-- The progression lift of one four-element signed CRT family. -/
def goldbachSignedQuadrupleCRTCount
    (n w : ℕ) (Q : Finset ℕ) : ℕ :=
  ∑ t₀ ∈ signedQuadrupleResidues n Q,
    goldbachProgressionWindowCount (min (n - 2) w) t₀ (Q.prod id)

theorem goldbach_signed_quadruple_count_eq_progression_sum
    {n w : ℕ} {Q : Finset ℕ} (hM : 0 < Q.prod id) :
    goldbachSignedQuadrupleCRTCount n w Q =
      ∑ t₀ ∈ signedQuadrupleResidues n Q,
        (goldbachProgressionSeats (min (n - 2) w) t₀ (Q.prod id)).card := by
  unfold goldbachSignedQuadrupleCRTCount
  apply Finset.sum_congr rfl
  intro t₀ ht₀
  exact goldbachProgressionWindowCount_eq_card hM

/-- Exact quadruple CRT count for one four-element prime subset. -/
theorem goldbachSignedQuadrupleCRTCount_eq_supportSeats_card
    {n w P : ℕ} {S Q : Finset ℕ}
    (hn : 2 ≤ n) (hS : KnownPrimeScales S)
    (hbound : ∀ ⦃r : ℕ⦄, r ∈ S → r ≤ P) (hanchor : P < n - w)
    (hQ : Q ∈ goldbachPrimeQuadruples S) :
    goldbachSignedQuadrupleCRTCount n w Q =
      (goldbachWindowQuadrupleSupportSeats n w S Q).card := by
  classical
  have hQ' := mem_goldbachPrimeQuadruples.mp hQ
  have hprime : ∀ r ∈ Q, Nat.Prime r := fun r hr => hS (hQ'.1 hr)
  have hM : 0 < Q.prod id := Finset.prod_pos (fun r hr => (hprime r hr).pos)
  let A := signedQuadrupleResidues n Q
  let L := A.sigma (fun t₀ =>
    goldbachProgressionSeats (min (n - 2) w) t₀ (Q.prod id))
  let B := goldbachWindowQuadrupleSupportSeats n w S Q
  have hcount : goldbachSignedQuadrupleCRTCount n w Q = L.card := by
    calc
      goldbachSignedQuadrupleCRTCount n w Q =
          ∑ t₀ ∈ A,
            (goldbachProgressionSeats (min (n - 2) w) t₀ (Q.prod id)).card := by
        simpa [A] using goldbach_signed_quadruple_count_eq_progression_sum hM
      _ = L.card := by simp [L, Finset.card_sigma]
  have hLB : L.card ≤ B.card := by
    let f : (Σ _ : ℕ, ℕ) → ℕ := Sigma.snd
    have hfmem : ∀ z ∈ L, f z ∈ B := by
      intro z hz
      rcases z with ⟨t₀, t⟩
      rcases Finset.mem_sigma.mp hz with ⟨ht₀, ht⟩
      change t₀ ∈ A at ht₀
      change t ∈ goldbachProgressionSeats (min (n - 2) w) t₀ (Q.prod id) at ht
      have ht₀' := mem_signedQuadrupleResidues.mp ht₀
      have hprog := (mem_goldbachProgressionSeats_iff_balanced_modEq
        hn hM ht₀'.1).mp ht
      have hsupport : ∀ r ∈ Q, r ∈ goldbachObstructionSupportIn n t S := by
        intro r hr
        have hres : (t : ZMod r) ∈ goldbachForbiddenResidues n r := by
          have hmod := natCast_mod_prod_eq (Q := Q) (t := t) hr
          rw [← hmod, hprog.2]
          exact ht₀'.2 r hr
        exact (goldbach_signed_pair_raw_iff_support hS hbound hanchor
          hprog.1 (hQ'.1 hr)).mp hres
      exact mem_goldbachWindowQuadrupleSupportSeats.mpr ⟨hprog.1, hsupport⟩
    have hfinj : Set.InjOn f (L : Set (Σ _ : ℕ, ℕ)) := by
      intro z hz z' hz' heq
      rcases z with ⟨t₀, t⟩
      rcases z' with ⟨u₀, u⟩
      dsimp [f] at heq
      have htu : t = u := by simpa using heq
      subst u
      have ht₀' := mem_signedQuadrupleResidues.mp
        (Finset.mem_sigma.mp hz).1
      have hu₀' := mem_signedQuadrupleResidues.mp
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
      have ht' := mem_goldbachWindowQuadrupleSupportSeats.mp ht
      have hsupport := ht'.2
      have hres : ∀ r ∈ Q, (t : ZMod r) ∈ goldbachForbiddenResidues n r := by
        intro r hr
        exact (goldbach_signed_pair_raw_iff_support hS hbound hanchor
          ht'.1 (hQ'.1 hr)).mpr (hsupport r hr)
      dsimp [g]
      change (⟨t % Q.prod id, t⟩ : (Σ _ : ℕ, ℕ)) ∈ L
      dsimp [L, A]
      rw [Finset.mem_sigma]
      constructor
      · exact mem_signedQuadrupleResidues.mpr ⟨Nat.mod_lt t hM, by
          intro r hr
          have hmod := natCast_mod_prod_eq (Q := Q) (t := t) hr
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

/-! ## Global quadruple double count -/

/-- Sum of exact quadruple CRT counts over the four-element world subsets. -/
def goldbachSignedQuadrupleCRTSum (n w : ℕ) (S : Finset ℕ) : ℕ :=
  ∑ Q ∈ goldbachPrimeQuadruples S,
    goldbachSignedQuadrupleCRTCount n w Q

theorem goldbachSignedQuadrupleCRTSum_eq_windowQuadrupleOverlapCount
    {n w P : ℕ} {S : Finset ℕ}
    (hn : 2 ≤ n) (hS : KnownPrimeScales S)
    (hbound : ∀ ⦃r : ℕ⦄, r ∈ S → r ≤ P) (hanchor : P < n - w) :
    goldbachSignedQuadrupleCRTSum n w S =
      goldbachWindowQuadrupleOverlapCount n w S := by
  classical
  let U := goldbachPrimeQuadruples S
  have hset (t : ℕ) :
      U.filter (fun Q => ∀ r ∈ Q,
        r ∈ goldbachObstructionSupportIn n t S) =
        (goldbachObstructionSupportIn n t S).powersetCard 4 := by
    ext Q
    constructor
    · intro h
      have h' := Finset.mem_filter.mp h
      have hQ := mem_goldbachPrimeQuadruples.mp h'.1
      apply Finset.mem_powersetCard.mpr
      exact ⟨fun r hr => h'.2 r hr, hQ.2⟩
    · intro h
      have hQ := Finset.mem_powersetCard.mp h
      apply Finset.mem_filter.mpr
      constructor
      · exact mem_goldbachPrimeQuadruples.mpr
          ⟨Finset.Subset.trans hQ.1 (Finset.filter_subset _ _), hQ.2⟩
      · exact hQ.1
  calc
    goldbachSignedQuadrupleCRTSum n w S =
        ∑ Q ∈ U, (goldbachWindowQuadrupleSupportSeats n w S Q).card := by
      apply Finset.sum_congr rfl
      intro Q hQ
      exact goldbachSignedQuadrupleCRTCount_eq_supportSeats_card
        hn hS hbound hanchor hQ
    _ = ∑ Q ∈ U, ∑ t ∈ goldbachBalancedOffsets n w,
          if (∀ r ∈ Q, r ∈ goldbachObstructionSupportIn n t S) then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro Q hQ
      unfold goldbachWindowQuadrupleSupportSeats
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
          ((goldbachObstructionSupportIn n t S).powersetCard 4).card := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [hset]
    _ = goldbachWindowQuadrupleOverlapCount n w S := by
      unfold goldbachWindowQuadrupleOverlapCount
        goldbachWindowLocalQuadrupleMultiplicity
      apply Finset.sum_congr rfl
      intro t ht
      rw [Finset.card_powersetCard]

/-! ## Bounded four-layer provider -/

/-- The exact four-layer payment supplies a survivor under the visible
support-size bound. -/
theorem goldbachWindowSurvivor_of_exact_signed_crt_quadruple_budget
    {n w P : ℕ} {S : Finset ℕ}
    (hn : 2 ≤ n) (hS : KnownPrimeScales S)
    (hbound : ∀ ⦃r : ℕ⦄, r ∈ S → r ≤ P) (hanchor : P < n - w)
    (hsupport4 : ∀ t ∈ goldbachBalancedOffsets n w,
      (goldbachObstructionSupportIn n t S).card ≤ 4)
    (hbudget : goldbachSignedSingleCRTSum n w S <
      (goldbachBalancedOffsets n w).card +
        ((goldbachSignedPairCRTSum n w S -
            goldbachSignedTripleCRTSum n w S) +
          goldbachSignedQuadrupleCRTSum n w S)) :
    (goldbachWindowSurvivors n w S).Nonempty := by
  apply goldbachWindowSurvivor_of_incidence_le_of_overlap_le
    (C := goldbachWindowIncidence n w S)
    (e := (goldbachWindowPairOverlapCount n w S -
      goldbachWindowTripleOverlapCount n w S) +
      goldbachWindowQuadrupleOverlapCount n w S)
  · exact le_rfl
  · rw [goldbachWindowOverlapExcess_eq_pair_sub_triple_add_quadruple
      hsupport4]
  · rw [← goldbachSignedSingleCRTSum_eq_windowIncidence hn hS hbound hanchor,
      ← goldbachSignedPairCRTSum_eq_windowPairOverlapCount hn hS hbound hanchor,
      ← goldbachSignedTripleCRTSum_eq_windowTripleOverlapCount hn hS hbound hanchor,
      ← goldbachSignedQuadrupleCRTSum_eq_windowQuadrupleOverlapCount
        hn hS hbound hanchor]
    exact hbudget

/-- A world of cardinality at most four supplies the bounded four-layer
provider without repeating the local support hypothesis. -/
theorem goldbachWindowSurvivor_of_exact_signed_crt_quadruple_budget_of_world_card_le_four
    {n w P : ℕ} {S : Finset ℕ}
    (hn : 2 ≤ n) (hS : KnownPrimeScales S)
    (hbound : ∀ ⦃r : ℕ⦄, r ∈ S → r ≤ P) (hanchor : P < n - w)
    (hS4 : S.card ≤ 4)
    (hbudget : goldbachSignedSingleCRTSum n w S <
      (goldbachBalancedOffsets n w).card +
        ((goldbachSignedPairCRTSum n w S -
            goldbachSignedTripleCRTSum n w S) +
          goldbachSignedQuadrupleCRTSum n w S)) :
    (goldbachWindowSurvivors n w S).Nonempty := by
  apply goldbachWindowSurvivor_of_exact_signed_crt_quadruple_budget
    hn hS hbound hanchor
    (goldbach_support_card_le_four_of_world_card_le_four hS4)
    hbudget

/-- Anchor-local fixed-target closure for the bounded four-layer provider. -/
theorem goldbachPairAt_of_exact_signed_crt_quadruple_budget
    {n w P : ℕ} (hn : 2 ≤ n) (hw : w ≤ n)
    (hanchor : P < n - w) (hhorizon : n + w ≤ squareBody P)
    (hS4 : (primeScalesUpTo P).card ≤ 4)
    (hbudget : goldbachSignedSingleCRTSum n w (primeScalesUpTo P) <
      (goldbachBalancedOffsets n w).card +
        ((goldbachSignedPairCRTSum n w (primeScalesUpTo P) -
            goldbachSignedTripleCRTSum n w (primeScalesUpTo P)) +
          goldbachSignedQuadrupleCRTSum n w (primeScalesUpTo P))) :
    GoldbachPairAt n := by
  have hsurv :=
    goldbachWindowSurvivor_of_exact_signed_crt_quadruple_budget_of_world_card_le_four
      (n := n) (w := w) (P := P) (S := primeScalesUpTo P) hn
      (knownPrimeScales_primeScalesUpTo P)
      (hbound := fun {_} hr => (mem_primeScalesUpTo.mp hr).2)
      hanchor hS4 hbudget
  obtain ⟨t, ht⟩ := hsurv
  exact goldbachPairAt_of_goldbachWindowSurvivor hw
    (mem_goldbachWindowSurvivors.mp ht).1 hanchor hhorizon
    (mem_goldbachWindowSurvivors.mp ht).2

end DkMath.NumberTheory
