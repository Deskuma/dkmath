/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.CoarseTownSymmetricDeletion
import Mathlib.Logic.Relation

#print "file: DkMath.NumberTheory.Legendre.CoarseTownPrimeHandoff"

/-! Extremal direction handoffs, strict ranks and bounded column continuation. -/
namespace DkMath.NumberTheory.Legendre

open DkMath.Combinatorics DkMath.NumberTheory.Primitive DkMath.NumberTheory.StructuralArithmetic

theorem coarseTownFiberMaximumAt_eq_max' {S : Finset ℕ} {n q a : ℕ}
    (hq : q ∈ coarseFullTownActivePrimes S n) :
    coarseTownFiberMaximumAt S n q a ↔
      a = (coarseFullTownPrimeFiber S n q).max' (mem_coarseFullTownActivePrimes.mp hq).2 := by
  have hF := (mem_coarseFullTownActivePrimes.mp hq).2
  constructor
  · intro h
    have ha := Finset.le_max' (coarseFullTownPrimeFiber S n q) a h.1
    have hb := h.2 ((coarseFullTownPrimeFiber S n q).max' hF) (Finset.max'_mem (coarseFullTownPrimeFiber S n q) hF)
    omega
  · rintro rfl
    exact ⟨Finset.max'_mem (coarseFullTownPrimeFiber S n q) hF,fun b hb => Finset.le_max' (coarseFullTownPrimeFiber S n q) b hb⟩

theorem existsUnique_coarseTownFiberMaximumAt {S : Finset ℕ} {n q : ℕ}
    (hq : q ∈ coarseFullTownActivePrimes S n) : ∃! a, coarseTownFiberMaximumAt S n q a := by
  refine ⟨(coarseFullTownPrimeFiber S n q).max' (mem_coarseFullTownActivePrimes.mp hq).2,?_,?_⟩
  · exact (coarseTownFiberMaximumAt_eq_max' hq).mpr rfl
  · intro a ha
    exact (coarseTownFiberMaximumAt_eq_max' hq).mp ha

theorem coarseTownMax_represented_iff_retained {S : Finset ℕ} {n q a : ℕ}
    (ha : coarseTownFiberMaximumAt S n q a) :
    q ∈ coarseTownRepresentedPrimes S n ↔ a ∈ coarseTownPackingRemainder S n := by
  constructor
  · intro hq
    obtain ⟨b,hb,hqb⟩ := Finset.mem_biUnion.mp hq
    have hm := (mem_coarseTownPackingRemainder_iff_maxima
      (coarseTownPackingRemainder_subset S n hb)).mp hb q hqb
    have hba := ha.2 b (Finset.mem_filter.mpr ⟨coarseTownPackingRemainder_subset S n hb,hqb⟩)
    have hab := hm.2 a ha.1
    have he : a = b := by omega
    rwa [he]
  · intro hr
    exact Finset.mem_biUnion.mpr ⟨a,hr,(Finset.mem_filter.mp ha.1).2⟩

theorem coarseTownMax_unrepresented_iff_deleted {S : Finset ℕ} {n q a : ℕ}
    (hq : q ∈ coarseFullTownActivePrimes S n) (ha : coarseTownFiberMaximumAt S n q a) :
    q ∈ coarseTownUnrepresentedActivePrimes S n ↔ a ∈ coarseTownDeletionVertices S n := by
  have hav := (Finset.mem_filter.mp ha.1).1
  unfold coarseTownUnrepresentedActivePrimes
  rw [Finset.mem_sdiff,coarseTownMax_represented_iff_retained ha]
  rw [mem_coarseTownPackingRemainder]
  simp only [hq,hav,true_and,not_not]

/-- Both vertices are active; the source endpoint is a nonextremal seat of the destination. -/
def coarseTownMaxHandoff (S : Finset ℕ) (n q p : ℕ) : Prop :=
  q ∈ coarseFullTownActivePrimes S n ∧ p ∈ coarseFullTownActivePrimes S n ∧
    ∃ a, coarseTownFiberMaximumAt S n q a ∧ a ∈ coarseTownNonmaximumFiberSeats S n p

theorem coarseTownMaxHandoff_active {S : Finset ℕ} {n q p : ℕ}
    (h : coarseTownMaxHandoff S n q p) :
    q ∈ coarseFullTownActivePrimes S n ∧ p ∈ coarseFullTownActivePrimes S n := ⟨h.1,h.2.1⟩

theorem coarseTownMaxHandoff_rank {S : Finset ℕ} {n q p : ℕ}
    (hq : q ∈ coarseFullTownActivePrimes S n) (hp : p ∈ coarseFullTownActivePrimes S n)
    (h : coarseTownMaxHandoff S n q p) :
    (coarseFullTownPrimeFiber S n q).max' (mem_coarseFullTownActivePrimes.mp hq).2 < (coarseFullTownPrimeFiber S n p).max' (mem_coarseFullTownActivePrimes.mp hp).2 := by
  obtain ⟨a,ha,hn⟩ := h.2.2
  obtain ⟨_haf,b,hb,hlt⟩ := mem_coarseTownNonmaximumFiberSeats.mp hn
  have he := (coarseTownFiberMaximumAt_eq_max' hq).mp ha
  have hbnd := Finset.le_max' (coarseFullTownPrimeFiber S n p) b hb
  omega

theorem coarseTownMaxHandoff_ne {S : Finset ℕ} {n q p : ℕ}
    (h : coarseTownMaxHandoff S n q p) : q ≠ p := by
  intro he
  subst p
  have hr := coarseTownMaxHandoff_rank h.1 h.2.1 h
  exact (Nat.lt_irrefl _) hr

theorem coarseTownMaxHandoff_no_two_cycle {S : Finset ℕ} {n q p : ℕ}
    (h : coarseTownMaxHandoff S n q p) : ¬ coarseTownMaxHandoff S n p q := by
  intro hr
  have h1 := coarseTownMaxHandoff_rank h.1 h.2.1 h
  have h2 := coarseTownMaxHandoff_rank h.2.1 h.1 hr
  omega

theorem coarseTownMax_unrepresented_iff_outgoing {S : Finset ℕ} (hS : KnownPrimeScales S)
    {n q : ℕ} (hq : q ∈ coarseFullTownActivePrimes S n) :
    q ∈ coarseTownUnrepresentedActivePrimes S n ↔ ∃ p, coarseTownMaxHandoff S n q p := by
  obtain ⟨a,ha,_hu⟩ := existsUnique_coarseTownFiberMaximumAt hq
  rw [coarseTownMax_unrepresented_iff_deleted hq ha,
    mem_coarseTownDeletionVertices_iff_multiplicity_pos hS]
  constructor
  · intro hm
    obtain ⟨p,hp⟩ := Finset.card_pos.mp hm
    have ht := Finset.mem_filter.mp hp
    have haf := (mem_coarseTownNonmaximumFiberSeats.mp ht.2).1
    have hpA : p ∈ coarseFullTownActivePrimes S n :=
      mem_coarseFullTownActivePrimes.mpr ⟨ht.1,a,haf⟩
    exact ⟨p,hq,hpA,a,ha,ht.2⟩
  · rintro ⟨p,_hq,hp,b,hb,hn⟩
    have hea := (coarseTownFiberMaximumAt_eq_max' hq).mp ha
    have heb := (coarseTownFiberMaximumAt_eq_max' hq).mp hb
    have he : b = a := heb.trans hea.symm
    rw [he] at hn
    apply Finset.card_pos.mpr
    exact ⟨p,Finset.mem_filter.mpr ⟨(mem_coarseFullTownActivePrimes.mp hp).1,hn⟩⟩

theorem coarseTownMax_represented_iff_terminal {S : Finset ℕ} (hS : KnownPrimeScales S)
    {n q : ℕ} (hq : q ∈ coarseFullTownActivePrimes S n) :
    q ∈ coarseTownRepresentedPrimes S n ↔ ¬ ∃ p, coarseTownMaxHandoff S n q p := by
  have h := coarseTownMax_unrepresented_iff_outgoing hS hq
  unfold coarseTownUnrepresentedActivePrimes at h
  rw [Finset.mem_sdiff] at h
  tauto

theorem coarseTownFiberMinimumAt_eq_min' {S : Finset ℕ} {n q a : ℕ}
    (hq : q ∈ coarseFullTownActivePrimes S n) :
    coarseTownFiberMinimumAt S n q a ↔
      a = (coarseFullTownPrimeFiber S n q).min' (mem_coarseFullTownActivePrimes.mp hq).2 := by
  have hF := (mem_coarseFullTownActivePrimes.mp hq).2
  constructor
  · intro h
    have ha := Finset.min'_le (coarseFullTownPrimeFiber S n q) a h.1
    have hb := h.2 ((coarseFullTownPrimeFiber S n q).min' hF) (Finset.min'_mem (coarseFullTownPrimeFiber S n q) hF)
    omega
  · rintro rfl
    exact ⟨Finset.min'_mem (coarseFullTownPrimeFiber S n q) hF,fun b hb => Finset.min'_le (coarseFullTownPrimeFiber S n q) b hb⟩

theorem existsUnique_coarseTownFiberMinimumAt {S : Finset ℕ} {n q : ℕ}
    (hq : q ∈ coarseFullTownActivePrimes S n) : ∃! a, coarseTownFiberMinimumAt S n q a := by
  refine ⟨(coarseFullTownPrimeFiber S n q).min' (mem_coarseFullTownActivePrimes.mp hq).2,?_,?_⟩
  · exact (coarseTownFiberMinimumAt_eq_min' hq).mpr rfl
  · intro a ha
    exact (coarseTownFiberMinimumAt_eq_min' hq).mp ha

theorem coarseTownMin_represented_iff_retained {S : Finset ℕ} {n q a : ℕ}
    (ha : coarseTownFiberMinimumAt S n q a) :
    q ∈ coarseTownRightRepresentedPrimes S n ↔ a ∈ coarseTownRightPackingRemainder S n := by
  constructor
  · intro hq
    obtain ⟨b,hb,hqb⟩ := Finset.mem_biUnion.mp hq
    have hm := (mem_coarseTownRightPackingRemainder_iff_minima
      (coarseTownRightPackingRemainder_subset S n hb)).mp hb q hqb
    have hba := ha.2 b (Finset.mem_filter.mpr ⟨coarseTownRightPackingRemainder_subset S n hb,hqb⟩)
    have hab := hm.2 a ha.1
    have he : a = b := by omega
    rwa [he]
  · intro hr
    exact Finset.mem_biUnion.mpr ⟨a,hr,(Finset.mem_filter.mp ha.1).2⟩

theorem coarseTownMin_unrepresented_iff_deleted {S : Finset ℕ} {n q a : ℕ}
    (hq : q ∈ coarseFullTownActivePrimes S n) (ha : coarseTownFiberMinimumAt S n q a) :
    q ∈ coarseTownRightUnrepresentedActivePrimes S n ↔ a ∈ coarseTownRightDeletionVertices S n := by
  have hav := (Finset.mem_filter.mp ha.1).1
  unfold coarseTownRightUnrepresentedActivePrimes
  rw [Finset.mem_sdiff,coarseTownMin_represented_iff_retained ha]
  rw [mem_coarseTownRightPackingRemainder]
  simp only [hq,hav,true_and,not_not]

/-- Both vertices are active; the source endpoint is a nonextremal seat of the destination. -/
def coarseTownMinHandoff (S : Finset ℕ) (n q p : ℕ) : Prop :=
  q ∈ coarseFullTownActivePrimes S n ∧ p ∈ coarseFullTownActivePrimes S n ∧
    ∃ a, coarseTownFiberMinimumAt S n q a ∧ a ∈ coarseTownNonminimumFiberSeats S n p

theorem coarseTownMinHandoff_active {S : Finset ℕ} {n q p : ℕ}
    (h : coarseTownMinHandoff S n q p) :
    q ∈ coarseFullTownActivePrimes S n ∧ p ∈ coarseFullTownActivePrimes S n := ⟨h.1,h.2.1⟩

theorem coarseTownMinHandoff_rank {S : Finset ℕ} {n q p : ℕ}
    (hq : q ∈ coarseFullTownActivePrimes S n) (hp : p ∈ coarseFullTownActivePrimes S n)
    (h : coarseTownMinHandoff S n q p) :
    (coarseFullTownPrimeFiber S n p).min' (mem_coarseFullTownActivePrimes.mp hp).2 < (coarseFullTownPrimeFiber S n q).min' (mem_coarseFullTownActivePrimes.mp hq).2 := by
  obtain ⟨a,ha,hn⟩ := h.2.2
  obtain ⟨_haf,b,hb,hlt⟩ := mem_coarseTownNonminimumFiberSeats.mp hn
  have he := (coarseTownFiberMinimumAt_eq_min' hq).mp ha
  have hbnd := Finset.min'_le (coarseFullTownPrimeFiber S n p) b hb
  omega

theorem coarseTownMinHandoff_ne {S : Finset ℕ} {n q p : ℕ}
    (h : coarseTownMinHandoff S n q p) : q ≠ p := by
  intro he
  subst p
  have hr := coarseTownMinHandoff_rank h.1 h.2.1 h
  exact (Nat.lt_irrefl _) hr

theorem coarseTownMinHandoff_no_two_cycle {S : Finset ℕ} {n q p : ℕ}
    (h : coarseTownMinHandoff S n q p) : ¬ coarseTownMinHandoff S n p q := by
  intro hr
  have h1 := coarseTownMinHandoff_rank h.1 h.2.1 h
  have h2 := coarseTownMinHandoff_rank h.2.1 h.1 hr
  omega

theorem coarseTownMin_unrepresented_iff_outgoing {S : Finset ℕ} (hS : KnownPrimeScales S)
    {n q : ℕ} (hq : q ∈ coarseFullTownActivePrimes S n) :
    q ∈ coarseTownRightUnrepresentedActivePrimes S n ↔ ∃ p, coarseTownMinHandoff S n q p := by
  obtain ⟨a,ha,_hu⟩ := existsUnique_coarseTownFiberMinimumAt hq
  rw [coarseTownMin_unrepresented_iff_deleted hq ha,
    mem_coarseTownRightDeletionVertices_iff_multiplicity_pos hS]
  constructor
  · intro hm
    obtain ⟨p,hp⟩ := Finset.card_pos.mp hm
    have ht := Finset.mem_filter.mp hp
    have haf := (mem_coarseTownNonminimumFiberSeats.mp ht.2).1
    have hpA : p ∈ coarseFullTownActivePrimes S n :=
      mem_coarseFullTownActivePrimes.mpr ⟨ht.1,a,haf⟩
    exact ⟨p,hq,hpA,a,ha,ht.2⟩
  · rintro ⟨p,_hq,hp,b,hb,hn⟩
    have hea := (coarseTownFiberMinimumAt_eq_min' hq).mp ha
    have heb := (coarseTownFiberMinimumAt_eq_min' hq).mp hb
    have he : b = a := heb.trans hea.symm
    rw [he] at hn
    apply Finset.card_pos.mpr
    exact ⟨p,Finset.mem_filter.mpr ⟨(mem_coarseFullTownActivePrimes.mp hp).1,hn⟩⟩

theorem coarseTownMin_represented_iff_terminal {S : Finset ℕ} (hS : KnownPrimeScales S)
    {n q : ℕ} (hq : q ∈ coarseFullTownActivePrimes S n) :
    q ∈ coarseTownRightRepresentedPrimes S n ↔ ¬ ∃ p, coarseTownMinHandoff S n q p := by
  have h := coarseTownMin_unrepresented_iff_outgoing hS hq
  unfold coarseTownRightUnrepresentedActivePrimes at h
  rw [Finset.mem_sdiff] at h
  tauto

/-- A continuation repeats p, while the maximal q direction cannot divide its positive gap. -/
theorem coarseTownMaxHandoff_gap_arithmetic {S : Finset ℕ} {n q p a b : ℕ}
    (ha : coarseTownFiberMaximumAt S n q a)
    (hap : a ∈ coarseFullTownPrimeFiber S n p) (hb : b ∈ coarseFullTownPrimeFiber S n p)
    (hab : a < b) :
    p ∣ n ^ 2 + a ∧ p ∣ n ^ 2 + b ∧ p ∣ b - a ∧ 0 < b - a ∧ ¬ q ∣ b - a := by
  have hpa := (mem_squareOffsetPrimeSupport.mp (Finset.mem_filter.mp hap).2).2.2
  have hpb := (mem_squareOffsetPrimeSupport.mp (Finset.mem_filter.mp hb).2).2.2
  have hqa := mem_squareOffsetPrimeSupport.mp (Finset.mem_filter.mp ha.1).2
  have hid : n ^ 2 + b = (n ^ 2 + a) + (b - a) := by omega
  have hpg : p ∣ b - a := (Nat.dvd_add_iff_right hpa).mpr (by rwa [← hid])
  refine ⟨hpa,hpb,hpg,by omega,?_⟩
  intro hqg
  have hqb : q ∣ n ^ 2 + b := by rw [hid]; exact dvd_add hqa.2.2 hqg
  have hbq : b ∈ coarseFullTownPrimeFiber S n q := Finset.mem_filter.mpr
    ⟨(Finset.mem_filter.mp hb).1,mem_squareOffsetPrimeSupport.mpr ⟨hqa.1,hqa.2.1,hqb⟩⟩
  have hle := ha.2 b hbq
  omega

/-- Every max handoff has a genuine positive continuation in production grid coordinates. -/
theorem coarseTownMaxHandoff_grid {S : Finset ℕ} {n q p : ℕ}
    (h : coarseTownMaxHandoff S n q p) :
    ∃ a b r s j k,
      coarseTownFiberMaximumAt S n q a ∧
      a ∈ coarseFullTownPrimeFiber S n p ∧ b ∈ coarseFullTownPrimeFiber S n p ∧ a < b ∧
      r ∈ coarsePrimeWorldBase S n ∧ s ∈ coarsePrimeWorldBase S n ∧
      j < coarsePrimeWorldPeriodCount S n ∧ k < coarsePrimeWorldPeriodCount S n ∧
      r + j * primeWorldModulus S = a ∧ s + k * primeWorldModulus S = b ∧
      (p : ℤ) ∣ ((s : ℤ) - r) + ((k : ℤ) - j) * primeWorldModulus S := by
  obtain ⟨a,ha,hn⟩ := h.2.2
  obtain ⟨hap,b,hb,hab⟩ := mem_coarseTownNonmaximumFiberSeats.mp hn
  obtain ⟨r,hr,j,hj,heja⟩ := mem_coarsePrimeWorldFullTown.mp (Finset.mem_filter.mp hap).1
  obtain ⟨s,hs,k,hk,hekb⟩ := mem_coarsePrimeWorldFullTown.mp (Finset.mem_filter.mp hb).1
  have hpa := (mem_squareOffsetPrimeSupport.mp (Finset.mem_filter.mp hap).2).2.2
  have hpb := (mem_squareOffsetPrimeSupport.mp (Finset.mem_filter.mp hb).2).2.2
  refine ⟨a,b,r,s,j,k,ha,hap,hb,hab,hr,hs,hj,hk,heja,hekb,?_⟩
  apply coarseCrossColumn_commonPrime_signed_gap
  · simpa only [Nat.add_assoc,heja] using hpa
  · simpa only [Nat.add_assoc,hekb] using hpb

/-- Uniform vertical sparsity forces a strict handoff continuation to change base column. -/
theorem coarseTownMaxHandoff_different_columns {S : Finset ℕ} (hS : KnownPrimeScales S)
    {n p a b r s j k : ℕ} (hp : p ∈ coarseOutsidePrimes S n)
    (hK : coarsePrimeWorldPeriodCount S n ≤ p)
    (hap : a ∈ coarseFullTownPrimeFiber S n p) (hbp : b ∈ coarseFullTownPrimeFiber S n p)
    (hab : a < b) (hj : j < coarsePrimeWorldPeriodCount S n)
    (hk : k < coarsePrimeWorldPeriodCount S n)
    (heja : r + j * primeWorldModulus S = a) (hekb : s + k * primeWorldModulus S = b) : r ≠ s := by
  intro he
  subst s
  have hpp := (mem_primeScalesUpTo.mp (Finset.mem_sdiff.mp hp).1).1
  have hpa := (mem_squareOffsetPrimeSupport.mp (Finset.mem_filter.mp hap).2).2.2
  have hpb := (mem_squareOffsetPrimeSupport.mp (Finset.mem_filter.mp hbp).2).2.2
  have hjeq := coarseCrossColumn_compatible_index_unique (s := r) hS hpp (Finset.mem_sdiff.mp hp).2 hK hj hk
    (by simpa only [Nat.add_assoc,heja] using hpa)
    (by simpa only [Nat.add_assoc,hekb] using hpb)
  have habEq : a = b := by rw [← heja,← hekb,hjeq]
  omega

/-- Fixing the destination column and prime fixes the continuation seat, not its source direction. -/
theorem coarseTownHandoff_destination_unique {S : Finset ℕ} (hS : KnownPrimeScales S)
    {n p s k l b c : ℕ} (hp : p ∈ coarseOutsidePrimes S n)
    (hK : coarsePrimeWorldPeriodCount S n ≤ p)
    (hk : k < coarsePrimeWorldPeriodCount S n) (hl : l < coarsePrimeWorldPeriodCount S n)
    (hb : b ∈ coarseFullTownPrimeFiber S n p) (hc : c ∈ coarseFullTownPrimeFiber S n p)
    (hekb : s + k * primeWorldModulus S = b) (helc : s + l * primeWorldModulus S = c) :
    k = l ∧ b = c := by
  have hpp := (mem_primeScalesUpTo.mp (Finset.mem_sdiff.mp hp).1).1
  have hpb := (mem_squareOffsetPrimeSupport.mp (Finset.mem_filter.mp hb).2).2.2
  have hpc := (mem_squareOffsetPrimeSupport.mp (Finset.mem_filter.mp hc).2).2.2
  have he := coarseCrossColumn_compatible_index_unique (s := s) hS hpp (Finset.mem_sdiff.mp hp).2 hK hk hl
    (by simpa only [Nat.add_assoc,hekb] using hpb)
    (by simpa only [Nat.add_assoc,helc] using hpc)
  exact ⟨he,by rw [← hekb,← helc,he]⟩

theorem coarseTownMaxHandoff_product_not_dvd_gap {S : Finset ℕ} {n q p a b : ℕ}
    (ha : coarseTownFiberMaximumAt S n q a)
    (hap : a ∈ coarseFullTownPrimeFiber S n p) (hb : b ∈ coarseFullTownPrimeFiber S n p)
    (hab : a < b) : ¬ p * q ∣ b - a := by
  intro hd
  exact (coarseTownMaxHandoff_gap_arithmetic ha hap hb hab).2.2.2.2
    (dvd_trans (dvd_mul_left q p) hd)

/-- Active subtypes make every rank nonempty without a default endpoint. -/
theorem coarseTownMaxHandoff_chain_rank {S : Finset ℕ} {n : ℕ}
    {q p : {q : ℕ // q ∈ coarseFullTownActivePrimes S n}}
    (h : Relation.TransGen (fun q p : {q : ℕ // q ∈ coarseFullTownActivePrimes S n} =>
      coarseTownMaxHandoff S n q p) q p) :
    (coarseFullTownPrimeFiber S n q).max' (mem_coarseFullTownActivePrimes.mp q.property).2 <
      (coarseFullTownPrimeFiber S n p).max' (mem_coarseFullTownActivePrimes.mp p.property).2 := by
  induction h with
  | single h => exact coarseTownMaxHandoff_rank h.1 h.2.1 h
  | @tail b c _ hbc ih => exact lt_trans ih (coarseTownMaxHandoff_rank b.property c.property hbc)

theorem coarseTownMinHandoff_chain_rank {S : Finset ℕ} {n : ℕ}
    {q p : {q : ℕ // q ∈ coarseFullTownActivePrimes S n}}
    (h : Relation.TransGen (fun q p : {q : ℕ // q ∈ coarseFullTownActivePrimes S n} =>
      coarseTownMinHandoff S n q p) q p) :
    (coarseFullTownPrimeFiber S n p).min' (mem_coarseFullTownActivePrimes.mp p.property).2 <
      (coarseFullTownPrimeFiber S n q).min' (mem_coarseFullTownActivePrimes.mp q.property).2 := by
  induction h with
  | single h => exact coarseTownMinHandoff_rank h.1 h.2.1 h
  | @tail b c _ hbc ih => exact lt_trans (coarseTownMinHandoff_rank b.property c.property hbc) ih

theorem coarseTownMaxHandoff_no_cycle {S : Finset ℕ} {n : ℕ}
    (q : {q : ℕ // q ∈ coarseFullTownActivePrimes S n}) :
    ¬ Relation.TransGen (fun q p : {q : ℕ // q ∈ coarseFullTownActivePrimes S n} =>
      coarseTownMaxHandoff S n q p) q q := by
  intro h
  exact (Nat.lt_irrefl _) (coarseTownMaxHandoff_chain_rank h)

theorem coarseTownMinHandoff_no_cycle {S : Finset ℕ} {n : ℕ}
    (q : {q : ℕ // q ∈ coarseFullTownActivePrimes S n}) :
    ¬ Relation.TransGen (fun q p : {q : ℕ // q ∈ coarseFullTownActivePrimes S n} =>
      coarseTownMinHandoff S n q p) q q := by
  intro h
  exact (Nat.lt_irrefl _) (coarseTownMinHandoff_chain_rank h)

/-- Every better-of-two capacity certificate already forces positive uncovered mass. -/
theorem coarseTownBetter_deficit_implies_uncovered_nonempty {S : Finset ℕ}
    (hS : KnownPrimeScales S) {n : ℕ}
    (h : (coarseOutsidePrimes S n).card < (coarseTownBetterRemainder S n).card) :
    (coarseFullTownUncoveredSeats S n).Nonempty := by
  apply Finset.card_pos.mp
  have hf := (coarseTownBetter_deficit_iff_loss_frontier hS n).mp h
  omega

end DkMath.NumberTheory.Legendre
