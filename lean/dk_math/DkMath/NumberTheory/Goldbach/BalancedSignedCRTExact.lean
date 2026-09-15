/-
Copyright (c) 2026 DkMath contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.NumberTheory.Goldbach.BalancedSignedCRTOverlap
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic

#print "file: DkMath.NumberTheory.Goldbach.BalancedSignedCRTExact"

/-!
# Exact signed CRT / Pascal overlap identification

This module closes the CGE-007 comparison boundary under an explicit finite
prime-world anchor.  All statements are balanced-window and conditional.
-/

namespace DkMath.NumberTheory

open DkMath.NumberTheory.Primitive
open DkMath.NumberTheory.StructuralArithmetic
open scoped BigOperators

/-! ## One progression and one congruence class -/

private theorem mem_progressionSeats_iff_le_and_mod
    {w t₀ M t : ℕ} (hM : 0 < M) (ht₀ : t₀ < M) :
    t ∈ goldbachProgressionSeats w t₀ M ↔
      t ≤ w ∧ t % M = t₀ := by
  classical
  constructor
  · intro ht
    unfold goldbachProgressionSeats at ht
    split at ht
    · next ht₀w =>
        rcases Finset.mem_image.mp ht with ⟨k, hk, rfl⟩
        have hk' : k ≤ (w - t₀) / M := by
          exact Nat.le_of_lt_succ
            (by simpa [Nat.succ_eq_add_one] using (Finset.mem_range.mp hk))
        have hkm : k * M ≤ w - t₀ :=
          (Nat.le_div_iff_mul_le hM).mp hk'
        have hmk : M * k ≤ w - t₀ := by simpa [Nat.mul_comm] using hkm
        constructor
        · omega
        · simp [Nat.add_mod, Nat.mod_eq_of_lt ht₀]
    · simp at ht
  · rintro ⟨htw, hmod⟩
    have hdecomp : t = t % M + M * (t / M) := (Nat.mod_add_div t M).symm
    have ht0 : t₀ + M * (t / M) = t := by
      calc
        t₀ + M * (t / M) = t % M + M * (t / M) := by rw [hmod]
        _ = t := hdecomp.symm
    have hkm : M * (t / M) ≤ w - t₀ := by omega
    have hk' : t / M ≤ (w - t₀) / M := by
      apply (Nat.le_div_iff_mul_le hM).mpr
      simpa [Nat.mul_comm] using hkm
    have hk : t / M < (w - t₀) / M + 1 := by omega
    rw [goldbachProgressionSeats, if_pos (by omega)]
    exact Finset.mem_image.mpr ⟨t / M, Finset.mem_range.mpr hk, ht0⟩

theorem mem_goldbachProgressionSeats_iff_balanced_modEq
    {n w t₀ M t : ℕ} (hn : 2 ≤ n) (hM : 0 < M) (ht₀ : t₀ < M) :
    t ∈ goldbachProgressionSeats (min (n - 2) w) t₀ M ↔
      t ∈ goldbachBalancedOffsets n w ∧ t % M = t₀ := by
  rw [goldbachBalancedOffsets_eq_range]
  constructor
  · intro h
    have h' := mem_progressionSeats_iff_le_and_mod
      (w := min (n - 2) w) (t₀ := t₀) (M := M) (t := t) hM ht₀ |>.mp h
    have hle : t ≤ min (n - 2) w := by
      by_cases hn : n - 2 ≤ w
      · rw [Nat.min_eq_left hn]
        omega
      · rw [Nat.min_eq_right (Nat.le_of_not_ge hn)]
        omega
    refine ⟨?_, h'.2⟩
    simp only [Finset.mem_range]
    rw [lt_min_iff]
    constructor
    · have hle' : t ≤ n - 2 := le_trans hle (min_le_left _ _)
      omega
    · have hle' : t ≤ w := le_trans hle (min_le_right _ _)
      exact Nat.lt_succ_of_le hle'
  · rintro ⟨ht, hmod⟩
    apply (mem_progressionSeats_iff_le_and_mod
      (w := min (n - 2) w) (t₀ := t₀) (M := M) (t := t) hM ht₀
    ).mpr
    refine ⟨?_, hmod⟩
    simp only [Finset.mem_range] at ht
    rw [le_min_iff]
    constructor
    · have ht' : t < n - 1 := lt_of_lt_of_le ht (min_le_left _ _)
      omega
    · have ht' : t < w + 1 := lt_of_lt_of_le ht (min_le_right _ _)
      omega

private theorem natCast_mod_mul_eq_left
    {p q t : ℕ} (_hp : 0 < p) (_hq : 0 < q) :
    ((t % (p * q) : ℕ) : ZMod p) = (t : ZMod p) := by
  apply (ZMod.natCast_eq_natCast_iff' (t % (p * q)) t p).mpr
  exact Nat.mod_mod_of_dvd t ⟨q, rfl⟩

private theorem natCast_mod_mul_eq_right
    {p q t : ℕ} (_hp : 0 < p) (_hq : 0 < q) :
    ((t % (p * q) : ℕ) : ZMod q) = (t : ZMod q) := by
  apply (ZMod.natCast_eq_natCast_iff' (t % (p * q)) t q).mpr
  exact Nat.mod_mod_of_dvd t ⟨p, by simp [Nat.mul_comm]⟩

private theorem natCast_mod_triple_eq_left
    {p q r t : ℕ} (_hp : 0 < p) (_hq : 0 < q) (_hr : 0 < r) :
    ((t % (p * q * r) : ℕ) : ZMod p) = (t : ZMod p) := by
  apply (ZMod.natCast_eq_natCast_iff' (t % (p * q * r)) t p).mpr
  exact Nat.mod_mod_of_dvd t ⟨q * r, by ring⟩

private theorem natCast_mod_triple_eq_middle
    {p q r t : ℕ} (_hp : 0 < p) (_hq : 0 < q) (_hr : 0 < r) :
    ((t % (p * q * r) : ℕ) : ZMod q) = (t : ZMod q) := by
  apply (ZMod.natCast_eq_natCast_iff' (t % (p * q * r)) t q).mpr
  exact Nat.mod_mod_of_dvd t ⟨p * r, by ring⟩

private theorem natCast_mod_triple_eq_right
    {p q r t : ℕ} (_hp : 0 < p) (_hq : 0 < q) (_hr : 0 < r) :
    ((t % (p * q * r) : ℕ) : ZMod r) = (t : ZMod r) := by
  apply (ZMod.natCast_eq_natCast_iff' (t % (p * q * r)) t r).mpr
  exact Nat.mod_mod_of_dvd t ⟨p * q, by ring⟩

private def goldbachSupportUpperPairs (s : Finset ℕ) : Finset (ℕ × ℕ) :=
  s.offDiag.filter (fun pair => pair.1 < pair.2)

private def goldbachSupportLowerPairs (s : Finset ℕ) : Finset (ℕ × ℕ) :=
  s.offDiag.filter (fun pair => pair.2 < pair.1)

private theorem goldbach_card_supportUpperPairs_eq_choose (s : Finset ℕ) :
    (goldbachSupportUpperPairs s).card = Nat.choose s.card 2 := by
  classical
  have hswap : (goldbachSupportLowerPairs s).card =
      (goldbachSupportUpperPairs s).card := by
    apply Finset.card_bij (fun pair _ => (pair.2, pair.1))
    · intro pair hpair
      have hpair' := Finset.mem_filter.mp hpair
      have hdiag := Finset.mem_offDiag.mp hpair'.1
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_offDiag.mpr
          ⟨hdiag.2.1, hdiag.1, Ne.symm hdiag.2.2⟩, hpair'.2⟩
    · intro pair₁ hpair₁ pair₂ hpair₂ heq
      exact Prod.ext (congrArg Prod.snd heq) (congrArg Prod.fst heq)
    · intro pair hpair
      refine ⟨(pair.2, pair.1), ?_, ?_⟩
      · have hpair' := Finset.mem_filter.mp hpair
        have hdiag := Finset.mem_offDiag.mp hpair'.1
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_offDiag.mpr
            ⟨hdiag.2.1, hdiag.1, Ne.symm hdiag.2.2⟩, hpair'.2⟩
      · rfl
  have hneg : s.offDiag.filter (fun pair => ¬ pair.1 < pair.2) =
      goldbachSupportLowerPairs s := by
    ext pair
    simp [goldbachSupportLowerPairs]
    omega
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := s.offDiag) (p := fun pair : ℕ × ℕ => pair.1 < pair.2)
  rw [hneg] at hsplit
  have hsum : (goldbachSupportUpperPairs s).card +
      (goldbachSupportLowerPairs s).card = s.offDiag.card := by
    simpa [goldbachSupportUpperPairs] using hsplit
  have htwice : 2 * (goldbachSupportUpperPairs s).card = s.offDiag.card := by
    omega
  rw [Nat.choose_two_right, Nat.mul_sub_left_distrib, mul_one,
    ← Finset.offDiag_card]
  exact (Nat.div_eq_of_eq_mul_right Nat.zero_lt_two htwice.symm).symm

private def goldbachSupportUpperTriples (s : Finset ℕ) :
    Finset (ℕ × ℕ × ℕ) :=
  (s.product (s.product s)).filter (fun triple =>
    triple.1 < triple.2.1 ∧ triple.2.1 < triple.2.2)

private theorem goldbach_card_supportUpperTriples_eq_choose (s : Finset ℕ) :
    (goldbachSupportUpperTriples s).card = Nat.choose s.card 3 := by
  classical
  let f : (ℕ × ℕ × ℕ) → Finset ℕ :=
    fun triple => {triple.1, triple.2.1, triple.2.2}
  have hmem : ∀ triple ∈ goldbachSupportUpperTriples s,
      f triple ∈ s.powersetCard 3 := by
    intro triple htriple
    have htriple' := Finset.mem_filter.mp htriple
    have hprod := Finset.mem_product.mp htriple'.1
    have hprod' := Finset.mem_product.mp hprod.2
    apply Finset.mem_powersetCard.mpr
    constructor
    · intro x hx
      rcases Finset.mem_insert.mp hx with hxa | hxbc
      · subst x
        exact hprod.1
      · rcases Finset.mem_insert.mp hxbc with hxb | hxc
        · subst x
          exact hprod'.1
        · exact Finset.mem_singleton.mp hxc ▸ hprod'.2
    · apply (Finset.card_triple_eq_three_iff).mpr
      exact ⟨ne_of_lt htriple'.2.1,
        ne_of_lt (lt_trans htriple'.2.1 htriple'.2.2),
        ne_of_lt htriple'.2.2⟩
  have hinj : Set.InjOn f
      (goldbachSupportUpperTriples s : Set (ℕ × ℕ × ℕ)) := by
    intro triple htriple triple' htriple' heq
    rcases triple with ⟨a, b, c⟩
    rcases triple' with ⟨x, y, z⟩
    have h₁ := Finset.mem_filter.mp htriple
    have h₂ := Finset.mem_filter.mp htriple'
    have hab : a < b := h₁.2.1
    have hbc : b < c := h₁.2.2
    have hxy : x < y := h₂.2.1
    have hyz : y < z := h₂.2.2
    have ha : a ∈ ({x, y, z} : Finset ℕ) := by
      have ha' : a ∈ f (a, b, c) := by simp [f]
      rw [heq] at ha'
      exact ha'
    have hb : b ∈ ({x, y, z} : Finset ℕ) := by
      have hb' : b ∈ f (a, b, c) := by simp [f]
      rw [heq] at hb'
      exact hb'
    have hc : c ∈ ({x, y, z} : Finset ℕ) := by
      have hc' : c ∈ f (a, b, c) := by simp [f]
      rw [heq] at hc'
      exact hc'
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb hc
    rcases ha with rfl | rfl | rfl <;>
      rcases hb with rfl | rfl | rfl <;>
        rcases hc with rfl | rfl | rfl <;>
          all_goals simp_all only [Prod.mk.injEq]
    all_goals omega
  have hex : ∀ u ∈ s.powersetCard 3, ∃ triple,
      triple ∈ goldbachSupportUpperTriples s ∧ f triple = u := by
    intro u hu
    have hu' := Finset.mem_powersetCard.mp hu
    obtain ⟨a, b, c, hab, hac, hbc, hs⟩ := Finset.card_eq_three.mp hu'.2
    have ha : a ∈ s := hu'.1 (by rw [hs]; simp)
    have hb : b ∈ s := hu'.1 (by rw [hs]; simp)
    have hc : c ∈ s := hu'.1 (by rw [hs]; simp)
    have horder : (a < b ∧ b < c) ∨ (a < c ∧ c < b) ∨
        (b < a ∧ a < c) ∨ (b < c ∧ c < a) ∨
        (c < a ∧ a < b) ∨ (c < b ∧ b < a) := by omega
    rcases horder with horder | horder | horder | horder | horder | horder
    · refine ⟨(a, b, c), ?_, ?_⟩
      · simp [goldbachSupportUpperTriples, ha, hb, hc, horder.1, horder.2]
      · rw [hs] -- finish    [                        ]
    · refine ⟨(a, c, b), ?_, ?_⟩
      · simp [goldbachSupportUpperTriples, ha, hb, hc, horder.1, horder.2]
      · rw [hs]; ext x; simp [f,               or_comm]
    · refine ⟨(b, a, c), ?_, ?_⟩
      · simp [goldbachSupportUpperTriples, ha, hb, hc, horder.1, horder.2]
      · rw [hs]; ext x; simp [f, or_left_comm         ]
    · refine ⟨(b, c, a), ?_, ?_⟩
      · simp [goldbachSupportUpperTriples, ha, hb, hc, horder.1, horder.2]
      · rw [hs]; ext x; simp [f, or_left_comm, or_comm]
    · refine ⟨(c, a, b), ?_, ?_⟩
      · simp [goldbachSupportUpperTriples, ha, hb, hc, horder.1, horder.2]
      · rw [hs]; ext x; simp [f, or_left_comm, or_comm]
    · refine ⟨(c, b, a), ?_, ?_⟩
      · simp [goldbachSupportUpperTriples, ha, hb, hc, horder.1, horder.2]
      · rw [hs]; ext x; simp [f, or_left_comm, or_comm]
  rw [← Finset.card_powersetCard 3 s]
  apply Finset.card_bij (fun triple _ => f triple)
  · exact hmem
  · intro triple htriple triple' htriple' heq
    exact hinj htriple htriple' heq
  · intro u hu
    exact ⟨Classical.choose (hex u hu),
      (Classical.choose_spec (hex u hu)).1,
      (Classical.choose_spec (hex u hu)).2⟩

/-! ## Exact pair and triple support-seat sets -/

def goldbachWindowPairSupportSeats
    (n w : ℕ) (S : Finset ℕ) (p q : ℕ) : Finset ℕ :=
  (goldbachBalancedOffsets n w).filter (fun t =>
    p ∈ goldbachObstructionSupportIn n t S ∧
      q ∈ goldbachObstructionSupportIn n t S)

@[simp] theorem mem_goldbachWindowPairSupportSeats
    {n w : ℕ} {S : Finset ℕ} {p q t : ℕ} :
    t ∈ goldbachWindowPairSupportSeats n w S p q ↔
      t ∈ goldbachBalancedOffsets n w ∧
        p ∈ goldbachObstructionSupportIn n t S ∧
          q ∈ goldbachObstructionSupportIn n t S := by
  simp [goldbachWindowPairSupportSeats, and_assoc]

def goldbachWindowTripleSupportSeats
    (n w : ℕ) (S : Finset ℕ) (p q r : ℕ) : Finset ℕ :=
  (goldbachBalancedOffsets n w).filter (fun t =>
    p ∈ goldbachObstructionSupportIn n t S ∧
      q ∈ goldbachObstructionSupportIn n t S ∧
        r ∈ goldbachObstructionSupportIn n t S)

@[simp] theorem mem_goldbachWindowTripleSupportSeats
    {n w : ℕ} {S : Finset ℕ} {p q r t : ℕ} :
    t ∈ goldbachWindowTripleSupportSeats n w S p q r ↔
      t ∈ goldbachBalancedOffsets n w ∧
        p ∈ goldbachObstructionSupportIn n t S ∧
          q ∈ goldbachObstructionSupportIn n t S ∧
            r ∈ goldbachObstructionSupportIn n t S := by
  simp [goldbachWindowTripleSupportSeats, and_assoc]

/-! ## Exact pair-seat cardinality -/

theorem goldbachSignedPairCRTCount_eq_pairSupportSeats_card
    {n w P : ℕ} {S : Finset ℕ}
    (hn : 2 ≤ n) (hS : KnownPrimeScales S)
    (hbound : ∀ ⦃r : ℕ⦄, r ∈ S → r ≤ P) (hanchor : P < n - w)
    {p q : ℕ} (hpq : (p, q) ∈ goldbachStrictPrimePairs S) :
    goldbachSignedPairCRTCount n w p q =
      (goldbachWindowPairSupportSeats n w S p q).card := by
  classical
  have hpS := (mem_goldbachStrictPrimePairs.mp hpq).1
  have hqS := (mem_goldbachStrictPrimePairs.mp hpq).2.1
  have hpq_lt := (mem_goldbachStrictPrimePairs.mp hpq).2.2
  have hp : Nat.Prime p := hS hpS
  have hq : Nat.Prime q := hS hqS
  have hp_pos := hp.pos
  have hq_pos := hq.pos
  have hM : 0 < p * q := Nat.mul_pos hp_pos hq_pos
  let A := signedPairResidues n p q
  let L := A.sigma (fun t₀ =>
    goldbachProgressionSeats (min (n - 2) w) t₀ (p * q))
  let B := goldbachWindowPairSupportSeats n w S p q
  have hcount : goldbachSignedPairCRTCount n w p q = L.card := by
    calc
      goldbachSignedPairCRTCount n w p q =
          ∑ t₀ ∈ A,
            (goldbachProgressionSeats (min (n - 2) w) t₀ (p * q)).card := by
        simpa [A] using
          (goldbach_signed_pair_count_eq_progression_sum hM)
      _ = L.card := by
        simp [L, Finset.card_sigma]
  have hLB : L.card ≤ B.card := by
    let f : (Σ _ : ℕ, ℕ) → ℕ := Sigma.snd
    have hfmem : ∀ z ∈ L, f z ∈ B := by
      intro z hz
      rcases z with ⟨t₀, t⟩
      rcases Finset.mem_sigma.mp hz with ⟨ht₀, ht⟩
      change t₀ ∈ A at ht₀
      change t ∈ goldbachProgressionSeats (min (n - 2) w) t₀ (p * q) at ht
      have ht₀' := mem_signedPairResidues.mp ht₀
      have hprog := (mem_goldbachProgressionSeats_iff_balanced_modEq
        hn hM ht₀'.1).mp ht
      have hpt : (t : ZMod p) ∈ goldbachForbiddenResidues n p := by
        have hpm := natCast_mod_mul_eq_left (t := t) hp_pos hq_pos
        rw [← hpm, hprog.2]
        exact ht₀'.2.1
      have hqt : (t : ZMod q) ∈ goldbachForbiddenResidues n q := by
        have hqm := natCast_mod_mul_eq_right (t := t) hp_pos hq_pos
        rw [← hqm, hprog.2]
        exact ht₀'.2.2
      have hps := (goldbach_signed_pair_raw_iff_support hS hbound hanchor
        hprog.1 hpS).mp hpt
      have hqs := (goldbach_signed_pair_raw_iff_support hS hbound hanchor
        hprog.1 hqS).mp hqt
      exact mem_goldbachWindowPairSupportSeats.mpr ⟨hprog.1, hps, hqs⟩
    have hfinj : Set.InjOn f (L : Set (Σ _ : ℕ, ℕ)) := by
      intro z hz z' hz' heq
      rcases z with ⟨t₀, t⟩
      rcases z' with ⟨u₀, u⟩
      dsimp [f] at heq
      have htu : t = u := by simpa using heq
      subst u
      have ht₀' := mem_signedPairResidues.mp
        (Finset.mem_sigma.mp hz).1
      have hu₀' := mem_signedPairResidues.mp
        (Finset.mem_sigma.mp hz').1
      have htp' := (mem_goldbachProgressionSeats_iff_balanced_modEq
        hn hM ht₀'.1).mp (Finset.mem_sigma.mp hz).2
      have hup' := (mem_goldbachProgressionSeats_iff_balanced_modEq
        hn hM hu₀'.1).mp (Finset.mem_sigma.mp hz').2
      have htp : t % (p * q) = t₀ := by simpa using htp'.2
      have hup : t % (p * q) = u₀ := by simpa using hup'.2
      have hidx : t₀ = u₀ := by omega
      subst u₀
      cases htp
      rfl
    exact Finset.card_le_card_of_injOn f hfmem hfinj
  have hBL : B.card ≤ L.card := by
    let g : ℕ → (Σ _ : ℕ, ℕ) := fun t => ⟨t % (p * q), t⟩
    have hgmem : ∀ t ∈ B, g t ∈ L := by
      intro t ht
      have ht' := mem_goldbachWindowPairSupportSeats.mp ht
      have hpt := (goldbach_signed_pair_raw_iff_support hS hbound hanchor
        ht'.1 hpS).mpr ht'.2.1
      have hqt := (goldbach_signed_pair_raw_iff_support hS hbound hanchor
        ht'.1 hqS).mpr ht'.2.2
      have hpm := natCast_mod_mul_eq_left (t := t) hp_pos hq_pos
      have hqm := natCast_mod_mul_eq_right (t := t) hp_pos hq_pos
      have hpt₀ : ((t % (p * q) : ℕ) : ZMod p) ∈
          goldbachForbiddenResidues n p := by
        rw [hpm]
        exact hpt
      have hqt₀ : ((t % (p * q) : ℕ) : ZMod q) ∈
          goldbachForbiddenResidues n q := by
        rw [hqm]
        exact hqt
      apply Finset.mem_sigma.mpr
      refine ⟨mem_signedPairResidues.mpr
        ⟨Nat.mod_lt t hM, hpt₀, hqt₀⟩, ?_⟩
      apply (mem_goldbachProgressionSeats_iff_balanced_modEq
        hn hM (Nat.mod_lt t hM)).mpr
      exact ⟨ht'.1, rfl⟩
    have hginj : Set.InjOn g (B : Set ℕ) := by
      intro t ht u hu heq
      exact congrArg Sigma.snd heq
    exact Finset.card_le_card_of_injOn g hgmem hginj
  have hcard : L.card = B.card := Nat.le_antisymm hLB hBL
  simpa [A, B] using hcount.trans hcard

/-! ## Exact triple-seat cardinality -/

theorem goldbachSignedTripleCRTCount_eq_tripleSupportSeats_card
    {n w P : ℕ} {S : Finset ℕ}
    (hn : 2 ≤ n) (hS : KnownPrimeScales S)
    (hbound : ∀ ⦃r : ℕ⦄, r ∈ S → r ≤ P) (hanchor : P < n - w)
    {p q r : ℕ} (htriple : (p, q, r) ∈ goldbachPrimeTriples S) :
    goldbachSignedTripleCRTCount n w p q r =
      (goldbachWindowTripleSupportSeats n w S p q r).card := by
  classical
  have htriple' := mem_goldbachPrimeTriples.mp htriple
  have hpS := htriple'.1
  have hqS := htriple'.2.1
  have hrS := htriple'.2.2.1
  have hp : Nat.Prime p := hS hpS
  have hq : Nat.Prime q := hS hqS
  have hr : Nat.Prime r := hS hrS
  have hp_pos := hp.pos
  have hq_pos := hq.pos
  have hr_pos := hr.pos
  have hM : 0 < p * q * r :=
    Nat.mul_pos (Nat.mul_pos hp_pos hq_pos) hr_pos
  let A := signedTripleResidues n p q r
  let L := A.sigma (fun t₀ =>
    goldbachProgressionSeats (min (n - 2) w) t₀ (p * q * r))
  let B := goldbachWindowTripleSupportSeats n w S p q r
  have hcount : goldbachSignedTripleCRTCount n w p q r = L.card := by
    calc
      goldbachSignedTripleCRTCount n w p q r =
          ∑ t₀ ∈ A,
            (goldbachProgressionSeats (min (n - 2) w) t₀
              (p * q * r)).card := by
        simpa [A] using
          (goldbach_signed_triple_count_eq_progression_sum hM)
      _ = L.card := by
        simp [L, Finset.card_sigma]
  have hLB : L.card ≤ B.card := by
    let f : (Σ _ : ℕ, ℕ) → ℕ := Sigma.snd
    have hfmem : ∀ z ∈ L, f z ∈ B := by
      intro z hz
      rcases z with ⟨t₀, t⟩
      rcases Finset.mem_sigma.mp hz with ⟨ht₀, ht⟩
      change t₀ ∈ A at ht₀
      change t ∈ goldbachProgressionSeats (min (n - 2) w) t₀
        (p * q * r) at ht
      have ht₀' := mem_signedTripleResidues.mp ht₀
      have hprog := (mem_goldbachProgressionSeats_iff_balanced_modEq
        hn hM ht₀'.1).mp ht
      have hpt : (t : ZMod p) ∈ goldbachForbiddenResidues n p := by
        have hpm := natCast_mod_triple_eq_left
          (t := t) hp_pos hq_pos hr_pos
        rw [← hpm, hprog.2]
        exact ht₀'.2.1
      have hqt : (t : ZMod q) ∈ goldbachForbiddenResidues n q := by
        have hqm := natCast_mod_triple_eq_middle
          (t := t) hp_pos hq_pos hr_pos
        rw [← hqm, hprog.2]
        exact ht₀'.2.2.1
      have hrt : (t : ZMod r) ∈ goldbachForbiddenResidues n r := by
        have hrm := natCast_mod_triple_eq_right
          (t := t) hp_pos hq_pos hr_pos
        rw [← hrm, hprog.2]
        exact ht₀'.2.2.2
      have hps := (goldbach_signed_pair_raw_iff_support hS hbound hanchor
        hprog.1 hpS).mp hpt
      have hqs := (goldbach_signed_pair_raw_iff_support hS hbound hanchor
        hprog.1 hqS).mp hqt
      have hrs := (goldbach_signed_pair_raw_iff_support hS hbound hanchor
        hprog.1 hrS).mp hrt
      exact mem_goldbachWindowTripleSupportSeats.mpr
        ⟨hprog.1, hps, hqs, hrs⟩
    have hfinj : Set.InjOn f (L : Set (Σ _ : ℕ, ℕ)) := by
      intro z hz z' hz' heq
      rcases z with ⟨t₀, t⟩
      rcases z' with ⟨u₀, u⟩
      dsimp [f] at heq
      have htu : t = u := by simpa using heq
      subst u
      have ht₀' := mem_signedTripleResidues.mp
        (Finset.mem_sigma.mp hz).1
      have hu₀' := mem_signedTripleResidues.mp
        (Finset.mem_sigma.mp hz').1
      have htp' := (mem_goldbachProgressionSeats_iff_balanced_modEq
        hn hM ht₀'.1).mp (Finset.mem_sigma.mp hz).2
      have hup' := (mem_goldbachProgressionSeats_iff_balanced_modEq
        hn hM hu₀'.1).mp (Finset.mem_sigma.mp hz').2
      have htp : t % (p * q * r) = t₀ := by simpa using htp'.2
      have hup : t % (p * q * r) = u₀ := by simpa using hup'.2
      have hidx : t₀ = u₀ := by omega
      subst u₀
      cases htp
      rfl
    exact Finset.card_le_card_of_injOn f hfmem hfinj
  have hBL : B.card ≤ L.card := by
    let g : ℕ → (Σ _ : ℕ, ℕ) :=
      fun t => ⟨t % (p * q * r), t⟩
    have hgmem : ∀ t ∈ B, g t ∈ L := by
      intro t ht
      have ht' := mem_goldbachWindowTripleSupportSeats.mp ht
      have hpt := (goldbach_signed_pair_raw_iff_support hS hbound hanchor
        ht'.1 hpS).mpr ht'.2.1
      have hqt := (goldbach_signed_pair_raw_iff_support hS hbound hanchor
        ht'.1 hqS).mpr ht'.2.2.1
      have hrt := (goldbach_signed_pair_raw_iff_support hS hbound hanchor
        ht'.1 hrS).mpr ht'.2.2.2
      have hpm := natCast_mod_triple_eq_left
        (t := t) hp_pos hq_pos hr_pos
      have hqm := natCast_mod_triple_eq_middle
        (t := t) hp_pos hq_pos hr_pos
      have hrm := natCast_mod_triple_eq_right
        (t := t) hp_pos hq_pos hr_pos
      have hpt₀ : ((t % (p * q * r) : ℕ) : ZMod p) ∈
          goldbachForbiddenResidues n p := by
        rw [hpm]
        exact hpt
      have hqt₀ : ((t % (p * q * r) : ℕ) : ZMod q) ∈
          goldbachForbiddenResidues n q := by
        rw [hqm]
        exact hqt
      have hrt₀ : ((t % (p * q * r) : ℕ) : ZMod r) ∈
          goldbachForbiddenResidues n r := by
        rw [hrm]
        exact hrt
      apply Finset.mem_sigma.mpr
      refine ⟨mem_signedTripleResidues.mpr
        ⟨Nat.mod_lt t hM, hpt₀, hqt₀, hrt₀⟩, ?_⟩
      apply (mem_goldbachProgressionSeats_iff_balanced_modEq
        hn hM (Nat.mod_lt t hM)).mpr
      exact ⟨ht'.1, rfl⟩
    have hginj : Set.InjOn g (B : Set ℕ) := by
      intro t ht u hu heq
      exact congrArg Sigma.snd heq
    exact Finset.card_le_card_of_injOn g hgmem hginj
  have hcard : L.card = B.card := Nat.le_antisymm hLB hBL
  simpa [A, B] using hcount.trans hcard

/-! ## Global pair double count -/

theorem goldbachSignedPairCRTSum_eq_windowPairOverlapCount
    {n w P : ℕ} {S : Finset ℕ}
    (hn : 2 ≤ n) (hS : KnownPrimeScales S)
    (hbound : ∀ ⦃r : ℕ⦄, r ∈ S → r ≤ P) (hanchor : P < n - w) :
    goldbachSignedPairCRTSum n w S =
      goldbachWindowPairOverlapCount n w S := by
  classical
  let U : Finset (ℕ × ℕ) := goldbachStrictPrimePairs S
  have hpairset (t : ℕ) :
      U.filter (fun pair =>
        pair.1 ∈ goldbachObstructionSupportIn n t S ∧
          pair.2 ∈ goldbachObstructionSupportIn n t S) =
        goldbachSupportUpperPairs (goldbachObstructionSupportIn n t S) := by
    ext pair
    rcases pair with ⟨p, q⟩
    simp [U, goldbachStrictPrimePairs, goldbachSupportUpperPairs,
      Finset.mem_offDiag, and_assoc, and_left_comm, and_comm]
    omega
  calc
    goldbachSignedPairCRTSum n w S =
        ∑ pair ∈ U,
          (goldbachWindowPairSupportSeats n w S pair.1 pair.2).card := by
      apply Finset.sum_congr rfl
      intro pair hp
      exact goldbachSignedPairCRTCount_eq_pairSupportSeats_card
        hn hS hbound hanchor hp
    _ = ∑ pair ∈ U, ∑ t ∈ goldbachBalancedOffsets n w,
          if pair.1 ∈ goldbachObstructionSupportIn n t S ∧
              pair.2 ∈ goldbachObstructionSupportIn n t S then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro pair hp
      unfold goldbachWindowPairSupportSeats
      rw [Finset.card_filter]
    _ = ∑ t ∈ goldbachBalancedOffsets n w, ∑ pair ∈ U,
          if pair.1 ∈ goldbachObstructionSupportIn n t S ∧
              pair.2 ∈ goldbachObstructionSupportIn n t S then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ t ∈ goldbachBalancedOffsets n w,
          (U.filter (fun pair =>
            pair.1 ∈ goldbachObstructionSupportIn n t S ∧
              pair.2 ∈ goldbachObstructionSupportIn n t S)).card := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [Finset.card_filter]
    _ = ∑ t ∈ goldbachBalancedOffsets n w,
          (goldbachSupportUpperPairs
            (goldbachObstructionSupportIn n t S)).card := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [hpairset]
    _ = goldbachWindowPairOverlapCount n w S := by
      unfold goldbachWindowPairOverlapCount
      apply Finset.sum_congr rfl
      intro t ht
      exact (goldbach_card_supportUpperPairs_eq_choose _).trans
        rfl

/-! ## Global triple double count -/

theorem goldbachSignedTripleCRTSum_eq_windowTripleOverlapCount
    {n w P : ℕ} {S : Finset ℕ}
    (hn : 2 ≤ n) (hS : KnownPrimeScales S)
    (hbound : ∀ ⦃r : ℕ⦄, r ∈ S → r ≤ P) (hanchor : P < n - w) :
    goldbachSignedTripleCRTSum n w S =
      goldbachWindowTripleOverlapCount n w S := by
  classical
  let U : Finset (ℕ × ℕ × ℕ) := goldbachPrimeTriples S
  have htripleset (t : ℕ) :
      U.filter (fun triple =>
        triple.1 ∈ goldbachObstructionSupportIn n t S ∧
          triple.2.1 ∈ goldbachObstructionSupportIn n t S ∧
            triple.2.2 ∈ goldbachObstructionSupportIn n t S) =
        goldbachSupportUpperTriples (goldbachObstructionSupportIn n t S) := by
    ext triple
    rcases triple with ⟨p, q, r⟩
    simp [U, goldbachPrimeTriples, goldbachSupportUpperTriples,
      Finset.mem_product, and_assoc, and_left_comm, and_comm]
  calc
    goldbachSignedTripleCRTSum n w S =
        ∑ triple ∈ U,
          (goldbachWindowTripleSupportSeats n w S triple.1
            triple.2.1 triple.2.2).card := by
      apply Finset.sum_congr rfl
      intro triple htriple
      exact goldbachSignedTripleCRTCount_eq_tripleSupportSeats_card
        hn hS hbound hanchor htriple
    _ = ∑ triple ∈ U, ∑ t ∈ goldbachBalancedOffsets n w,
          if triple.1 ∈ goldbachObstructionSupportIn n t S ∧
              triple.2.1 ∈ goldbachObstructionSupportIn n t S ∧
              triple.2.2 ∈ goldbachObstructionSupportIn n t S then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro triple htriple
      unfold goldbachWindowTripleSupportSeats
      rw [Finset.card_filter]
    _ = ∑ t ∈ goldbachBalancedOffsets n w, ∑ triple ∈ U,
          if triple.1 ∈ goldbachObstructionSupportIn n t S ∧
              triple.2.1 ∈ goldbachObstructionSupportIn n t S ∧
              triple.2.2 ∈ goldbachObstructionSupportIn n t S then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ t ∈ goldbachBalancedOffsets n w,
          (U.filter (fun triple =>
            triple.1 ∈ goldbachObstructionSupportIn n t S ∧
              triple.2.1 ∈ goldbachObstructionSupportIn n t S ∧
              triple.2.2 ∈ goldbachObstructionSupportIn n t S)).card := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [Finset.card_filter]
    _ = ∑ t ∈ goldbachBalancedOffsets n w,
          (goldbachSupportUpperTriples
            (goldbachObstructionSupportIn n t S)).card := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [htripleset]
    _ = goldbachWindowTripleOverlapCount n w S := by
      unfold goldbachWindowTripleOverlapCount
      apply Finset.sum_congr rfl
      intro t ht
      exact (goldbach_card_supportUpperTriples_eq_choose _).trans rfl

/-! ## Provider bridge after exact identification -/

theorem goldbachWindowSurvivor_of_signed_crt_budget_exact
    {n w P : ℕ} {S : Finset ℕ} {C : ℕ}
    (hn : 2 ≤ n) (hS : KnownPrimeScales S)
    (hbound : ∀ ⦃r : ℕ⦄, r ∈ S → r ≤ P) (hanchor : P < n - w)
    (hincidence : goldbachWindowIncidence n w S ≤ C)
    (hbudget : C < (goldbachBalancedOffsets n w).card +
      (goldbachSignedPairCRTSum n w S - goldbachSignedTripleCRTSum n w S)) :
    (goldbachWindowSurvivors n w S).Nonempty := by
  apply goldbachWindowSurvivor_of_signed_crt_budget hincidence
  · rw [goldbachSignedPairCRTSum_eq_windowPairOverlapCount
      hn hS hbound hanchor]
  · rw [goldbachSignedTripleCRTSum_eq_windowTripleOverlapCount
      hn hS hbound hanchor]
  · exact hbudget

theorem goldbachWindowSurvivor_of_residue_capacity_of_signed_crt_budget_exact
    {n w P : ℕ} {S : Finset ℕ}
    (hn : 2 ≤ n) (hS : KnownPrimeScales S)
    (hbound : ∀ ⦃r : ℕ⦄, r ∈ S → r ≤ P) (hanchor : P < n - w)
    (hbudget :
      (∑ r ∈ S, (if r ∣ 2 * n then 1 else 2) * (w / r + 1)) <
        (goldbachBalancedOffsets n w).card +
          (goldbachSignedPairCRTSum n w S -
            goldbachSignedTripleCRTSum n w S)) :
    (goldbachWindowSurvivors n w S).Nonempty := by
  apply goldbachWindowSurvivor_of_signed_crt_budget_exact
    hn hS hbound hanchor
    (C := ∑ r ∈ S, (if r ∣ 2 * n then 1 else 2) * (w / r + 1))
  · exact goldbachWindow_incidence_le_residue_capacity n w S
  · exact hbudget

end DkMath.NumberTheory
