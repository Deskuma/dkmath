/-
Copyright (c) 2026 DkMath contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: DkMath contributors.
-/

import DkMath.NumberTheory.MultiGauge.GnomonPetalTransition
import DkMath.NumberTheory.MultiGauge.Path

#print "file: DkMath.NumberTheory.MultiGauge.GnomonPetalPath"

/-!
# Finite paths of Petal transitions

This module specializes `GNGaugePath` to the canonical degree-two Petal
transitions.  The transition list is linked by construction, so the generic
path balance and prime-transport theorems apply without introducing another
path representation.
-/

namespace DkMath.NumberTheory.MultiGauge

open DkMath.Gnomon
open scoped BigOperators

/-- The address reached after multiplying by all factors in `bs`. -/
def petalFold (a : ℕ) : List ℕ → ℕ
  | [] => a
  | b :: bs => petalFold (petalMul a b) bs

/-- The canonical transition list for a finite sequence of Petal factors. -/
def petalPathTransitions (a : ℕ) : List ℕ → List (GNGaugeTransition 2)
  | [] => []
  | b :: bs =>
      gnomonPetalTransition a b :: petalPathTransitions (petalMul a b) bs

theorem petalPathTransitions_linked (a : ℕ) (bs : List ℕ) :
    Linked (oddGnomonGaugeStage a) (petalPathTransitions a bs) := by
  induction bs generalizing a with
  | nil => simp [petalPathTransitions, Linked]
  | cons b bs ih =>
      simp only [petalPathTransitions, Linked]
      exact ⟨rfl, ih (a := petalMul a b)⟩

/-- The finite linked path of canonical Petal transitions. -/
def gnomonPetalPath (a : ℕ) (bs : List ℕ) : GNGaugePath 2 :=
  { start := oddGnomonGaugeStage a
    transitions := petalPathTransitions a bs
    linked := petalPathTransitions_linked a bs }

@[simp] theorem gnomonPetalPath_start (a : ℕ) (bs : List ℕ) :
    (gnomonPetalPath a bs).start = oddGnomonGaugeStage a := rfl

@[simp] theorem gnomonPetalPath_transitions (a : ℕ) (bs : List ℕ) :
    (gnomonPetalPath a bs).transitions = petalPathTransitions a bs := rfl

@[simp] theorem gnomonPetalPath_endStage (a : ℕ) (bs : List ℕ) :
    (gnomonPetalPath a bs).endStage =
      oddGnomonGaugeStage (petalFold a bs) := by
  induction bs generalizing a with
  | nil => rfl
  | cons b bs ih =>
      change (gnomonPetalPath (petalMul a b) bs).endStage =
        oddGnomonGaugeStage (petalFold (petalMul a b) bs)
      exact ih (a := petalMul a b)

@[simp] theorem gnomonPetalPath_denominatorProduct (a : ℕ) (bs : List ℕ) :
    (gnomonPetalPath a bs).denominatorProduct = 1 := by
  induction bs generalizing a with
  | nil => rfl
  | cons b bs ih =>
      change 1 * (gnomonPetalPath (petalMul a b) bs).denominatorProduct = 1
      simp [ih]

@[simp] theorem gnomonPetalPath_numeratorProduct (a : ℕ) (bs : List ℕ) :
    (gnomonPetalPath a bs).numeratorProduct =
      (bs.map oddGnomon).prod := by
  induction bs generalizing a with
  | nil => rfl
  | cons b bs ih =>
      change oddGnomon b *
          (gnomonPetalPath (petalMul a b) bs).numeratorProduct =
        oddGnomon b * (bs.map oddGnomon).prod
      rw [ih]

/-! ## Exact endpoint observers -/

theorem gnomonPetalPath_balance_value (a : ℕ) (bs : List ℕ) :
    (gnomonPetalPath a bs).endStage.value =
      oddGnomon a * (bs.map oddGnomon).prod := by
  have h := (gnomonPetalPath a bs).balance
  rw [gnomonPetalPath_numeratorProduct,
    gnomonPetalPath_denominatorProduct] at h
  simpa [oddGnomonGaugeStage_value] using h

theorem oddGnomon_petalFold (a : ℕ) (bs : List ℕ) :
    oddGnomon (petalFold a bs) = oddGnomon a * (bs.map oddGnomon).prod := by
  have h := gnomonPetalPath_balance_value a bs
  simpa [gnomonPetalPath_endStage, oddGnomonGaugeStage_value] using h

/-! ## Factor support and escape localization -/

theorem exists_petalFactor_of_mem_petalPathTransitions
    {a : ℕ} {bs : List ℕ} {t : GNGaugeTransition 2}
    (ht : t ∈ petalPathTransitions a bs) :
    ∃ b ∈ bs, t.numerator = oddGnomon b := by
  induction bs generalizing a with
  | nil => simp [petalPathTransitions] at ht
  | cons b bs ih =>
      simp only [petalPathTransitions, List.mem_cons] at ht
      rcases ht with rfl | ht
      · exact ⟨b, by simp, by simp⟩
      · obtain ⟨b', hb', hnum⟩ := ih (a := petalMul a b) ht
        exact ⟨b', by simp [hb'], hnum⟩

theorem primeEscapes_all_stages_gnomonPetalPath
    {q a : ℕ} (bs : List ℕ) (hq : Nat.Prime q)
    (hEscape : PrimeEscapes q (oddGnomonGaugeStage a))
    (hFactor : ∀ b ∈ bs, ¬ q ∣ oddGnomon b) :
    ∀ s ∈ (gnomonPetalPath a bs).stages, PrimeEscapes q s := by
  apply primeEscapes_all_stages hq (gnomonPetalPath a bs) hEscape
  intro t ht
  obtain ⟨b, hb, hnum⟩ :=
    exists_petalFactor_of_mem_petalPathTransitions
      (a := a) (bs := bs) (t := t) (by simpa using ht)
  rw [hnum]
  exact hFactor b hb

theorem primeEscapes_endStage_gnomonPetalPath
    {q a : ℕ} (bs : List ℕ) (hq : Nat.Prime q)
    (hEscape : PrimeEscapes q (oddGnomonGaugeStage a))
    (hFactor : ∀ b ∈ bs, ¬ q ∣ oddGnomon b) :
    PrimeEscapes q (gnomonPetalPath a bs).endStage := by
  apply primeEscapes_end_of_start_of_not_dvd_numeratorProduct
    hq (gnomonPetalPath a bs) hEscape
  rw [gnomonPetalPath_numeratorProduct]
  induction bs with
  | nil => exact hq.not_dvd_one
  | cons b bs ih =>
      simp only [List.map_cons, List.prod_cons]
      intro hqprod
      rcases hq.dvd_mul.mp hqprod with hqb | hqbs
      · exact hFactor b (by simp) hqb
      · exact ih (by
          intro b' hb'
          exact hFactor b' (by simp [hb'])) hqbs

private theorem exists_petalFactor_of_prime_dvd_prod
    {q : ℕ} (hq : Nat.Prime q) :
    ∀ bs : List ℕ, q ∣ (bs.map oddGnomon).prod → ∃ b ∈ bs, q ∣ oddGnomon b := by
  intro bs
  induction bs with
  | nil =>
      intro hqone
      exact False.elim (hq.not_dvd_one hqone)
  | cons b bs ih =>
      intro hqprod
      simp only [List.map_cons, List.prod_cons] at hqprod
      rcases hq.dvd_mul.mp hqprod with hqb | hqbs
      · exact ⟨b, by simp, hqb⟩
      · obtain ⟨b', hb', hqb'⟩ := ih hqbs
        exact ⟨b', by simp [hb'], hqb'⟩

theorem exists_petalFactor_dvd_of_start_escape_of_captured_stage
    {q a : ℕ} (bs : List ℕ) (hq : Nat.Prime q)
    (hEscape : PrimeEscapes q (oddGnomonGaugeStage a))
    (hCaptured : ∃ s ∈ (gnomonPetalPath a bs).stages, PrimeCaught q s) :
    ∃ b ∈ bs, q ∣ oddGnomon b := by
  rcases exists_escape_to_capture_transition_of_captured_stage
      hq (gnomonPetalPath a bs) hEscape hCaptured with
    ⟨t, ht, _, _, hqNum⟩
  obtain ⟨b, hb, hnum⟩ :=
    exists_petalFactor_of_mem_petalPathTransitions
      (a := a) (bs := bs) (t := t) (by simpa using ht)
  exact ⟨b, hb, by rw [← hnum]; exact hqNum⟩

theorem exists_petalFactor_dvd_of_start_escape_of_end_caught
    {q a : ℕ} (bs : List ℕ) (hq : Nat.Prime q)
    (hEscape : PrimeEscapes q (oddGnomonGaugeStage a))
    (hCaught : PrimeCaught q (gnomonPetalPath a bs).endStage) :
    ∃ b ∈ bs, q ∣ oddGnomon b := by
  have hqNum := prime_dvd_numeratorProduct_of_start_escape_of_end_caught
    hq (gnomonPetalPath a bs) hEscape hCaught
  rw [gnomonPetalPath_numeratorProduct] at hqNum
  exact exists_petalFactor_of_prime_dvd_prod hq bs hqNum

/-! ## Small deterministic regressions -/

theorem regression_empty_petalPath (a : ℕ) :
    (gnomonPetalPath a []).transitions = [] ∧
      (gnomonPetalPath a []).endStage = oddGnomonGaugeStage a := by
  exact ⟨rfl, rfl⟩

theorem regression_one_factor_petalPath (a b : ℕ) :
    (gnomonPetalPath a [b]).transitions = [gnomonPetalTransition a b] := by
  rfl

theorem regression_two_factor_petalPath (a b c : ℕ) :
    (gnomonPetalPath a [b, c]).endStage.value =
      oddGnomon a * oddGnomon b * oddGnomon c := by
  simpa [mul_assoc] using gnomonPetalPath_balance_value a [b, c]

theorem regression_prime_avoidance_petalPath :
    ∀ s ∈ (gnomonPetalPath 0 [1]).stages, PrimeEscapes 5 s := by
  apply primeEscapes_all_stages_gnomonPetalPath [1] (by norm_num)
  · simp [PrimeEscapes, oddGnomonGaugeStage_value, oddGnomon]
  · intro b hb
    simp only [List.mem_singleton] at hb
    subst b
    norm_num [oddGnomon]

end DkMath.NumberTheory.MultiGauge

#print axioms DkMath.NumberTheory.MultiGauge.gnomonPetalPath_balance_value
#print axioms DkMath.NumberTheory.MultiGauge.exists_petalFactor_dvd_of_start_escape_of_end_caught
