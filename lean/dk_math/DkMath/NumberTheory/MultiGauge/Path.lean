/-
Copyright (c) 2026 DkMath contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: DkMath contributors.
-/

import DkMath.NumberTheory.MultiGauge.PrimeTransport

#print "file: DkMath.NumberTheory.MultiGauge.Path"

/-!
# Finite prime-escape paths

This module composes the MG-000 two-stage transport law over a finite linked
list of transitions. The path representation is intentionally small: a start
stage, a transition list, and the invariant that every transition starts at
the preceding stage's endpoint.
-/

namespace DkMath.NumberTheory.MultiGauge

/-! ## Linked paths and observers -/

/-- A transition list is linked when each transition starts at the current
stage and the remainder starts at that transition's second stage. -/
def Linked {d : ℕ} (current : GNGaugeStage d) :
    List (GNGaugeTransition d) → Prop
  | [] => True
  | t :: ts => t.first = current ∧ Linked t.second ts

/-- A finite linked chain of GN gauge transitions. -/
structure GNGaugePath (d : ℕ) where
  start : GNGaugeStage d
  transitions : List (GNGaugeTransition d)
  linked : Linked start transitions

private def pathEndFrom {d : ℕ} (current : GNGaugeStage d) :
    List (GNGaugeTransition d) → GNGaugeStage d
  | [] => current
  | t :: ts => pathEndFrom t.second ts

private def numeratorProductFrom {d : ℕ} :
    List (GNGaugeTransition d) → ℕ
  | [] => 1
  | t :: ts => t.numerator * numeratorProductFrom ts

private def denominatorProductFrom {d : ℕ} :
    List (GNGaugeTransition d) → ℕ
  | [] => 1
  | t :: ts => t.denominator * denominatorProductFrom ts

/-- The endpoint of a finite path. -/
def GNGaugePath.endStage (p : GNGaugePath d) : GNGaugeStage d :=
  pathEndFrom p.start p.transitions

/-- The ordered list of stages visited by a finite path. -/
def GNGaugePath.stages (p : GNGaugePath d) : List (GNGaugeStage d) :=
  p.start :: p.transitions.map (fun t => t.second)

/-- The product of all transition numerators on a finite path. -/
def GNGaugePath.numeratorProduct (p : GNGaugePath d) : ℕ :=
  numeratorProductFrom p.transitions

/-- The product of all transition denominators on a finite path. -/
def GNGaugePath.denominatorProduct (p : GNGaugePath d) : ℕ :=
  denominatorProductFrom p.transitions

/-! ## Telescoped balance -/

private theorem path_balance_from
    {d : ℕ} (current : GNGaugeStage d)
    (ts : List (GNGaugeTransition d))
    (hLinked : Linked current ts) :
    (pathEndFrom current ts).value * denominatorProductFrom ts =
      current.value * numeratorProductFrom ts := by
  induction ts generalizing current with
  | nil =>
      simp [pathEndFrom, numeratorProductFrom, denominatorProductFrom]
  | cons t ts ih =>
      rcases hLinked with ⟨hfirst, htail⟩
      have hrest := ih (current := t.second) htail
      change (pathEndFrom t.second ts).value *
          (t.denominator * denominatorProductFrom ts) =
        current.value * (t.numerator * numeratorProductFrom ts)
      calc
        (pathEndFrom t.second ts).value *
            (t.denominator * denominatorProductFrom ts) =
            ((pathEndFrom t.second ts).value * denominatorProductFrom ts) *
              t.denominator := by ring
        _ = (t.second.value * numeratorProductFrom ts) * t.denominator := by
          rw [hrest]
        _ = (t.second.value * t.denominator) *
              numeratorProductFrom ts := by ring
        _ = (t.first.value * t.numerator) *
              numeratorProductFrom ts := by rw [t.balance]
        _ = current.value *
              (t.numerator * numeratorProductFrom ts) := by
          rw [hfirst]
          ring

/-- The exact telescoped balance law for a finite path. -/
theorem GNGaugePath.balance (p : GNGaugePath d) :
    p.endStage.value * p.denominatorProduct =
      p.start.value * p.numeratorProduct := by
  exact path_balance_from p.start p.transitions p.linked

/-! ## Global support localization -/

/-- Endpoint capture comes from start capture or total numerator support. -/
theorem prime_dvd_end_value_imp_dvd_start_or_numeratorProduct
    {d q : ℕ} (hq : Nat.Prime q) (p : GNGaugePath d)
    (hqEnd : q ∣ p.endStage.value) :
    q ∣ p.start.value ∨ q ∣ p.numeratorProduct := by
  have hprod : q ∣ p.endStage.value * p.denominatorProduct :=
    dvd_mul_of_dvd_left hqEnd _
  rw [p.balance] at hprod
  exact (hq.dvd_mul).mp hprod

/-- Start capture persists to the endpoint or enters total denominator support. -/
theorem prime_dvd_start_value_imp_dvd_end_or_denominatorProduct
    {d q : ℕ} (hq : Nat.Prime q) (p : GNGaugePath d)
    (hqStart : q ∣ p.start.value) :
    q ∣ p.endStage.value ∨ q ∣ p.denominatorProduct := by
  have hprod : q ∣ p.start.value * p.numeratorProduct :=
    dvd_mul_of_dvd_left hqStart _
  rw [← p.balance] at hprod
  exact (hq.dvd_mul).mp hprod

/-- Initial escape and total numerator avoidance imply endpoint escape. -/
theorem primeEscapes_end_of_start_of_not_dvd_numeratorProduct
    {d q : ℕ} (hq : Nat.Prime q) (p : GNGaugePath d)
    (hEscape : PrimeEscapes q p.start)
    (hNum : ¬ q ∣ p.numeratorProduct) :
    PrimeEscapes q p.endStage := by
  intro hqEnd
  rcases prime_dvd_end_value_imp_dvd_start_or_numeratorProduct hq p hqEnd with
    hqStart | hqNum
  · exact hEscape hqStart
  · exact hNum hqNum

/-- Endpoint escape and denominator avoidance imply initial escape. -/
theorem primeEscapes_start_of_end_of_not_dvd_denominatorProduct
    {d q : ℕ} (hq : Nat.Prime q) (p : GNGaugePath d)
    (hEscape : PrimeEscapes q p.endStage)
    (hDen : ¬ q ∣ p.denominatorProduct) :
    PrimeEscapes q p.start := by
  intro hqStart
  rcases prime_dvd_start_value_imp_dvd_end_or_denominatorProduct hq p hqStart with
    hqEnd | hqDen
  · exact hEscape hqEnd
  · exact hDen hqDen

/-! ## Global visibility equivalences -/

/-- Outside total transition support, endpoint capture is equivalent to start
capture. -/
theorem primeCaught_iff_of_not_dvd_path_support
    {d q : ℕ} (hq : Nat.Prime q) (p : GNGaugePath d)
    (hNum : ¬ q ∣ p.numeratorProduct)
    (hDen : ¬ q ∣ p.denominatorProduct) :
    PrimeCaught q p.start ↔ PrimeCaught q p.endStage := by
  constructor
  · intro hqStart
    rcases prime_dvd_start_value_imp_dvd_end_or_denominatorProduct hq p hqStart with
      hqEnd | hqDen
    · exact hqEnd
    · exact False.elim (hDen hqDen)
  · intro hqEnd
    rcases prime_dvd_end_value_imp_dvd_start_or_numeratorProduct hq p hqEnd with
      hqStart | hqNum
    · exact hqStart
    · exact False.elim (hNum hqNum)

/-- Outside total transition support, endpoint escape is equivalent to start
escape. -/
theorem primeEscapes_iff_of_not_dvd_path_support
    {d q : ℕ} (hq : Nat.Prime q) (p : GNGaugePath d)
    (hNum : ¬ q ∣ p.numeratorProduct)
    (hDen : ¬ q ∣ p.denominatorProduct) :
    PrimeEscapes q p.start ↔ PrimeEscapes q p.endStage := by
  constructor
  · intro hEscape
    exact primeEscapes_end_of_start_of_not_dvd_numeratorProduct hq p hEscape hNum
  · intro hEscape
    exact primeEscapes_start_of_end_of_not_dvd_denominatorProduct hq p hEscape hDen

/-! ## Escape at every visited stage -/

private theorem primeEscapes_stage_list_from
    {d q : ℕ} (hq : Nat.Prime q) (current : GNGaugeStage d)
    (ts : List (GNGaugeTransition d)) (hLinked : Linked current ts)
    (hEscape : PrimeEscapes q current)
    (hNum : ∀ t ∈ ts, ¬ q ∣ t.numerator) :
    ∀ s ∈ current :: ts.map (fun t => t.second), PrimeEscapes q s := by
  induction ts generalizing current with
  | nil =>
      intro s hs
      simp only [List.map_nil, List.mem_cons] at hs
      rcases hs with rfl | hs
      · exact hEscape
      · exact False.elim (by simp at hs)
  | cons t ts ih =>
      rcases hLinked with ⟨hfirst, htail⟩
      have hfirstEscape : PrimeEscapes q t.first := by
        simpa [hfirst] using hEscape
      have hsecondEscape :=
        primeEscapes_second_of_first_of_not_dvd_numerator hq t hfirstEscape
          (hNum t (by simp))
      have htailEscape := ih (current := t.second) htail hsecondEscape (by
        intro t' ht'
        exact hNum t' (by simp [ht']))
      intro s hs
      simp only [List.map_cons, List.mem_cons] at hs
      rcases hs with rfl | rfl | hs
      · exact hEscape
      · exact hsecondEscape
      · exact htailEscape s (by simp [hs])

/-- Initial escape persists at every stage of the finite path when every
transition numerator avoids the prime. -/
theorem primeEscapes_all_stages
    {d q : ℕ} (hq : Nat.Prime q) (p : GNGaugePath d)
    (hEscape : PrimeEscapes q p.start)
    (hNum : ∀ t ∈ p.transitions, ¬ q ∣ t.numerator) :
    ∀ s ∈ p.stages, PrimeEscapes q s := by
  exact primeEscapes_stage_list_from hq p.start p.transitions p.linked hEscape hNum

/-! ## First capture localization -/

private theorem first_capture_from
    {d q : ℕ} (hq : Nat.Prime q) (current : GNGaugeStage d)
    (ts : List (GNGaugeTransition d)) (hLinked : Linked current ts)
    (hEscape : PrimeEscapes q current)
    (hCaptured : ∃ s ∈ current :: ts.map (fun t => t.second), PrimeCaught q s) :
    ∃ t ∈ ts, PrimeEscapes q t.first ∧ PrimeCaught q t.second ∧
      q ∣ t.numerator := by
  induction ts generalizing current with
  | nil =>
      rcases hCaptured with ⟨s, hs, hsCaught⟩
      simp only [List.map_nil, List.mem_cons] at hs
      rcases hs with rfl | hs
      · exact False.elim (hEscape hsCaught)
      · exact False.elim (by simp at hs)
  | cons t ts ih =>
      rcases hLinked with ⟨hfirst, htail⟩
      rcases hCaptured with ⟨s, hs, hsCaught⟩
      simp only [List.map_cons, List.mem_cons] at hs
      rcases hs with rfl | rfl | hs
      · exact False.elim (hEscape hsCaught)
      · have hfirstEscape : PrimeEscapes q t.first := by
          simpa [hfirst] using hEscape
        have hqNum : q ∣ t.numerator := by
          rcases prime_dvd_second_value_imp_dvd_first_or_numerator hq t hsCaught with
            hqFirst | hqNum
          · exact False.elim (hfirstEscape hqFirst)
          · exact hqNum
        exact ⟨t, by simp, hfirstEscape, hsCaught, hqNum⟩
      · by_cases hsecondEscape : PrimeEscapes q t.second
        · have htailCapture := ih (current := t.second) htail hsecondEscape
            ⟨s, by simp [hs], hsCaught⟩
          rcases htailCapture with ⟨t', ht', hfirstEscape, hsecondCaught, hqNum⟩
          exact ⟨t', by simp [ht'], hfirstEscape, hsecondCaught, hqNum⟩
        · have hsecondCaught : PrimeCaught q t.second := by
            by_contra hnot
            exact hsecondEscape hnot
          have hfirstEscape : PrimeEscapes q t.first := by
            simpa [hfirst] using hEscape
          have hqNum : q ∣ t.numerator := by
            rcases prime_dvd_second_value_imp_dvd_first_or_numerator hq t hsecondCaught with
              hqFirst | hqNum
            · exact False.elim (hfirstEscape hqFirst)
            · exact hqNum
          exact ⟨t, by simp, hfirstEscape, hsecondCaught, hqNum⟩

/-- A captured stage after initial escape has an escape-to-capture transition
whose numerator contains the prime. -/
theorem exists_escape_to_capture_transition_of_captured_stage
    {d q : ℕ} (hq : Nat.Prime q) (p : GNGaugePath d)
    (hEscape : PrimeEscapes q p.start)
    (hCaptured : ∃ s ∈ p.stages, PrimeCaught q s) :
    ∃ t ∈ p.transitions, PrimeEscapes q t.first ∧ PrimeCaught q t.second ∧
      q ∣ t.numerator := by
  exact first_capture_from hq p.start p.transitions p.linked hEscape hCaptured

/-- If a path starts escaped and ends captured, the prime divides the total
numerator product. -/
theorem prime_dvd_numeratorProduct_of_start_escape_of_end_caught
    {d q : ℕ} (hq : Nat.Prime q) (p : GNGaugePath d)
    (hEscape : PrimeEscapes q p.start)
    (hCaught : PrimeCaught q p.endStage) :
    q ∣ p.numeratorProduct := by
  rcases prime_dvd_end_value_imp_dvd_start_or_numeratorProduct hq p hCaught with
    hqStart | hqNum
  · exact False.elim (hEscape hqStart)
  · exact hqNum

/-- If a path starts captured and ends escaped, the prime divides the total
denominator product. -/
theorem prime_dvd_denominatorProduct_of_start_caught_of_end_escape
    {d q : ℕ} (hq : Nat.Prime q) (p : GNGaugePath d)
    (hCaught : PrimeCaught q p.start)
    (hEscape : PrimeEscapes q p.endStage) :
    q ∣ p.denominatorProduct := by
  rcases prime_dvd_start_value_imp_dvd_end_or_denominatorProduct hq p hCaught with
    hqEnd | hqDen
  · exact False.elim (hEscape hqEnd)
  · exact hqDen

/-! ## Small regression theorems -/

/-- A two-transition chain transports escape through both arrows when both
numerators avoid the prime. -/
theorem two_step_prime_escape_regression
    {d q : ℕ} (hq : Nat.Prime q)
    (t₀ t₁ : GNGaugeTransition d)
    (hjoin : t₀.second = t₁.first)
    (hEscape : PrimeEscapes q t₀.first)
    (hNum₀ : ¬ q ∣ t₀.numerator)
    (hNum₁ : ¬ q ∣ t₁.numerator) :
    PrimeEscapes q t₀.first ∧ PrimeEscapes q t₀.second ∧ PrimeEscapes q t₁.second := by
  have hPathLink : Linked t₀.first [t₀, t₁] := by
    simp [Linked, hjoin]
  let p : GNGaugePath d :=
    { start := t₀.first
      transitions := [t₀, t₁]
      linked := hPathLink }
  have hall := primeEscapes_all_stages hq p hEscape (by
    intro t ht
    rcases (by simpa [p] using ht) with rfl | rfl
    · exact hNum₀
    · exact hNum₁)
  refine ⟨hEscape, ?_, ?_⟩
  · exact hall t₀.second (by simp [p, GNGaugePath.stages])
  · exact hall t₁.second (by simp [p, GNGaugePath.stages])

/-- A newly captured second-stage prime is found in the transition numerator. -/
theorem new_capture_has_numerator_support_regression
    {d q : ℕ} (hq : Nat.Prime q) (t : GNGaugeTransition d)
    (hEscape : PrimeEscapes q t.first)
    (hCaught : PrimeCaught q t.second) :
    q ∣ t.numerator := by
  rcases prime_dvd_second_value_imp_dvd_first_or_numerator hq t hCaught with
    hqFirst | hqNum
  · exact False.elim (hEscape hqFirst)
  · exact hqNum

end DkMath.NumberTheory.MultiGauge
