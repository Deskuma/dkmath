/-
Copyright (c) 2026 DkMath contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: DkMath contributors.
-/

import DkMath.NumberTheory.MultiGauge.Basic

#print "file: DkMath.NumberTheory.MultiGauge.PrimeTransport"

/-!
# Prime transport across a two-stage gauge transition

All transport results here are elementary consequences of primality and the
cross-multiplication balance law.  The one-stage common-channel result reuses
the production `GTail` gcd boundary theorem.
-/

namespace DkMath.NumberTheory.MultiGauge

open DkMath.CosmicFormula

/-! ## Transition support localization -/

/--
Capture at the second stage can come from the first observer or the
transition numerator.
-/
theorem prime_dvd_second_value_imp_dvd_first_or_numerator
    {d q : ℕ} (hq : Nat.Prime q)
    (t : GNGaugeTransition d)
    (hq2 : q ∣ t.second.value) :
    q ∣ t.first.value ∨ q ∣ t.numerator := by
  have hprod : q ∣ t.second.value * t.denominator :=
    dvd_mul_of_dvd_left hq2 _
  rw [t.balance] at hprod
  exact (hq.dvd_mul).mp hprod

/--
Capture at the first stage can persist to the second stage or be carried by
the transition denominator.
-/
theorem prime_dvd_first_value_imp_dvd_second_or_denominator
    {d q : ℕ} (hq : Nat.Prime q)
    (t : GNGaugeTransition d)
    (hq1 : q ∣ t.first.value) :
    q ∣ t.second.value ∨ q ∣ t.denominator := by
  have hprod : q ∣ t.first.value * t.numerator :=
    dvd_mul_of_dvd_left hq1 _
  rw [← t.balance] at hprod
  exact (hq.dvd_mul).mp hprod

/-! ## Escape transport -/

/--
A prime absent from the first stage cannot appear at the second stage unless
it enters through the transition numerator.
-/
theorem primeEscapes_second_of_first_of_not_dvd_numerator
    {d q : ℕ} (hq : Nat.Prime q)
    (t : GNGaugeTransition d)
    (hEscape : PrimeEscapes q t.first)
    (hNum : ¬ q ∣ t.numerator) :
    PrimeEscapes q t.second := by
  intro hq2
  rcases prime_dvd_second_value_imp_dvd_first_or_numerator hq t hq2 with hq1 | hqν
  · exact hEscape hq1
  · exact hNum hqν

/--
A prime absent from the second stage cannot have been present at the first
stage unless it is carried by the transition denominator.
-/
theorem primeEscapes_first_of_second_of_not_dvd_denominator
    {d q : ℕ} (hq : Nat.Prime q)
    (t : GNGaugeTransition d)
    (hEscape : PrimeEscapes q t.second)
    (hDen : ¬ q ∣ t.denominator) :
    PrimeEscapes q t.first := by
  intro hq1
  rcases prime_dvd_first_value_imp_dvd_second_or_denominator hq t hq1 with hq2 | hqδ
  · exact hEscape hq2
  · exact hDen hqδ

/-! ## Visibility conservation outside transition support -/

/-- Visibility is conserved when a prime avoids both transition coefficients. -/
theorem primeCaught_iff_of_not_dvd_transition_support
    {d q : ℕ} (hq : Nat.Prime q)
    (t : GNGaugeTransition d)
    (hNum : ¬ q ∣ t.numerator)
    (hDen : ¬ q ∣ t.denominator) :
    PrimeCaught q t.first ↔ PrimeCaught q t.second := by
  constructor
  · intro hq1
    rcases prime_dvd_first_value_imp_dvd_second_or_denominator hq t hq1 with hq2 | hqδ
    · exact hq2
    · exact False.elim (hDen hqδ)
  · intro hq2
    rcases prime_dvd_second_value_imp_dvd_first_or_numerator hq t hq2 with hq1 | hqν
    · exact hq1
    · exact False.elim (hNum hqν)

/-- Escape is conserved when a prime avoids both transition coefficients. -/
theorem primeEscapes_iff_of_not_dvd_transition_support
    {d q : ℕ} (hq : Nat.Prime q)
    (t : GNGaugeTransition d)
    (hNum : ¬ q ∣ t.numerator)
    (hDen : ¬ q ∣ t.denominator) :
    PrimeEscapes q t.first ↔ PrimeEscapes q t.second := by
  constructor
  · intro hEscape
    exact primeEscapes_second_of_first_of_not_dvd_numerator hq t hEscape hNum
  · intro hEscape
    exact primeEscapes_first_of_second_of_not_dvd_denominator hq t hEscape hDen

/-! ## One-stage boundary and GN channels -/

/-- The stage observer is caught exactly through its boundary or GN channel. -/
theorem primeCaught_iff_boundary_or_gnValue
    {d q : ℕ} (hq : Nat.Prime q) (s : GNGaugeStage d) :
    PrimeCaught q s ↔ q ∣ s.x ∨ q ∣ s.gnValue := by
  exact hq.dvd_mul

/-- Any common boundary/GN divisor at a coprime stage divides the exponent. -/
theorem common_channel_dvd_exponent
    {d q : ℕ} (hd : 1 ≤ d) (s : GNGaugeStage d)
    (hqx : q ∣ s.x) (hqgn : q ∣ s.gnValue) :
    q ∣ d := by
  have hqgcd : q ∣ Nat.gcd s.x s.gnValue := Nat.dvd_gcd hqx hqgn
  change q ∣ Nat.gcd s.x (GTail d 1 s.x s.u) at hqgcd
  rw [gcd_GN_eq_gcd_of_one_le hd s.coprime] at hqgcd
  exact dvd_trans hqgcd (Nat.gcd_dvd_right _ _)

/-- A divisor away from the exponent cannot occupy both stage channels. -/
theorem no_common_channel_of_not_dvd_exponent
    {d q : ℕ} (hd : 1 ≤ d) (s : GNGaugeStage d)
    (hqd : ¬ q ∣ d) :
    ¬ (q ∣ s.x ∧ q ∣ s.gnValue) := by
  rintro ⟨hqx, hqgn⟩
  exact hqd (common_channel_dvd_exponent hd s hqx hqgn)

end DkMath.NumberTheory.MultiGauge
