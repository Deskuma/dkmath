/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.PrimorialUniverse.SquareAnchorPhaseMixedRadixTransport
import Mathlib.Tactic

#print "file: DkMath.NumberTheory.PrimorialUniverse.SquareAnchorPhaseMixedRadixAudit"

/-!
# Square-anchor mixed-radix information audit

PUU-L030 checks whether the L029 mixed-radix transport excludes any finite
raw coordinate.  Euclidean encode/decode and explicit canonical-orbit
witnesses show that every allowed pair `(r,d)` occurs.  The reservation
classification is exactly the existing old-basis/new-prime deletion rule, so
this module records a coordinate-complete finite endpoint rather than a new
coverage obstruction.
-/

namespace DkMath.NumberTheory.PrimorialUniverse

/-- An admissible old-coordinate/fresh-digit pair in one enlarged period. -/
def squareAnchorFreshPrimeMixedRadixCoordinate
    (S : Finset ℕ) (q r d : ℕ) : Prop :=
  r < finitePrimeBasisProduct S ∧ d < q

/-- Euclidean encoding of an enlarged-period coordinate. -/
theorem freshPrimeMixedRadix_encode
    {S : Finset ℕ} (x : ℕ) :
    x = (x % finitePrimeBasisProduct S) +
      (x / finitePrimeBasisProduct S) * finitePrimeBasisProduct S := by
  exact (Nat.mod_add_div' x (finitePrimeBasisProduct S)).symm

/-- The encoder coordinates of an enlarged-period point satisfy the grid
bounds. -/
theorem freshPrimeMixedRadix_encode_bounds
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S)
    {q x : ℕ} (_hq : Nat.Prime q)
    (hx : x < q * finitePrimeBasisProduct S) :
    squareAnchorFreshPrimeMixedRadixCoordinate S q
      (x % finitePrimeBasisProduct S) (x / finitePrimeBasisProduct S) := by
  constructor
  · exact Nat.mod_lt _ (Nat.pos_of_ne_zero (finitePrimeBasisProduct_ne_zero hS))
  · apply (Nat.div_lt_iff_lt_mul
      (Nat.pos_of_ne_zero (finitePrimeBasisProduct_ne_zero hS))).2
    exact hx

/-- Two bounded mixed-radix encodings are equal exactly when both coordinates
are equal. -/
theorem freshPrimeMixedRadix_eq_iff
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S)
    {q r₁ d₁ r₂ d₂ : ℕ}
    (hr₁ : r₁ < finitePrimeBasisProduct S) (_hd₁ : d₁ < q)
    (hr₂ : r₂ < finitePrimeBasisProduct S) (hd₂ : d₂ < q) :
    r₁ + d₁ * finitePrimeBasisProduct S =
        r₂ + d₂ * finitePrimeBasisProduct S ↔
      r₁ = r₂ ∧ d₁ = d₂ := by
  have hMpos : 0 < finitePrimeBasisProduct S :=
    Nat.pos_of_ne_zero (finitePrimeBasisProduct_ne_zero hS)
  constructor
  · intro heq
    have hmod := congrArg (fun x : ℕ => x % finitePrimeBasisProduct S) heq
    have hr : r₁ = r₂ := by
      simpa [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr₁,
        Nat.mod_eq_of_lt hr₂] using hmod
    have hd : d₁ = d₂ := by
      apply Nat.mul_right_cancel hMpos
      simpa [hr] using heq
    exact ⟨hr, hd⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- Every point below the enlarged period has a unique bounded mixed-radix
encoding. -/
theorem freshPrimeMixedRadix_exists_unique
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S)
    {q x : ℕ} (hq : Nat.Prime q)
    (hx : x < q * finitePrimeBasisProduct S) :
    ∃! z : ℕ × ℕ,
      squareAnchorFreshPrimeMixedRadixCoordinate S q z.1 z.2 ∧
        x = z.1 + z.2 * finitePrimeBasisProduct S := by
  have hcoord := freshPrimeMixedRadix_encode_bounds hS hq hx
  have hencode := freshPrimeMixedRadix_encode (S := S) x
  refine ⟨(x % finitePrimeBasisProduct S, x / finitePrimeBasisProduct S),
    ⟨hcoord, hencode⟩, ?_⟩
  intro z hz
  have heq : z.1 + z.2 * finitePrimeBasisProduct S =
      (x % finitePrimeBasisProduct S) +
        (x / finitePrimeBasisProduct S) * finitePrimeBasisProduct S :=
    hz.2.symm.trans hencode
  have huniq := freshPrimeMixedRadix_eq_iff hS hz.1.1 hz.1.2
    hcoord.1 hcoord.2
  exact Prod.ext (huniq.mp heq).1 (huniq.mp heq).2

/-- The digit of a canonical orbit point `r + d*M` is exactly `d`. -/
theorem squareAnchorFreshPrimeBlockDigit_lift
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S)
    {q r d : ℕ} (_hq : Nat.Prime q)
    (hr : r < finitePrimeBasisProduct S) (hd : d < q) :
    squareAnchorFreshPrimeBlockDigit S q
      (r + d * finitePrimeBasisProduct S) = d := by
  have hMpos : 0 < finitePrimeBasisProduct S :=
    Nat.pos_of_ne_zero (finitePrimeBasisProduct_ne_zero hS)
  unfold squareAnchorFreshPrimeBlockDigit squareAnchorPhaseBlockQuotient
  have hquot :
      (r + d * finitePrimeBasisProduct S) /
          finitePrimeBasisProduct S = d := by
    rw [Nat.add_mul_div_right r d hMpos, Nat.div_eq_of_lt hr, Nat.zero_add]
  rw [hquot, Nat.mod_eq_of_lt hd]

/-- Every bounded old coordinate and fresh digit is realized by an explicit
canonical moving anchor in the enlarged period. -/
theorem forall_raw_lift_digit_realized_by_canonical_orbit
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S)
    {q : ℕ} (hq : Nat.Prime q) (hqS : q ∉ S) :
    ∀ r d, r < finitePrimeBasisProduct S → d < q →
      ∃ n, n < q * finitePrimeBasisProduct S ∧
        squareAnchorPhaseRepresentative S n = r ∧
        squareAnchorFreshPrimeBlockDigit S q n = d ∧
        squareAnchorPhaseRepresentative (insert q S) n =
          primeBasisWheelLift S r d := by
  intro r d hr hd
  have hMpos : 0 < finitePrimeBasisProduct S :=
    Nat.pos_of_ne_zero (finitePrimeBasisProduct_ne_zero hS)
  have hlt : r + d * finitePrimeBasisProduct S <
      q * finitePrimeBasisProduct S := by
    calc
      r + d * finitePrimeBasisProduct S <
          finitePrimeBasisProduct S + d * finitePrimeBasisProduct S :=
        Nat.add_lt_add_right hr _
      _ = (d + 1) * finitePrimeBasisProduct S := by ring
      _ ≤ q * finitePrimeBasisProduct S :=
        Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hd)
  have hold : squareAnchorPhaseRepresentative S
      (r + d * finitePrimeBasisProduct S) = r := by
    unfold squareAnchorPhaseRepresentative primeBasisWheelProjection
    rw [Nat.add_mod, Nat.mul_mod_left, Nat.mod_eq_of_lt hr]
    exact Nat.mod_eq_of_lt hr
  have hdigit := squareAnchorFreshPrimeBlockDigit_lift hS hq hr hd
  have hinsert := squareAnchorPhaseRepresentative_insert_eq_old_lift_digit
    hS hq hqS (r + d * finitePrimeBasisProduct S)
  rw [hold, hdigit] at hinsert
  exact ⟨r + d * finitePrimeBasisProduct S, hlt, hold, hdigit, hinsert⟩

/-- On an old lift, enlarged-basis reservation is exactly old reservation or
fresh-prime divisibility. -/
theorem reservedByPrimeBasis_insert_fresh_lift_iff_old_or_fresh
    {S : Finset ℕ} (_hS : IsFinitePrimeBasis S)
    {q r d : ℕ} (_hq : Nat.Prime q) (hqS : q ∉ S) :
    ReservedByPrimeBasis (insert q S)
        (primeBasisWheelLift S r d) ↔
      ReservedByPrimeBasis S r ∨
        q ∣ primeBasisWheelLift S r d := by
  unfold ReservedByPrimeBasis primeBasisWheelLift
  constructor
  · rintro ⟨p, hp, hpdiv⟩
    simp only [Finset.mem_insert] at hp
    rcases hp with rfl | hpS
    · exact Or.inr hpdiv
    · left
      have hpM : p ∣ finitePrimeBasisProduct S :=
        mem_dvd_finitePrimeBasisProduct hpS
      have hpDM : p ∣ d * finitePrimeBasisProduct S :=
        dvd_mul_of_dvd_right hpM d
      have hpdiv' : p ∣ d * finitePrimeBasisProduct S + r := by
        simpa [Nat.add_comm] using hpdiv
      exact ⟨p, hpS, (Nat.dvd_add_iff_right hpDM).mpr hpdiv'⟩
  · intro h
    rcases h with h | h
    · obtain ⟨p, hpS, hpr⟩ := h
      refine ⟨p, Finset.mem_insert_of_mem hpS, ?_⟩
      exact dvd_add hpr (dvd_mul_of_dvd_right
        (mem_dvd_finitePrimeBasisProduct hpS) d)
    · exact ⟨q, Finset.mem_insert_self q S, h⟩

/-- Over an old wheel survivor, the previous classification reduces to the
existing fresh-prime deletion rule. -/
theorem reservedByPrimeBasis_insert_fresh_lift_iff_of_oldSurvivor
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S)
    {q r d : ℕ} (hq : Nat.Prime q) (hqS : q ∉ S)
    (hr : IsPrimeBasisWheelSurvivor S r) :
    ReservedByPrimeBasis (insert q S)
        (primeBasisWheelLift S r d) ↔
      q ∣ primeBasisWheelLift S r d := by
  exact reservedByPrimeBasis_insert_fresh_lift_iff hS hq hqS hr

/-- The unique reserved digit above an old survivor is the existing unique
fresh-prime deleted lift. -/
theorem existsUnique_mixedRadix_deleted_digit_of_oldSurvivor
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S)
    {q r : ℕ} (hq : Nat.Prime q) (hqS : q ∉ S)
    (hr : IsPrimeBasisWheelSurvivor S r) :
    ∃! d : ℕ, d < q ∧
      ReservedByPrimeBasis (insert q S) (primeBasisWheelLift S r d) :=
  existsUnique_reservedByPrimeBasis_insert_fresh_lift hS hq hqS hr

/-- The canonical orbit visits every fresh digit above a fixed old coordinate. -/
theorem squareAnchorFreshPrimeBlockDigit_fixed_old_coordinate
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S)
    {q r : ℕ} (hq : Nat.Prime q)
    (hr : r < finitePrimeBasisProduct S) :
    ∀ d, d < q →
      squareAnchorFreshPrimeBlockDigit S q
        (r + d * finitePrimeBasisProduct S) = d := by
  intro d hd
  exact squareAnchorFreshPrimeBlockDigit_lift hS hq hr hd

/-- Visible L030 regression: old coordinate `4` traverses all five digits and
the corresponding enlarged representatives in `[0,30)`. -/
theorem squareAnchorMixedRadixAudit_two_three_four_to_twenty_eight_regression :
    squareAnchorFreshPrimeBlockDigit ({2, 3} : Finset ℕ) 5 4 = 0 ∧
      squareAnchorFreshPrimeBlockDigit ({2, 3} : Finset ℕ) 5 10 = 1 ∧
      squareAnchorFreshPrimeBlockDigit ({2, 3} : Finset ℕ) 5 16 = 2 ∧
      squareAnchorFreshPrimeBlockDigit ({2, 3} : Finset ℕ) 5 22 = 3 ∧
      squareAnchorFreshPrimeBlockDigit ({2, 3} : Finset ℕ) 5 28 = 4 ∧
      squareAnchorPhaseRepresentative (insert 5 ({2, 3} : Finset ℕ)) 4 = 4 ∧
      squareAnchorPhaseRepresentative (insert 5 ({2, 3} : Finset ℕ)) 10 = 10 ∧
      squareAnchorPhaseRepresentative (insert 5 ({2, 3} : Finset ℕ)) 16 = 16 ∧
      squareAnchorPhaseRepresentative (insert 5 ({2, 3} : Finset ℕ)) 22 = 22 ∧
      squareAnchorPhaseRepresentative (insert 5 ({2, 3} : Finset ℕ)) 28 = 28 := by
  have hS : IsFinitePrimeBasis ({2, 3} : Finset ℕ) := by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl <;> norm_num
  have hq : Nat.Prime 5 := by norm_num
  have hqS : 5 ∉ ({2, 3} : Finset ℕ) := by simp
  have h0 := squareAnchorFreshPrimeBlockDigit_lift hS hq (r := 4) (d := 0)
    (by norm_num [finitePrimeBasisProduct]) (by norm_num)
  have h1 := squareAnchorFreshPrimeBlockDigit_lift hS hq (r := 4) (d := 1)
    (by norm_num [finitePrimeBasisProduct]) (by norm_num)
  have h2 := squareAnchorFreshPrimeBlockDigit_lift hS hq (r := 4) (d := 2)
    (by norm_num [finitePrimeBasisProduct]) (by norm_num)
  have h3 := squareAnchorFreshPrimeBlockDigit_lift hS hq (r := 4) (d := 3)
    (by norm_num [finitePrimeBasisProduct]) (by norm_num)
  have h4 := squareAnchorFreshPrimeBlockDigit_lift hS hq (r := 4) (d := 4)
    (by norm_num [finitePrimeBasisProduct]) (by norm_num)
  have r0 := squareAnchorPhaseRepresentative_insert_eq_old_lift_digit
    hS hq hqS 4
  have r1 := squareAnchorPhaseRepresentative_insert_eq_old_lift_digit
    hS hq hqS 10
  have r2 := squareAnchorPhaseRepresentative_insert_eq_old_lift_digit
    hS hq hqS 16
  have r3 := squareAnchorPhaseRepresentative_insert_eq_old_lift_digit
    hS hq hqS 22
  have r4 := squareAnchorPhaseRepresentative_insert_eq_old_lift_digit
    hS hq hqS 28
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert h0 using 1; norm_num [squareAnchorFreshPrimeBlockDigit,
      squareAnchorPhaseBlockQuotient, finitePrimeBasisProduct]
  · convert h1 using 1; norm_num [squareAnchorFreshPrimeBlockDigit,
      squareAnchorPhaseBlockQuotient, finitePrimeBasisProduct]
  · convert h2 using 1; norm_num [squareAnchorFreshPrimeBlockDigit,
      squareAnchorPhaseBlockQuotient, finitePrimeBasisProduct]
  · convert h3 using 1; norm_num [squareAnchorFreshPrimeBlockDigit,
      squareAnchorPhaseBlockQuotient, finitePrimeBasisProduct]
  · convert h4 using 1; norm_num [squareAnchorFreshPrimeBlockDigit,
      squareAnchorPhaseBlockQuotient, finitePrimeBasisProduct]
  · convert r0 using 1; norm_num [squareAnchorPhaseRepresentative,
      primeBasisWheelProjection, primeBasisWheelLift,
      squareAnchorFreshPrimeBlockDigit, squareAnchorPhaseBlockQuotient,
      finitePrimeBasisProduct]
  · convert r1 using 1; norm_num [squareAnchorPhaseRepresentative,
      primeBasisWheelProjection, primeBasisWheelLift,
      squareAnchorFreshPrimeBlockDigit, squareAnchorPhaseBlockQuotient,
      finitePrimeBasisProduct]
  · convert r2 using 1; norm_num [squareAnchorPhaseRepresentative,
      primeBasisWheelProjection, primeBasisWheelLift,
      squareAnchorFreshPrimeBlockDigit, squareAnchorPhaseBlockQuotient,
      finitePrimeBasisProduct]
  · convert r3 using 1; norm_num [squareAnchorPhaseRepresentative,
      primeBasisWheelProjection, primeBasisWheelLift,
      squareAnchorFreshPrimeBlockDigit, squareAnchorPhaseBlockQuotient,
      finitePrimeBasisProduct]
  · convert r4 using 1; norm_num [squareAnchorPhaseRepresentative,
      primeBasisWheelProjection, primeBasisWheelLift,
      squareAnchorFreshPrimeBlockDigit, squareAnchorPhaseBlockQuotient,
      finitePrimeBasisProduct]

end DkMath.NumberTheory.PrimorialUniverse
