/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.PrimorialUniverse.UnitCoordinateRefinement

#print "file: DkMath.NumberTheory.PrimorialUniverse.CommonLattice"

/-!
# Coprime common-lattice fibers

This module studies two positive unit universes with one coprime integer
synchronization.  If `a * u₁ = b * u₂` and `a,b` are coprime, every common
coordinate pair is exactly `(a*t,b*t)` for one natural parameter `t`.

The resulting prime-to-prime statement concerns coordinates in the two chosen
units.  It does not say that the shared real point is prime or composite, and
it does not classify rational or irrational unit ratios.  Primorial wheels,
PowerSwap, and Legendre remain outside this checkpoint.
-/

namespace DkMath.NumberTheory.PrimorialUniverse

/-! ## Synchronization vocabulary -/

/-- `u₁` and `u₂` are synchronized by the common positive point `a*u₁=b*u₂`.

The first argument is the coordinate in `u₁`, the second in `u₂`; the two
coordinates are required to be positive and coprime.
-/
def UnitSynchronizesBy
    (u₁ u₂ : PositiveUnit) (a b : ℕ) : Prop :=
  0 < a ∧
  0 < b ∧
  Nat.Coprime a b ∧
  (a : ℝ) * u₁.val = (b : ℝ) * u₂.val

/-- A real point has the two displayed natural coordinates simultaneously. -/
def HasCommonUnitCoordinates
    (u₁ u₂ : PositiveUnit) (m n : ℕ) (X : ℝ) : Prop :=
  HasUnitCoordinate u₁ m X ∧
  HasUnitCoordinate u₂ n X

@[simp] theorem unitSynchronizesBy_iff
    (u₁ u₂ : PositiveUnit) (a b : ℕ) :
    UnitSynchronizesBy u₁ u₂ a b ↔
      0 < a ∧ 0 < b ∧ Nat.Coprime a b ∧
        (a : ℝ) * u₁.val = (b : ℝ) * u₂.val :=
  Iff.rfl

@[simp] theorem hasCommonUnitCoordinates_iff
    (u₁ u₂ : PositiveUnit) (m n : ℕ) (X : ℝ) :
    HasCommonUnitCoordinates u₁ u₂ m n X ↔
      HasUnitCoordinate u₁ m X ∧ HasUnitCoordinate u₂ n X :=
  Iff.rfl

/-! ## Canonical points and their multiples -/

/-- The synchronized coefficients themselves name a common real point. -/
theorem syncCoordinates_have_common_point
    {u₁ u₂ : PositiveUnit} {a b : ℕ}
    (hsync : UnitSynchronizesBy u₁ u₂ a b) :
    HasCommonUnitCoordinates u₁ u₂ a b ((a : ℝ) * u₁.val) := by
  refine ⟨?_, ?_⟩
  · rfl
  · exact hsync.2.2.2

/-- Every natural multiple of the synchronized point is common. -/
theorem syncCoordinates_multiple_has_common_point
    {u₁ u₂ : PositiveUnit} {a b t : ℕ}
    (hsync : UnitSynchronizesBy u₁ u₂ a b) :
    HasCommonUnitCoordinates u₁ u₂ (a * t) (b * t)
      (((a * t : ℕ) : ℝ) * u₁.val) := by
  refine ⟨?_, ?_⟩
  · rfl
  · calc
      (((a * t : ℕ) : ℝ) * u₁.val) =
          (t : ℝ) * ((a : ℝ) * u₁.val) := by
            simp only [Nat.cast_mul]
            ring
      _ = (t : ℝ) * ((b : ℝ) * u₂.val) := by
            rw [hsync.2.2.2]
      _ = (((b * t : ℕ) : ℝ) * u₂.val) := by
            simp only [Nat.cast_mul]
            ring

/-! ## Cross multiplication and coprime divisibility -/

/-- Two common coordinate pairs lie on the same cross-multiplication line. -/
theorem commonCoordinates_cross_mul
    {u₁ u₂ : PositiveUnit} {a b m n : ℕ}
    (hsync : (a : ℝ) * u₁.val = (b : ℝ) * u₂.val)
    (hcommon : (m : ℝ) * u₁.val = (n : ℝ) * u₂.val) :
    b * m = a * n := by
  have hprod :
      (a : ℝ) * ((n : ℝ) * u₂.val) =
        (b : ℝ) * ((m : ℝ) * u₂.val) := by
    calc
      (a : ℝ) * ((n : ℝ) * u₂.val) =
          (a : ℝ) * ((m : ℝ) * u₁.val) := by rw [hcommon]
      _ = (m : ℝ) * ((a : ℝ) * u₁.val) := by ring
      _ = (m : ℝ) * ((b : ℝ) * u₂.val) := by rw [hsync]
      _ = (b : ℝ) * ((m : ℝ) * u₂.val) := by ring
  have hreal :
      (a : ℝ) * (n : ℝ) = (b : ℝ) * (m : ℝ) := by
    apply mul_right_cancel₀ (ne_of_gt u₂.pos)
    simpa only [mul_assoc] using hprod
  exact_mod_cast hreal.symm

/-- Coprime synchronization coefficients divide every common coordinate. -/
theorem commonCoordinates_divisible_by_syncCoordinates
    {a b m n : ℕ}
    (hcop : Nat.Coprime a b)
    (hcross : b * m = a * n) :
    a ∣ m ∧ b ∣ n := by
  have ha : a ∣ b * m := by
    rw [hcross]
    exact dvd_mul_right a n
  have hb : b ∣ a * n := by
    rw [← hcross]
    exact dvd_mul_right b m
  exact ⟨hcop.dvd_of_dvd_mul_left ha,
    hcop.symm.dvd_of_dvd_mul_left hb⟩

/-! ## The canonical common-lattice fiber -/

/-- Every common coordinate pair is one coprime synchronization fiber. -/
theorem commonCoordinates_eq_sync_mul
    {u₁ u₂ : PositiveUnit} {a b m n : ℕ}
    (hsync : UnitSynchronizesBy u₁ u₂ a b)
    (hcommon :
      ∃ X : ℝ,
        HasUnitCoordinate u₁ m X ∧
        HasUnitCoordinate u₂ n X) :
    ∃ t : ℕ,
      m = a * t ∧
      n = b * t := by
  obtain ⟨X, hm, hn⟩ := hcommon
  have hcross : b * m = a * n :=
    commonCoordinates_cross_mul hsync.2.2.2 (hm.symm.trans hn)
  have hdvd : a ∣ m ∧ b ∣ n :=
    commonCoordinates_divisible_by_syncCoordinates hsync.2.2.1 hcross
  obtain ⟨t, ht⟩ := hdvd.1
  refine ⟨t, ht, ?_⟩
  have hcancel : a * (b * t) = a * n := by
    calc
      a * (b * t) = b * (a * t) := by ac_rfl
      _ = b * m := by rw [ht]
      _ = a * n := hcross
  exact Nat.mul_left_cancel hsync.1 hcancel.symm

/-- The common coordinate relation is exactly the canonical fiber. -/
theorem commonCoordinates_iff_sync_mul
    {u₁ u₂ : PositiveUnit} {a b m n : ℕ}
    (hsync : UnitSynchronizesBy u₁ u₂ a b) :
    (∃ X : ℝ,
      HasCommonUnitCoordinates u₁ u₂ m n X) ↔
      ∃ t : ℕ, m = a * t ∧ n = b * t := by
  constructor
  · intro hcommon
    exact commonCoordinates_eq_sync_mul hsync hcommon
  · rintro ⟨t, rfl, rfl⟩
    exact ⟨((a * t : ℕ) : ℝ) * u₁.val,
      syncCoordinates_multiple_has_common_point hsync⟩

/-- Positive multiplication has a unique fiber parameter. -/
theorem sync_mul_parameter_unique
    {a _b t s : ℕ}
    (ha : 0 < a)
    (h : a * t = a * s) :
    t = s :=
  Nat.mul_left_cancel ha h

/-! ## Prime-to-prime synchronization consumer -/

/-- Distinct prime synchronization has one prime-coordinate common pair.

There are still infinitely many common points `(p*t,q*t)`; this theorem says
only that the pair whose two natural coordinates are both prime is `(p,q)`.
-/
theorem distinctPrimeSynchronization_unique_primeCoordinatePair
    {u₁ u₂ : PositiveUnit} {p q r s : ℕ}
    (hp : Nat.Prime p)
    (hq : Nat.Prime q)
    (hpq : p ≠ q)
    (hsync : (p : ℝ) * u₁.val = (q : ℝ) * u₂.val)
    (hr : Nat.Prime r)
    (_hs : Nat.Prime s)
    (hcommon :
      ∃ X : ℝ,
        HasUnitCoordinate u₁ r X ∧
        HasUnitCoordinate u₂ s X) :
    r = p ∧ s = q := by
  have hsync' : UnitSynchronizesBy u₁ u₂ p q :=
    ⟨hp.pos, hq.pos, (Nat.coprime_primes hp hq).mpr hpq, hsync⟩
  obtain ⟨t, hrt, hst⟩ := commonCoordinates_eq_sync_mul hsync' hcommon
  have hpt_prime : Nat.Prime (p * t) := hrt ▸ hr
  have ht : t = 1 := by
    rcases (Nat.prime_mul_iff.mp hpt_prime) with h | h
    · exact h.2
    · exact False.elim (hp.ne_one h.2)
  exact ⟨by simpa [ht] using hrt, by simpa [ht] using hst⟩

/-! ## Same-coordinate edge case -/

/-- A positive same-coordinate synchronization forces equal unit values. -/
theorem sameCoordinate_synchronization_unit_eq
    {u₁ u₂ : PositiveUnit} {p : ℕ}
    (hp : 0 < p)
    (hsync : (p : ℝ) * u₁.val = (p : ℝ) * u₂.val) :
    u₁.val = u₂.val := by
  have hp0 : (p : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hp)
  exact mul_left_cancel₀ hp0 hsync

/-! ## Small synchronization regression -/

/-- The integer-valued pair `2*3 = 3*2` is a coprime synchronization. -/
def regressionUnitThree : PositiveUnit :=
  ⟨3, by norm_num⟩

def regressionUnitTwo : PositiveUnit :=
  ⟨2, by norm_num⟩

theorem two_three_synchronization_regression :
    UnitSynchronizesBy regressionUnitThree regressionUnitTwo 2 3 := by
  norm_num [UnitSynchronizesBy, regressionUnitThree, regressionUnitTwo]

theorem two_three_common_point_regression :
    HasCommonUnitCoordinates regressionUnitThree regressionUnitTwo 2 3 6 := by
  norm_num [HasCommonUnitCoordinates, HasUnitCoordinate,
    regressionUnitThree, regressionUnitTwo]

end DkMath.NumberTheory.PrimorialUniverse
