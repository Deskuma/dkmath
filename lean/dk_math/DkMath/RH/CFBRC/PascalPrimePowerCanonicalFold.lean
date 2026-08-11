/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.PascalPrimePowerPHZFinite
import DkMath.NumberTheory.PrimitiveSet.VonMangoldtShadow
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.PascalPrimePowerCanonicalFold"

/-!
# Canonical prime-power labels and the finite `q` fold

This module records the arithmetic part of the PPW construction: a positive
prime-power label has one base prime and one exponent, and the corresponding
prime-power mode is the natural-label complex power.  The resulting shadow is
finite and arithmetic.  It is deliberately not identified with an analytic
von Mangoldt function, `-ζ'/ζ`, an infinite series, or RH.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open DkMath.NumberTheory
open DkMath.NumberTheory.PrimitiveSet

local instance propDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- Equal positive powers of primes have the same base prime. -/
theorem prime_eq_of_pow_eq_pow
    {p q a b : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (ha : 0 < a) (_hb : 0 < b) (hpow : p ^ a = q ^ b) : p = q := by
  have hp_dvd : p ∣ q ^ b := by
    rw [← hpow]
    exact dvd_pow_self p (Nat.ne_of_gt ha)
  have hpq : p ∣ q := (hp.dvd_of_dvd_pow hp_dvd)
  rcases (Nat.dvd_prime hq).mp hpq with hp_one | hp_eq
  · exact False.elim (hp.ne_one hp_one)
  · exact hp_eq

/-- A prime has injective natural powers. -/
theorem prime_pow_exponent_injective
    {p a b : ℕ} (hp : Nat.Prime p) (hpow : p ^ a = p ^ b) : a = b := by
  exact Nat.pow_right_injective hp.one_lt hpow

/-- Positive prime-power witnesses of one natural number are unique. -/
theorem primePower_witness_unique
    {p q a b n : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (ha : 0 < a) (hb : 0 < b) (hpw : n = p ^ a) (hqw : n = q ^ b) :
    p = q ∧ a = b := by
  have hbase : p = q := prime_eq_of_pow_eq_pow hp hq ha hb (hpw.symm.trans hqw)
  refine ⟨hbase, ?_⟩
  apply prime_pow_exponent_injective hp
  simpa [hbase] using hpw.symm.trans hqw

/-- The chosen base prime of a positive prime-power natural number. -/
noncomputable def primePowerBaseShadow (q : ℕ) : ℕ :=
  if hq : IsPrimePowerLabel q then Classical.choose hq else 1

/-- The finite von-Mangoldt shadow cost attached canonically to `q`. -/
noncomputable def canonicalPrimePowerShadowCost (q : ℕ) : ℝ :=
  if _hq : IsPrimePowerLabel q then
    Real.log (primePowerBaseShadow q : ℝ)
  else 0

/-! ### Canonical exponent and finite supports -/

/-- The positive exponent selected together with `primePowerBaseShadow`. -/
noncomputable def primePowerExponentShadow (q : ℕ) : ℕ :=
  if hq : IsPrimePowerLabel q then
    Classical.choose (Classical.choose_spec hq)
  else 0

/-- The finite `(prime, exponent-index)` support used by the PPW pair sum. -/
def pascalPrimePowerPairSupportUpTo (X : ℕ) : Finset (ℕ × ℕ) :=
  ((pascalPrimeCoordinateSupportUpTo X).product (Finset.range X)).filter
    (fun pk => pk.1 ^ (pk.2 + 1) ≤ X)

/-- The finite canonical natural-label support below the cutoff. -/
noncomputable def canonicalPrimePowerSupportUpTo (X : ℕ) : Finset ℕ :=
  (Finset.range (X + 1)).filter IsPrimePowerLabel

/-- The natural label represented by a PPW pair. -/
def primePowerPairLabel (pk : ℕ × ℕ) : ℕ := pk.1 ^ (pk.2 + 1)

/-- Membership in the finite prime/exponent support with the natural cutoff. -/
@[simp] theorem mem_pascalPrimePowerPairSupportUpTo_iff
    {X : ℕ} {pk : ℕ × ℕ} :
    pk ∈ pascalPrimePowerPairSupportUpTo X ↔
      pk.1 ∈ pascalPrimeCoordinateSupportUpTo X ∧
        pk.2 < X ∧ pk.1 ^ (pk.2 + 1) ≤ X := by
  simp [pascalPrimePowerPairSupportUpTo, Finset.mem_product]
  tauto

/-- Membership in the canonical prime-power support below `X`. -/
@[simp] theorem mem_canonicalPrimePowerSupportUpTo_iff
    {X q : ℕ} :
    q ∈ canonicalPrimePowerSupportUpTo X ↔
      q ≤ X ∧ IsPrimePowerLabel q := by
  simp [canonicalPrimePowerSupportUpTo]

/-- The canonical base and exponent form a valid prime-power witness. -/
theorem primePowerShadow_spec
    {q : ℕ} (hq : IsPrimePowerLabel q) :
    Nat.Prime (primePowerBaseShadow q) ∧
      0 < primePowerExponentShadow q ∧
      q = primePowerBaseShadow q ^ primePowerExponentShadow q := by
  unfold primePowerBaseShadow primePowerExponentShadow
  rw [dif_pos hq, dif_pos hq]
  let p := Classical.choose hq
  have hp := Classical.choose_spec hq
  let k := Classical.choose hp
  have hk := Classical.choose_spec hp
  exact ⟨hk.1, hk.2.1, hk.2.2⟩

/-- The pair label is injective on one finite prime-power support. -/
theorem primePowerPairLabel_injOn (X : ℕ) :
    Set.InjOn primePowerPairLabel
      (↑(pascalPrimePowerPairSupportUpTo X) : Set (ℕ × ℕ)) := by
  intro a ha b hb hab
  have ha' := mem_pascalPrimePowerPairSupportUpTo_iff.mp ha
  have hb' := mem_pascalPrimePowerPairSupportUpTo_iff.mp hb
  have hpa : Nat.Prime a.1 :=
    (mem_pascalPrimeCoordinateSupportUpTo_iff.mp ha'.1).1
  have hpb : Nat.Prime b.1 :=
    (mem_pascalPrimeCoordinateSupportUpTo_iff.mp hb'.1).1
  have haexp : 0 < a.2 + 1 := by omega
  have hbexp : 0 < b.2 + 1 := by omega
  have hw := primePower_witness_unique hpa hpb haexp hbexp
    (by rfl) (by simpa [primePowerPairLabel] using hab)
  have hbase : a.1 = b.1 := hw.1
  have hexp : a.2 + 1 = b.2 + 1 := hw.2
  apply Prod.ext
  · exact hbase
  · omega

/-- The pair-label image is exactly the canonical support below `X`. -/
theorem image_primePowerPairLabel_support_eq_canonicalSupport
    (X : ℕ) :
    (pascalPrimePowerPairSupportUpTo X).image primePowerPairLabel =
      canonicalPrimePowerSupportUpTo X := by
  ext q
  constructor
  · intro hq
    rcases Finset.mem_image.mp hq with ⟨pk, hpk, rfl⟩
    have hsupport := mem_pascalPrimePowerPairSupportUpTo_iff.mp hpk
    have hpX := (mem_pascalPrimeCoordinateSupportUpTo_iff.mp hsupport.1).2
    have hprime := (mem_pascalPrimeCoordinateSupportUpTo_iff.mp hsupport.1).1
    have hpow : pk.1 ^ (pk.2 + 1) ≤ X := hsupport.2.2
    have hlabel : IsPrimePowerLabel (primePowerPairLabel pk) :=
      ⟨pk.1, pk.2 + 1, hprime, by omega, rfl⟩
    exact mem_canonicalPrimePowerSupportUpTo_iff.mpr ⟨hpow, hlabel⟩
  · intro hq
    have hcanon := mem_canonicalPrimePowerSupportUpTo_iff.mp hq
    rcases primePowerShadow_spec hcanon.2 with ⟨hp, hj, hqpow⟩
    let pk : ℕ × ℕ := (primePowerBaseShadow q,
      primePowerExponentShadow q - 1)
    have hqpos : 0 < q := by
      rw [hqpow]
      exact pow_pos hp.pos _
    have hp_dvd : primePowerBaseShadow q ∣ q := by
      calc
        primePowerBaseShadow q ∣
            primePowerBaseShadow q ^ primePowerExponentShadow q :=
          dvd_pow_self _ (Nat.ne_of_gt hj)
        _ = q := hqpow.symm
    have hpX : primePowerBaseShadow q ≤ X := by
      exact (Nat.le_of_dvd (by omega) hp_dvd).trans hcanon.1
    have hjlt : primePowerExponentShadow q < q := by
      calc
        primePowerExponentShadow q <
            primePowerBaseShadow q ^ primePowerExponentShadow q :=
          Nat.lt_pow_self hp.one_lt
        _ = q := hqpow.symm
    have hpk : pk ∈ pascalPrimePowerPairSupportUpTo X := by
      dsimp [pk]
      apply mem_pascalPrimePowerPairSupportUpTo_iff.mpr
      refine ⟨?_, ?_, ?_⟩
      · exact mem_pascalPrimeCoordinateSupportUpTo_iff.mpr ⟨hp, hpX⟩
      · omega
      · calc
          primePowerBaseShadow q ^
              (primePowerExponentShadow q - 1 + 1) = q := by
            rw [Nat.sub_add_cancel hj]
            exact hqpow.symm
          _ ≤ X := hcanon.1
    refine Finset.mem_image.mpr ⟨pk, hpk, ?_⟩
    change primePowerBaseShadow q ^
      (primePowerExponentShadow q - 1 + 1) = q
    rw [Nat.sub_add_cancel hj]
    exact hqpow.symm

/-- The finite canonical `q`-indexed Dirichlet polynomial. -/
noncomputable def pascalPrimePowerPHZCanonicalUpTo
    (X : ℕ) (s : ℂ) : ℂ :=
  ∑ q ∈ Finset.range (X + 1),
    (canonicalPrimePowerShadowCost q : ℂ) * ((q : ℂ) ^ (-s))

@[simp] theorem pascalPrimePowerPHZCanonicalUpTo_zero (s : ℂ) :
    pascalPrimePowerPHZCanonicalUpTo 0 s = 0 := by
  classical
  have hzero : ¬ IsPrimePowerLabel 0 := by
    rintro ⟨p, k, hp, hk, hpow⟩
    have : 0 < p ^ k := pow_pos hp.pos k
    omega
  simp [pascalPrimePowerPHZCanonicalUpTo, canonicalPrimePowerShadowCost, hzero]

end DkMath.RH.CFBRCProjection
