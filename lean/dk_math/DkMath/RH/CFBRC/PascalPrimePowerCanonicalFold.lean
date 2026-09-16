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

/-- The powered primitive mode is the complex power of its natural label. -/
theorem eulerPrimePowerMode_eq_primePower_cpow_neg
    {p j : ℕ} (hp : Nat.Prime p) (s : ℂ) :
    eulerPrimePowerMode p j s = (((p ^ j : ℕ) : ℂ) ^ (-s)) := by
  rw [eulerPrimePowerMode, eulerPrimePrimitiveMode_eq_cpow_neg hp]
  calc
    ((p : ℂ) ^ (-s)) ^ j = (p : ℂ) ^ ((j : ℂ) * (-s)) := by
      symm
      exact Complex.cpow_nat_mul (p : ℂ) j (-s)
    _ = ((p : ℂ) ^ j) ^ (-s) := by
      exact Complex.natCast_cpow_natCast_mul p j (-s)
    _ = (((p ^ j : ℕ) : ℂ) ^ (-s)) := by
      simp only [Nat.cast_pow]

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
  rw [dite_eq_left hq, dite_eq_left hq]
  let p := Classical.choose hq
  have hp := Classical.choose_spec hq
  let k := Classical.choose hp
  have hk := Classical.choose_spec hp
  exact ⟨hk.1, hk.2.1, hk.2.2⟩

/-- The canonical shadow cost reads `log p` on any prime-power witness. -/
theorem canonicalPrimePowerShadowCost_eq_log_of_witness
    {q p j : ℕ} (hp : Nat.Prime p) (hj : 0 < j) (hq : q = p ^ j) :
    canonicalPrimePowerShadowCost q = Real.log (p : ℝ) := by
  have hs := primePowerShadow_spec (q := q) ⟨p, j, hp, hj, hq⟩
  have hu := primePower_witness_unique hs.1 hp hs.2.1 hj hs.2.2 hq
  unfold canonicalPrimePowerShadowCost
  rw [dite_eq_left ⟨p, j, hp, hj, hq⟩, hu.1]

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

/-- A pair-support summand agrees with the canonical summand at its label. -/
theorem primePowerPair_summand_eq_canonical
    {X : ℕ} {pk : ℕ × ℕ}
    (hpk : pk ∈ pascalPrimePowerPairSupportUpTo X) (s : ℂ) :
    (Real.log (pk.1 : ℝ) : ℂ) *
        eulerPrimePowerMode pk.1 (pk.2 + 1) s =
      (canonicalPrimePowerShadowCost (primePowerPairLabel pk) : ℂ) *
        (((primePowerPairLabel pk : ℕ) : ℂ) ^ (-s)) := by
  have hs := mem_pascalPrimePowerPairSupportUpTo_iff.mp hpk
  have hp := (mem_pascalPrimeCoordinateSupportUpTo_iff.mp hs.1).1
  have hcost := canonicalPrimePowerShadowCost_eq_log_of_witness hp (by omega)
    (q := primePowerPairLabel pk) (p := pk.1) (j := pk.2 + 1) rfl
  rw [hcost, eulerPrimePowerMode_eq_primePower_cpow_neg hp]
  simp [primePowerPairLabel, Nat.cast_pow]

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

/-- The canonical range sum restricted to its prime-power support. -/
theorem pascalPrimePowerPHZCanonicalUpTo_eq_support_sum
    (X : ℕ) (s : ℂ) :
    pascalPrimePowerPHZCanonicalUpTo X s =
      ∑ q ∈ canonicalPrimePowerSupportUpTo X,
        (canonicalPrimePowerShadowCost q : ℂ) * ((q : ℂ) ^ (-s)) := by
  classical
  unfold pascalPrimePowerPHZCanonicalUpTo canonicalPrimePowerSupportUpTo
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro q hq
  by_cases h : IsPrimePowerLabel q <;> simp [canonicalPrimePowerShadowCost, h]

/-- The original nested finite PHZ sum, packaged over its actual pair support. -/
theorem pascalPrimePowerPHZFiniteUpTo_eq_pairSupport_sum
    (X : ℕ) (s : ℂ) :
    pascalPrimePowerPHZFiniteUpTo X s =
      ∑ pk ∈ pascalPrimePowerPairSupportUpTo X,
        (Real.log (pk.1 : ℝ) : ℂ) *
          eulerPrimePowerMode pk.1 (pk.2 + 1) s := by
  classical
  unfold pascalPrimePowerPHZFiniteUpTo pascalPrimePowerPairSupportUpTo
  rw [Finset.sum_filter]
  exact (Finset.sum_product'
    (pascalPrimeCoordinateSupportUpTo X) (Finset.range X)
    (fun p k => if p ^ (k + 1) ≤ X then
      (Real.log (p : ℝ) : ℂ) * eulerPrimePowerMode p (k + 1) s else 0)).symm

/-- The PPW finite prime-power polynomial is the canonical finite `q` fold. -/
theorem pascalPrimePowerPHZFiniteUpTo_eq_canonical
    (X : ℕ) (s : ℂ) :
    pascalPrimePowerPHZFiniteUpTo X s =
      pascalPrimePowerPHZCanonicalUpTo X s := by
  classical
  rw [pascalPrimePowerPHZFiniteUpTo_eq_pairSupport_sum,
    pascalPrimePowerPHZCanonicalUpTo_eq_support_sum,
    ← image_primePowerPairLabel_support_eq_canonicalSupport]
  apply Finset.sum_bij (fun pk _ => primePowerPairLabel pk)
  · intro pk hpk
    exact Finset.mem_image.mpr ⟨pk, hpk, rfl⟩
  · intro a ha b hb hab
    exact primePowerPairLabel_injOn X ha hb hab
  · intro q hq
    rcases Finset.mem_image.mp hq with ⟨pk, hpk, rfl⟩
    exact ⟨pk, hpk, rfl⟩
  · intro pk hpk
    exact primePowerPair_summand_eq_canonical hpk s

end DkMath.RH.CFBRCProjection
