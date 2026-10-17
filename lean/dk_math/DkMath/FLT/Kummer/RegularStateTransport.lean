/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Kummer.RegularDescentPowers
import DkMath.Lib.NumberTheory.CosmicRamifiedPrimePower
import DkMath.Lib.Cosmic.GNPhaseThreeTerm

#print "file: DkMath.FLT.Kummer.RegularStateTransport"

/-!
# Conditional prime-degree Kummer descent

This is an actual reconstruction, not a provider that assumes a descent step.
Its inputs are a ramified phase packet, Dedekind structure, `p ≥ 3`, oddness,
ramification `(p) ∣ λ^(p-1)`, class-group p-torsion-freeness, and the Kummer
unit criterion. Three roots from the same phase family supply the new state.

The endpoint excludes positive-depth states. An oriented primitive Case II
integer entrance is provided below. General Case I and orientation of arbitrary
integer counterexamples remain separate FLT entrance obligations.
-/

namespace DkMath.FLT.Kummer.RegularDescent

open DkMath.Lib.NumberTheory
open scoped BigOperators

section Domain

variable {R : Type*} [CommRing R] [IsDomain R]
variable {p : ℕ} [hp : Fact p.Prime] {P : RamifiedPhasePacket R p}

/-- Arithmetic inputs beyond the neutral phase packet. These hypotheses are
proved by concrete providers; none is inferred from GN identities alone. -/
structure Conditions (P : RamifiedPhasePacket R p) : Prop where
  odd : Odd p
  three_le : 3 ≤ p
  ramification : (p : R) ∣ P.lambda ^ (p - 1)
  class_group : classGroupPTorsionFreeAt R p
  unit_power : KummerUnitPowerCriterion R p

/-- The residue inverse gives a Bezout witness even in a non-PID Dedekind ring. -/
theorem coprime_lambda_of_away {x : R} (hx : ¬ P.lambda ∣ x) : IsCoprime P.lambda x := by
  have hn : P.residue x ≠ 0 := fun h => hx ((P.residue_zero_iff _).mp h)
  let b : R := ((P.residue x)⁻¹).val
  have hd : P.lambda ∣ b * x - 1 := by
    apply (P.residue_zero_iff _).mp
    simp only [map_sub, map_mul, map_one, b, map_natCast, ZMod.natCast_zmod_val]
    rw [inv_mul_cancel₀ hn, sub_self]
  obtain ⟨a, ha⟩ := hd
  refine ⟨-a, b, ?_⟩
  linear_combination ha

/-- Every p-th power is congruent to an integer modulo p. -/
theorem power_congr_integer (hram : (p : R) ∣ P.lambda ^ (p - 1)) (x : R) :
    ∃ n : ℤ, (p : R) ∣ x ^ p - (n : R) := by
  let n : ℤ := (P.residue x).val
  have hn : P.lambda ∣ x - (n : R) := by
    apply (P.residue_zero_iff _).mp
    simp only [map_sub, n, Int.cast_natCast, map_natCast, ZMod.natCast_zmod_val, sub_self]
  obtain ⟨w, hw⟩ := hn
  have hx : x = P.lambda * w + (n : R) := by linear_combination hw
  refine ⟨n ^ p, ?_⟩
  rw [Int.cast_pow, hx]
  apply Nat.Prime.dvd_add_pow_sub_pow_of_dvd (P.lambda * w) (n : R) hp.out
  · rw [mul_pow]
    exact dvd_mul_of_dvd_left (hram.trans (pow_dvd_pow P.lambda (Nat.sub_le p 1))) _
  · exact dvd_mul_right _ _

/-- The weighted equation first gives a p-th-power congruence for its ratio. -/
theorem ratio_congr_power (hodd : Odd p) (hram : (p : R) ∣ P.lambda ^ (p - 1))
    {x y : R} (u v : Rˣ) (hx : ¬ P.lambda ∣ x)
    (h : (p : R) ∣ (u : R) * x ^ p + (v : R) * y ^ p) :
    ∃ a : R, (p : R) ∣ ((u / v : Rˣ) : R) - a ^ p := by
  have hc : IsCoprime (p : R) x :=
    (coprime_lambda_of_away hx).pow_left.of_isCoprime_of_dvd_left hram
  obtain ⟨a, b, hab⟩ := hc
  have hbx : (p : R) ∣ b * x - 1 := by
    refine ⟨-a, ?_⟩
    linear_combination hab
  have hbpow := hbx.trans (sub_one_dvd_pow_sub_one (b * x) p)
  have hs : (p : R) ∣ ((u / v : Rˣ) : R) * (b * x) ^ p + (b * y) ^ p := by
    convert dvd_mul_of_dvd_right h ((↑v⁻¹ : R) * b ^ p) using 1
    simp only [div_eq_mul_inv, Units.val_mul, mul_pow]
    have hv : (↑v⁻¹ : R) * (v : R) = 1 := v.inv_val
    linear_combination -(b ^ p * y ^ p) * hv
  refine ⟨-(b * y), ?_⟩
  rw [hodd.neg_pow]
  convert dvd_sub hs (dvd_mul_of_dvd_right hbpow (((u / v : Rˣ) : R))) using 1
  ring

/-- Apply the actual Kummer unit criterion to the ratio of the two coefficients. -/
theorem ratio_power (C : Conditions P) {x y : R} (u v : Rˣ) (hx : ¬ P.lambda ∣ x)
    (h : (p : R) ∣ (u : R) * x ^ p + (v : R) * y ^ p) :
    ∃ k : Rˣ, u / v = k ^ p := by
  obtain ⟨a, ha⟩ := ratio_congr_power C.odd C.ramification u v hx h
  obtain ⟨n, hn⟩ := power_congr_integer C.ramification a
  apply C.unit_power
  exact ⟨n, by simpa only [sub_add_sub_cancel] using dvd_add ha hn⟩

/-- The relation uses the same center and endpoints in all three factors. -/
theorem quotient_three_term (q y : R) (i0 i1 i2 : Fin p) :
    (P.slope i2 - P.slope i0) * P.quotient q y i1 +
      (P.slope i0 - P.slope i1) * P.quotient q y i2 =
      (P.slope i2 - P.slope i1) * P.quotient q y i0 := by
  have h := DkMath.Lib.Cosmic.phaseSource_three_term_relation
    (1 - P.slope i1) (1 - P.slope i2) (1 - P.slope i0) q y
  unfold DkMath.Lib.Cosmic.phaseSource at h
  unfold RamifiedPhasePacket.quotient
  linear_combination -h

end Domain

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable {p : ℕ} [hp : Fact p.Prime] {P : RamifiedPhasePacket R p}

/-- Reconstruct a weighted successor from three different roots in the same family. -/
theorem State.exists_weighted_successor (C : Conditions P) {m : ℕ} (E : State P (m + 1)) :
    ∃ (x y z : R) (u v e : Rˣ), IsCoprime x y ∧
      ¬ P.lambda ∣ x ∧ ¬ P.lambda ∣ y ∧ ¬ P.lambda ∣ z ∧
      (u : R) * x ^ p + (v : R) * y ^ p = (e : R) * (P.lambda ^ m * z) ^ p := by
  classical
  obtain ⟨u, b, g, hb, hgfac, hga, ha, hcop⟩ := E.exists_descent_roots C.odd C.class_group
  let i0 := P.distinguished (E.center (by omega)) E.y
  obtain ⟨i1, hi1⟩ := Finset.exists_mem_ne (s := (Finset.univ : Finset (Fin p)))
    (by simp; have := C.three_le; omega) i0
  obtain ⟨i2, hi2, hi21⟩ := Finset.exists_mem_ne
    (s := (Finset.univ.erase i0 : Finset (Fin p))) (by simp; have := C.three_le; omega) i1
  have h10 : i1 ≠ i0 := hi1.2
  have h20 : i2 ≠ i0 := (Finset.mem_erase.mp hi2).1
  have h21 : i2 ≠ i1 := hi21
  let a := (slope_sub_isUnit P h20).unit
  let b' := (slope_sub_isUnit P h10.symm).unit
  let c := (slope_sub_isUnit P h21).unit
  have ha0 : (a : R) = P.slope i2 - P.slope i0 := IsUnit.unit_spec _
  have hb0 : (b' : R) = P.slope i0 - P.slope i1 := IsUnit.unit_spec _
  have hc0 : (c : R) = P.slope i2 - P.slope i1 := IsUnit.unit_spec _
  refine ⟨b i1, b i2, g, a * u i1, b' * u i2, c * u i0,
    hcop _ _ h21.symm, ha _ h10, ha _ h20, hga, ?_⟩
  have hf := quotient_three_term (P := P) (E.center (by omega)) E.y i0 i1 i2
  rw [hb i1, hb i2, hgfac] at hf
  simpa only [Units.val_mul, ha0, hb0, hc0, mul_assoc] using hf

/-- Actual one-step descent at positive target depth. All guards are reconstructed. -/
theorem descent_step (C : Conditions P) (m : ℕ) (hm : 1 ≤ m) :
    Nonempty (State P (m + 1)) → Nonempty (State P m) := by
  rintro ⟨E⟩
  obtain ⟨x, y, z, u, v, e, hxy, hx, hy, hz, he⟩ := E.exists_weighted_successor C
  have hle : p - 1 ≤ m * p := (Nat.sub_le p 1).trans (by simpa using Nat.mul_le_mul_right p hm)
  have hd : (p : R) ∣ (u : R) * x ^ p + (v : R) * y ^ p := by
    rw [he, mul_pow, ← pow_mul]
    exact dvd_mul_of_dvd_right
      (dvd_mul_of_dvd_left (C.ramification.trans (pow_dvd_pow P.lambda hle)) _) _
  obtain ⟨k, hk⟩ := ratio_power C u v hx hd
  obtain ⟨E', _, _, _⟩ := normalize_weighted m x y z u v e k hxy hy hz he hk
  exact ⟨E'⟩

/-- Close positive-depth state descent. This conclusion does not include an FLT entrance. -/
theorem no_state (C : Conditions P) (m : ℕ) (hm : 1 ≤ m) : ¬ Nonempty (State P m) := by
  induction m, hm using Nat.le_induction with
  | base => exact no_state_one C.odd
  | succ m hm ih => exact fun h => ih (descent_step C m hm h)

/-- On integers, the packet's ramified prime detects precisely divisibility by p. -/
theorem lambda_dvd_intCast_iff (P : RamifiedPhasePacket R p) (n : ℤ) :
    P.lambda ∣ (n : R) ↔ (p : ℤ) ∣ n := by
  rw [← P.residue_zero_iff]
  simp only [map_intCast]
  exact ZMod.intCast_zmod_eq_zero_iff_dvd n p

/-- An oriented primitive Case II solution enters positive depth by factoring
the same nonzero integer `c`. This does not assert that every counterexample
can be oriented this way; Case I remains a separate obligation. -/
theorem initial_state_of_int_solution [CharZero R] (P : RamifiedPhasePacket R p)
    {a b c : ℤ} (hc : c ≠ 0) (heq : a ^ p + b ^ p = c ^ p)
    (hcop : IsCoprime a b) (hpc : (p : ℤ) ∣ c) (hpb : ¬ (p : ℤ) ∣ b) :
    ∃ m : ℕ, 1 ≤ m ∧ Nonempty (State P m) := by
  have hcR : (c : R) ≠ 0 := Int.cast_ne_zero.mpr hc
  have hf := FiniteMultiplicity.of_not_isUnit P.lambda_prime.not_isUnit hcR
  obtain ⟨z, hz, hza⟩ := hf.exists_eq_pow_mul_and_not_dvd
  have hld : P.lambda ∣ (c : R) := (lambda_dvd_intCast_iff P c).mpr hpc
  have hm : 1 ≤ multiplicity P.lambda (c : R) :=
    Nat.one_le_iff_ne_zero.mpr ((multiplicity_ne_zero hf).mpr hld)
  refine ⟨_, hm, ⟨{
    x := (a : R), y := (b : R), z := z, epsilon := 1
    coprime := hcop.map (Int.castRingHom R)
    y_away := fun h => hpb ((lambda_dvd_intCast_iff P b).mp h)
    z_away := hza
    equation := ?_ }⟩⟩
  simp only [Units.val_one, one_mul, ← hz]
  exact_mod_cast heq

/-- Conditional Case II exclusion with an explicit integer entrance. -/
theorem not_int_solution_caseII [CharZero R] (C : Conditions P)
    {a b c : ℤ} (hc : c ≠ 0) (hcop : IsCoprime a b)
    (hpc : (p : ℤ) ∣ c) (hpb : ¬ (p : ℤ) ∣ b) : a ^ p + b ^ p ≠ c ^ p := by
  intro heq
  obtain ⟨m, hm, hE⟩ := initial_state_of_int_solution P hc heq hcop hpc hpb
  exact no_state C m hm hE

end DkMath.FLT.Kummer.RegularDescent
