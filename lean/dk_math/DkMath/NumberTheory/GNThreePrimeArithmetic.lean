/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement
import DkMath.NumberTheory.GNPrimeTargetResidue
import DkMath.NumberTheory.GNThreeQuadratic

#print "file: DkMath.NumberTheory.GNThreePrimeArithmetic"

namespace DkMath.NumberTheory

open DkMath.CosmicFormulaBinom

/-!
## Prime arithmetic of the degree-three GN shell

This module separates the ramified prime `3` from the non-ramified prime
divisors of the primitive shell `GN 3 u x`.  The ramified prime cannot
square-lift on coprime coordinates, while every other prime divisor lies in
the `1 mod 3` sector.  Square lifts do occur in that sector; this module
therefore records a classification constraint, not a universal no-lift claim.

The module is pure NumberTheory.  It does not modify or prove the FLT3
application endpoint.
-/

/-- The ramified prime criterion for the dual-oriented cubic shell. -/
theorem three_dvd_GN_three_iff_dvd_boundary
    {u x : ℕ} :
    3 ∣ DkMath.CosmicFormulaBinom.GN 3 u x ↔ 3 ∣ u := by
  rw [GN_three_dual_explicit]
  have hrest : 3 ∣ 3 * u * x + 3 * x ^ 2 := by
    apply Nat.dvd_add
    · rw [Nat.mul_assoc]
      exact dvd_mul_of_dvd_left (Nat.dvd_refl 3) (u * x)
    · exact dvd_mul_of_dvd_left (Nat.dvd_refl 3) (x ^ 2)
  constructor
  · intro h
    have htotal : 3 ∣ u ^ 2 + (3 * u * x + 3 * x ^ 2) := by
      simpa only [← Nat.add_assoc] using h
    have hu2 : 3 ∣ u ^ 2 :=
      (Nat.dvd_add_iff_left (k := 3) (m := u ^ 2)
        (n := 3 * u * x + 3 * x ^ 2) hrest).mpr htotal
    exact Nat.prime_three.dvd_of_dvd_pow hu2
  · intro h
    have hu2 : 3 ∣ u ^ 2 := dvd_pow h (by norm_num)
    have htotal : 3 ∣ u ^ 2 + (3 * u * x + 3 * x ^ 2) :=
      (Nat.dvd_add_iff_left (k := 3) (m := u ^ 2)
        (n := 3 * u * x + 3 * x ^ 2) hrest).mp hu2
    simpa only [← Nat.add_assoc] using htotal

/-- On coprime coordinates, the ramified prime occurs at most once. -/
theorem not_nine_dvd_GN_three_of_coprime
    {u x : ℕ}
    (hcop : Nat.Coprime u x) :
    ¬ 9 ∣ DkMath.CosmicFormulaBinom.GN 3 u x := by
  intro h9
  by_cases h3u : 3 ∣ u
  · rcases h3u with ⟨k, rfl⟩
    have hx3 : ¬ 3 ∣ x := by
      intro h3x
      have h31 : 3 ∣ 1 := by
        rw [← hcop.gcd_eq_one]
        exact Nat.dvd_gcd ⟨k, by simp⟩ h3x
      exact (Nat.Prime.not_dvd_one Nat.prime_three) h31
    have hfactor :
        DkMath.CosmicFormulaBinom.GN 3 (3 * k) x =
          3 * (3 * k ^ 2 + 3 * k * x + x ^ 2) := by
      rw [GN_three_dual_explicit]
      ring
    have h9factor : 9 ∣ 3 * (3 * k ^ 2 + 3 * k * x + x ^ 2) := by
      rw [← hfactor]
      exact h9
    have h3factor : 3 ∣ 3 * k ^ 2 + 3 * k * x + x ^ 2 := by
      rcases h9factor with ⟨t, ht⟩
      refine ⟨t, ?_⟩
      omega
    have hrest : 3 ∣ 3 * k ^ 2 + 3 * k * x := by
      apply Nat.dvd_add
      · exact dvd_mul_of_dvd_left (Nat.dvd_refl 3) (k ^ 2)
      · rw [Nat.mul_assoc]
        exact dvd_mul_of_dvd_left (Nat.dvd_refl 3) (k * x)
    have hx2 : 3 ∣ x ^ 2 := by
      have htotal : 3 ∣ (3 * k ^ 2 + 3 * k * x) + x ^ 2 := by
        exact h3factor
      exact (Nat.dvd_add_iff_right (k := 3)
        (m := 3 * k ^ 2 + 3 * k * x) (n := x ^ 2) hrest).mpr htotal
    exact hx3 (Nat.prime_three.dvd_of_dvd_pow hx2)
  · have h3GN : 3 ∣ DkMath.CosmicFormulaBinom.GN 3 u x := by
      exact dvd_trans (by norm_num : 3 ∣ 9) h9
    exact h3u ((three_dvd_GN_three_iff_dvd_boundary (u := u) (x := x)).mp h3GN)

/-- A prime divisor away from `3` cannot divide the first cubic coordinate. -/
theorem prime_not_dvd_boundary_of_dvd_GN_three_of_coprime_of_ne_three
    {q u x : ℕ}
    (hq : Nat.Prime q)
    (hcop : Nat.Coprime u x)
    (hqGN : q ∣ DkMath.CosmicFormulaBinom.GN 3 u x)
    (hq3 : q ≠ 3) :
    ¬ q ∣ u := by
  intro hqu
  rw [GN_three_dual_explicit] at hqGN
  have hu2 : q ∣ u ^ 2 := dvd_pow hqu (by norm_num)
  have hux : q ∣ 3 * u * x := by
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hqu 3) x
  have hfirst : q ∣ u ^ 2 + 3 * u * x := Nat.dvd_add hu2 hux
  have hsecond : q ∣ 3 * x ^ 2 := by
    exact (Nat.dvd_add_iff_right (k := q) (m := u ^ 2 + 3 * u * x)
      (n := 3 * x ^ 2) hfirst).mpr hqGN
  have hxx : q ∣ x ^ 2 := by
    rcases (hq.dvd_mul.mp hsecond) with hq3' | hxx
    · exfalso
      apply hq3
      exact ((Nat.dvd_prime Nat.prime_three).mp hq3').resolve_left hq.ne_one
    · exact hxx
  have hqgcd : q ∣ Nat.gcd u x :=
    Nat.dvd_gcd hqu (hq.dvd_of_dvd_pow hxx)
  have hqone : q ∣ 1 := by
    rw [hcop.gcd_eq_one] at hqgcd
    exact hqgcd
  exact hq.not_dvd_one hqone

private theorem prime_not_dvd_second_coordinate_of_dvd_GN_three
    {q u x : ℕ}
    (hq : Nat.Prime q)
    (hq_u : ¬ q ∣ u)
    (hqGN : q ∣ DkMath.CosmicFormulaBinom.GN 3 u x) :
    ¬ q ∣ x := by
  intro hqx
  rw [GN_three_dual_explicit] at hqGN
  have hxsq : q ∣ x ^ 2 := dvd_pow hqx (by norm_num)
  have hrest : q ∣ 3 * u * x + 3 * x ^ 2 := by
    apply Nat.dvd_add
    · exact dvd_mul_of_dvd_right hqx (3 * u)
    · exact dvd_mul_of_dvd_right hxsq 3
  have htotal : q ∣ u ^ 2 + (3 * u * x + 3 * x ^ 2) := by
    simpa only [← Nat.add_assoc] using hqGN
  have hu2 : q ∣ u ^ 2 :=
    (Nat.dvd_add_iff_left (k := q) (m := u ^ 2)
      (n := 3 * u * x + 3 * x ^ 2) hrest).mpr htotal
  exact hq_u (hq.dvd_of_dvd_pow hu2)

private theorem prime_not_dvd_sum_coordinate_of_dvd_GN_three
    {q u x : ℕ}
    (hq : Nat.Prime q)
    (hq_x : ¬ q ∣ x)
    (hqGN : q ∣ DkMath.CosmicFormulaBinom.GN 3 u x) :
    ¬ q ∣ x + u := by
  intro hqsum
  rw [GN_three_eq_discriminant_neg_three_form] at hqGN
  have hsum2 : q ∣ (x + u) ^ 2 := dvd_pow hqsum (by norm_num)
  have hsumx : q ∣ (x + u) * x := dvd_mul_of_dvd_left hqsum x
  have hfirst : q ∣ (x + u) ^ 2 + (x + u) * x := Nat.dvd_add hsum2 hsumx
  have hx2 : q ∣ x ^ 2 :=
    (Nat.dvd_add_iff_right (k := q)
      (m := (x + u) ^ 2 + (x + u) * x) (n := x ^ 2) hfirst).mpr hqGN
  exact hq_x (hq.dvd_of_dvd_pow hx2)

/-- A non-ramified prime divisor of the primitive cubic shell is `1 mod 3`. -/
theorem three_dvd_prime_sub_one_of_prime_dvd_GN_three_of_coprime_of_ne_three
    {q u x : ℕ}
    (hq : Nat.Prime q)
    (hcop : Nat.Coprime u x)
    (hqGN : q ∣ DkMath.CosmicFormulaBinom.GN 3 u x)
    (hq3 : q ≠ 3) :
    3 ∣ q - 1 := by
  have hq_u : ¬ q ∣ u :=
    prime_not_dvd_boundary_of_dvd_GN_three_of_coprime_of_ne_three
      hq hcop hqGN hq3
  have hq_x : ¬ q ∣ x :=
    prime_not_dvd_second_coordinate_of_dvd_GN_three hq hq_u hqGN
  have hq_sum : ¬ q ∣ x + u :=
    prime_not_dvd_sum_coordinate_of_dvd_GN_three hq hq_x hqGN
  letI : Fact q.Prime := ⟨hq⟩
  have haZ : ((x + u : ℕ) : ZMod q) ≠ 0 := by
    intro hzero
    exact hq_sum ((ZMod.natCast_eq_zero_iff (x + u) q).mp hzero)
  have hbZ : ((x : ℕ) : ZMod q) ≠ 0 := by
    intro hzero
    exact hq_x ((ZMod.natCast_eq_zero_iff x q).mp hzero)
  let ua := Units.mk0 ((x + u : ℕ) : ZMod q)
    haZ
  let ub := Units.mk0 (x : ZMod q)
    hbZ
  let r : (ZMod q)ˣ := ua * ub⁻¹
  have hprod : q ∣ u * DkMath.CosmicFormulaBinom.GN 3 u x :=
    dvd_mul_of_dvd_right hqGN u
  have hprod_zero :
      ((u * DkMath.CosmicFormulaBinom.GN 3 u x : ℕ) : ZMod q) = 0 :=
    (ZMod.natCast_eq_zero_iff _ q).2 hprod
  have hcosmic :
      (u + x) ^ 3 =
        u * DkMath.CosmicFormulaBinom.GN 3 u x + x ^ 3 := by
    simpa [Nat.add_comm] using
      (DkMath.CosmicFormulaBinom.cosmic_id_csr' (R := ℕ) 3 u x)
  have hpow_eq :
      (ua ^ 3 : ZMod q) = (ub ^ 3 : ZMod q) := by
    have hcast := congrArg (fun n : ℕ => (n : ZMod q)) hcosmic
    have hcast' :
        ((u + x : ℕ) : ZMod q) ^ 3 =
          ((u * DkMath.CosmicFormulaBinom.GN 3 u x + x ^ 3 : ℕ) : ZMod q) := by
      simpa only [Nat.cast_pow] using hcast
    have hbase :
        ((x + u : ℕ) : ZMod q) ^ 3 = (x : ZMod q) ^ 3 := by
      calc
        ((x + u : ℕ) : ZMod q) ^ 3 = ((u + x : ℕ) : ZMod q) ^ 3 := by
          rw [Nat.add_comm]
        _ = ((u * DkMath.CosmicFormulaBinom.GN 3 u x + x ^ 3 : ℕ) : ZMod q) := by
          exact hcast'
        _ = (x : ZMod q) ^ 3 := by
          rw [Nat.cast_add, Nat.cast_pow, hprod_zero, zero_add]
    simpa [ua, ub] using hbase
  have hpow_units : ua ^ 3 = ub ^ 3 := Units.ext_iff.mpr hpow_eq
  have hrpow : r ^ 3 = 1 := by
    simp [r, mul_pow, hpow_units]
  have hrne : r ≠ 1 := by
    intro hr
    have hcoe :
        ((x + u : ℕ) : ZMod q) * (x : ZMod q)⁻¹ = 1 := by
      have h := congrArg (fun z : (ZMod q)ˣ => (z : ZMod q)) hr
      simpa [r, ua, ub] using h
    have hsum_eq :
        ((x + u : ℕ) : ZMod q) = (x : ZMod q) := by
      calc
        ((x + u : ℕ) : ZMod q) =
            ((x + u : ℕ) : ZMod q) * (x : ZMod q)⁻¹ * (x : ZMod q) := by
              simp [hbZ]
        _ = 1 * (x : ZMod q) := by rw [hcoe]
        _ = (x : ZMod q) := by simp
    have hu_zero : (u : ZMod q) = 0 := by
      have hsum_eq' :
          (u : ZMod q) + (x : ZMod q) = (x : ZMod q) := by
        simpa [Nat.cast_add, Nat.add_comm] using hsum_eq
      have hsum_eq'' :
          (u : ZMod q) + (x : ZMod q) = 0 + (x : ZMod q) := by
        simpa using hsum_eq'
      exact add_right_cancel hsum_eq''
    exact hq_u ((ZMod.natCast_eq_zero_iff u q).1 hu_zero)
  have horder : orderOf r = 3 := orderOf_eq_prime hrpow hrne
  have hcard : orderOf r ∣ Nat.card ((ZMod q)ˣ) := orderOf_dvd_natCard r
  have hcard' : orderOf r ∣ q - 1 := by
    simpa [Nat.card_units, Nat.card_eq_fintype_card, ZMod.card,
      Nat.totient_prime hq] using hcard
  simpa [horder] using hcard'

/- A prime divisor in the non-ramified sector does not divide the cubic
boundary derivative.  This is the finite discriminant-side exclusion used by
the shell package; it is not a Hensel lifting theorem. -/
theorem prime_not_dvd_cubic_boundary_derivative
    {q u x : ℕ}
    (hq : Nat.Prime q)
    (hcop : Nat.Coprime u x)
    (hqGN : q ∣ DkMath.CosmicFormulaBinom.GN 3 u x)
    (hq3 : q ≠ 3) :
    ¬ q ∣ 2 * u + 3 * x := by
  have hq_u : ¬ q ∣ u :=
    prime_not_dvd_boundary_of_dvd_GN_three_of_coprime_of_ne_three
      hq hcop hqGN hq3
  have hq_x : ¬ q ∣ x :=
    prime_not_dvd_second_coordinate_of_dvd_GN_three hq hq_u hqGN
  intro hder
  have hleft : q ∣ 4 * DkMath.CosmicFormulaBinom.GN 3 u x :=
    dvd_mul_of_dvd_right hqGN 4
  have hidentity :
      4 * DkMath.CosmicFormulaBinom.GN 3 u x =
        (2 * u + 3 * x) ^ 2 + 3 * x ^ 2 := by
    rw [GN_three_dual_explicit]
    ring
  have htotal : q ∣ (2 * u + 3 * x) ^ 2 + 3 * x ^ 2 := by
    rw [← hidentity]
    exact hleft
  have hder2 : q ∣ (2 * u + 3 * x) ^ 2 :=
    dvd_pow hder (by norm_num)
  have hsecond : q ∣ 3 * x ^ 2 :=
    (Nat.dvd_add_iff_right (k := q)
      (m := (2 * u + 3 * x) ^ 2) (n := 3 * x ^ 2) hder2).mpr htotal
  rcases (hq.dvd_mul.mp hsecond) with hq3' | hx2
  · apply hq3
    exact ((Nat.dvd_prime Nat.prime_three).mp hq3').resolve_left hq.ne_one
  · exact hq_x (hq.dvd_of_dvd_pow hx2)

/-- A square-lift prime divisor is necessarily in the non-ramified sector. -/
theorem three_dvd_prime_sub_one_of_square_lift_GN_three
    {q u x : ℕ}
    (hq : Nat.Prime q)
    (hcop : Nat.Coprime u x)
    (hq2 : q ^ 2 ∣ DkMath.CosmicFormulaBinom.GN 3 u x) :
    3 ∣ q - 1 := by
  have hqGN : q ∣ DkMath.CosmicFormulaBinom.GN 3 u x := by
    have hq_sq : q ∣ q ^ 2 := by
      exact ⟨q, by simp [pow_two]⟩
    exact dvd_trans hq_sq hq2
  have hq3 : q ≠ 3 := by
    intro hqeq
    apply not_nine_dvd_GN_three_of_coprime hcop
    simpa [hqeq] using hq2
  exact three_dvd_prime_sub_one_of_prime_dvd_GN_three_of_coprime_of_ne_three
    hq hcop hqGN hq3

/-- Positive prime targets at degree three have primitive coordinates. -/
theorem GNPositiveRepresentation.coprime_coordinates_of_degree_three_target_prime
    {p u x : ℕ}
    (hrep : GNPositiveRepresentation p 3 u x)
    (hp : Nat.Prime p) :
    Nat.Coprime u x := by
  have hbounds := GNPositiveRepresentation.bounds hrep
  rcases hbounds with ⟨_, _, _, _, hup, _⟩
  rcases hrep with ⟨_, hu, hx, hvalue⟩
  apply (Nat.coprime_iff_gcd_eq_one).2
  by_contra hg
  let g := Nat.gcd u x
  have hgu : g ∣ u := Nat.gcd_dvd_left u x
  have hgx : g ∣ x := Nat.gcd_dvd_right u x
  have h1 : g ∣ u ^ 2 := dvd_pow hgu (by norm_num)
  have h2 : g ∣ 3 * u * x := by
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hgu 3) x
  have h3 : g ∣ 3 * x ^ 2 :=
    dvd_mul_of_dvd_right (dvd_pow hgx (by norm_num)) 3
  have hgGN : g ∣ DkMath.CosmicFormulaBinom.GN 3 u x := by
    rw [GN_three_dual_explicit]
    exact Nat.dvd_add (Nat.dvd_add h1 h2) h3
  have hgp : g ∣ p := by
    rw [← hvalue]
    exact hgGN
  rcases (Nat.dvd_prime hp).mp hgp with hg1 | hgp_eq
  · exact hg hg1
  · have hgle : g ≤ u := Nat.le_of_dvd hu hgu
    rw [hgp_eq] at hgle
    omega

/-! ### Degree-three prime shell package -/

/-- All primitive, ramified, residue, and centered-shell filters at degree three. -/
theorem GNPositiveRepresentation.degree_three_prime_shell_constraints
    {p u x : ℕ}
    (hrep : GNPositiveRepresentation p 3 u x)
    (hp : Nat.Prime p) :
    Nat.Coprime u x ∧
      ¬ 3 ∣ u ∧
      3 ∣ p - 1 ∧
      4 * p = u ^ 2 + 3 * (2 * x + u) ^ 2 := by
  have hcop :=
    GNPositiveRepresentation.coprime_coordinates_of_degree_three_target_prime
      hrep hp
  have hvalue : DkMath.CosmicFormulaBinom.GN 3 u x = p := hrep.2.2.2
  have hnot3 : ¬ 3 ∣ u := by
    intro h3u
    have h3GN : 3 ∣ DkMath.CosmicFormulaBinom.GN 3 u x :=
      (three_dvd_GN_three_iff_dvd_boundary (u := u) (x := x)).mpr h3u
    have h3p : 3 ∣ p := by
      rw [← hvalue]
      exact h3GN
    have h3eqp : 3 = p :=
      (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp h3p
    have hdp : 3 < p := (GNPositiveRepresentation.bounds hrep).2.2.2.1
    omega
  have hdvd : 3 ∣ p - 1 :=
    GNPositiveRepresentation.degree_dvd_target_sub_one_of_target_prime hrep hp
  have hsquare : 4 * p = u ^ 2 + 3 * (2 * x + u) ^ 2 := by
    exact (GN_three_eq_target_iff_centered_square (p := p) (u := u) (x := x)).mp
      hvalue
  exact ⟨hcop, hnot3, hdvd, hsquare⟩

/-! ### Explicit square-lift counterexample -/

example : DkMath.CosmicFormulaBinom.GN 3 17 1 = 343 := by
  rw [GN_three_dual_explicit]
  norm_num

example : DkMath.CosmicFormulaBinom.GN 3 17 1 = 7 ^ 3 := by
  rw [GN_three_dual_explicit]
  norm_num

example : 7 ^ 2 ∣ DkMath.CosmicFormulaBinom.GN 3 17 1 := by
  rw [GN_three_dual_explicit]
  norm_num

end DkMath.NumberTheory
