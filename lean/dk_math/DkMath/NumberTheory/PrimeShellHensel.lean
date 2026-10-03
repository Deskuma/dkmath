/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.PolynomialHenselDigit
import DkMath.Lib.Cosmic.GNProductDegree
import Mathlib.FieldTheory.Finite.Basic

/-!
# Prime-shell finite Hensel lifting

The polynomial is the existing GN tail in the gap variable, with an explicitly
fixed integer base. Away from the prime degree, a base unit modulo q makes
shell roots simple and yields unique next digits at every positive depth.
Repeated lifting supplies finite roots and exact divisibility depths. The
ramified root sector is stated separately; no infinite branch is constructed.
-/

namespace DkMath.NumberTheory

open Polynomial DkMath.CosmicFormula DkMath.Lib.NumberTheory

/-- The existing GN tail as an integer polynomial in the gap, with fixed base. -/
noncomputable def primeShellPolynomial (p : ℕ) (u : ℤ) : ℤ[X] := GTail p 1 X (C u)

theorem primeShellPolynomial_eval (p : ℕ) (u g : ℤ) :
    (primeShellPolynomial p u).eval g = GTail p 1 g u := by
  simpa only [primeShellPolynomial, coe_evalRingHom, eval_X, eval_C] using
    map_GN (evalRingHom g) p X (C u)

theorem primeShellPolynomial_map_eval (p q : ℕ) (u g : ℤ) :
    ((primeShellPolynomial p u).map (Int.castRingHom (ZMod q))).eval (g : ZMod q) =
      GTail p 1 (g : ZMod q) (u : ZMod q) := by
  rw [eval_map]
  simpa only [primeShellPolynomial, coe_eval₂RingHom, eval₂_X, eval₂_C,
    Int.coe_castRingHom] using
    map_GN (eval₂RingHom (Int.castRingHom (ZMod q)) (g : ZMod q)) p X (C u)

/-- The derivative relation behind simplicity of every prime shell. -/
theorem primeShellPolynomial_derivative_identity (p : ℕ) (u : ℤ) :
    primeShellPolynomial p u + X * (primeShellPolynomial p u).derivative =
      C (p : ℤ) * (X + C u) ^ (p - 1) := by
  have h := congrArg derivative (add_pow_eq_mul_GTail_one_add_gap p (X : ℤ[X]) (C u))
  simpa only [derivative_pow, derivative_add, derivative_X, derivative_C,
    add_zero, derivative_mul, one_mul, mul_zero, zero_add, mul_one,
    primeShellPolynomial, add_comm] using h.symm

/-- With invertible base and nonzero degree scalar, GN roots are exactly
nontrivial roots of unity in the normalized endpoint ratio. -/
theorem primeShell_root_iff {K : Type*} [Field K] (p : ℕ) (g u : K)
    (hp : (p : K) ≠ 0) (hu : u ≠ 0) :
    GTail p 1 g u = 0 ↔ ((g + u) / u) ^ p = 1 ∧ (g + u) / u ≠ 1 := by
  have hgn : GTail p 1 g u = 0 → g ≠ 0 := by
    intro h hg
    rw [hg, GN_zero_eval, Nat.choose_one_right] at h
    exact (mul_ne_zero hp (pow_ne_zero _ hu)) h
  have hratio : (g + u) / u = 1 ↔ g = 0 := by
    rw [div_eq_one_iff_eq hu]
    exact add_eq_right
  constructor
  · intro h
    refine ⟨?_, fun hr => hgn h (hratio.mp hr)⟩
    rw [div_pow, div_eq_one_iff_eq (pow_ne_zero _ hu),
      add_pow_eq_mul_GTail_one_add_gap, h, mul_zero, zero_add]
  · rintro ⟨hr, hn⟩
    have hg : g ≠ 0 := fun h => hn (hratio.mpr h)
    rw [div_pow, div_eq_one_iff_eq (pow_ne_zero _ hu)] at hr
    rw [add_pow_eq_mul_GTail_one_add_gap] at hr
    have hzero : g * GTail p 1 g u = 0 := add_eq_right.mp hr
    exact (mul_eq_zero.mp hzero).resolve_left hg

/-- Integer shell divisibility is equivalent to a nontrivial normalized p-th root of unity. -/
theorem primeShell_dvd_iff_rootOfUnity {p q : ℕ} [Fact q.Prime]
    (hp : p.Prime) (hqp : q ≠ p) (u g : ℤ) (hu : ¬ (q : ℤ) ∣ u) :
    (q : ℤ) ∣ GTail p 1 g u ↔
      (((g : ZMod q) + (u : ZMod q)) / (u : ZMod q)) ^ p = 1 ∧
        ((g : ZMod q) + (u : ZMod q)) / (u : ZMod q) ≠ 1 := by
  have hp0 : (p : ZMod q) ≠ 0 := by
    intro h
    have hd := (ZMod.natCast_eq_zero_iff p q).mp h
    exact hqp ((Nat.dvd_prime hp).mp hd |>.resolve_left (Fact.out : q.Prime).ne_one)
  have hu0 : (u : ZMod q) ≠ 0 := fun h => hu ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h)
  have he : ((GTail p 1 g u : ℤ) : ZMod q) =
      GTail p 1 (g : ZMod q) (u : ZMod q) := by
    exact map_GN (Int.castRingHom (ZMod q)) p g u
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, he, primeShell_root_iff p _ _ hp0 hu0]

/-- A root away from the prime degree has nonzero gap derivative modulo q. -/
theorem primeShell_derivative_not_dvd {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hqp : q ≠ p) (u g : ℤ) (hu : ¬ (q : ℤ) ∣ u)
    (hr : (q : ℤ) ∣ GTail p 1 g u) :
    ¬ (q : ℤ) ∣ (primeShellPolynomial p u).derivative.eval g := by
  let : Fact q.Prime := ⟨hq⟩
  have hp0 : (p : ZMod q) ≠ 0 := by
    intro h
    have hd := (ZMod.natCast_eq_zero_iff p q).mp h
    exact hqp ((Nat.dvd_prime hp).mp hd |>.resolve_left hq.ne_one)
  have hu0 : (u : ZMod q) ≠ 0 := fun h => hu ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h)
  have hr0 : GTail p 1 (g : ZMod q) (u : ZMod q) = 0 := by
    have h := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hr
    change (Int.castRingHom (ZMod q)) (GTail p 1 g u) = 0 at h
    rw [map_GN (Int.castRingHom (ZMod q))] at h
    exact h
  have hroot := (primeShell_root_iff p (g : ZMod q) (u : ZMod q) hp0 hu0).mp hr0
  have hz : (g : ZMod q) + (u : ZMod q) ≠ 0 := by
    intro h
    have hbad := hroot.1
    rw [h, zero_div, zero_pow hp.ne_zero] at hbad
    exact zero_ne_one hbad
  have hid := congrArg (fun a : ℤ => (a : ZMod q))
    (congrArg (eval g) (primeShellPolynomial_derivative_identity p u))
  simp only [eval_add, eval_mul, eval_X, eval_C, eval_pow, Int.cast_add,
    Int.cast_mul, Int.cast_pow, Int.cast_natCast, primeShellPolynomial_eval] at hid
  have hGN : ((GTail p 1 g u : ℤ) : ZMod q) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hr
  rw [hGN, zero_add] at hid
  intro hd
  rw [(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hd, mul_zero] at hid
  exact (mul_ne_zero hp0 (pow_ne_zero _ hz)) hid.symm

/-- Every nonramified prime-shell root has a unique next digit at arbitrary depth. -/
theorem existsUnique_primeShell_powLift_digit {p q k : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hqp : q ≠ p) (hk : 1 ≤ k)
    (u g : ℤ) (hu : ¬ (q : ℤ) ∣ u) (hr : (q : ℤ) ^ k ∣ GTail p 1 g u) :
    ∃! t : Fin q, (q : ℤ) ^ (k + 1) ∣
      GTail p 1 (g + (q : ℤ) ^ k * t.val) u := by
  have hr1 : (q : ℤ) ∣ GTail p 1 g u :=
    (dvd_pow_self _ (by omega)).trans hr
  simpa only [primeShellPolynomial_eval] using
    existsUnique_polynomial_powLift_digit (primeShellPolynomial p u) g hq hk
      (by rwa [primeShellPolynomial_eval])
      (primeShell_derivative_not_dvd hp hq hqp u g hu hr1)

/-- Every nonramified seed extends to every finite positive depth. -/
theorem exists_primeShell_pow_root {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hqp : q ≠ p)
    (u r : ℤ) (hu : ¬ (q : ℤ) ∣ u) (hr : (q : ℤ) ∣ GTail p 1 r u)
    (k : ℕ) : ∃ g : ℤ, (q : ℤ) ^ (k + 1) ∣ GTail p 1 g u := by
  induction k with
  | zero => exact ⟨r, by simpa only [Nat.zero_add, pow_one] using hr⟩
  | succ k ih =>
    obtain ⟨g, hg⟩ := ih
    obtain ⟨t, ht, _⟩ := existsUnique_primeShell_powLift_digit hp hq hqp
      (by omega : 1 ≤ k + 1) u g hu hg
    exact ⟨g + (q : ℤ) ^ (k + 1) * t.val, ht⟩

/-- Arbitrary exact finite q-adic divisibility depth is available from a seed. -/
theorem exists_primeShell_exact_depth {p q k : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hqp : q ≠ p) (hk : 1 ≤ k)
    (u r : ℤ) (hu : ¬ (q : ℤ) ∣ u) (hr : (q : ℤ) ∣ GTail p 1 r u) :
    ∃ g : ℤ, (q : ℤ) ^ k ∣ GTail p 1 g u ∧
      ¬ (q : ℤ) ^ (k + 1) ∣ GTail p 1 g u := by
  obtain ⟨g, hg⟩ := exists_primeShell_pow_root hp hq hqp u r hu hr k
  have hsmall : (q : ℤ) ^ k ∣ GTail p 1 g u := (pow_dvd_pow _ (by omega)).trans hg
  have hr1 : (q : ℤ) ∣ GTail p 1 g u := (dvd_pow_self _ (by omega)).trans hsmall
  obtain ⟨s, hs, hsn⟩ := exists_polynomial_exact_depth_digit
    (primeShellPolynomial p u) g hq hk (by rwa [primeShellPolynomial_eval])
    (primeShell_derivative_not_dvd hp hq hqp u g hu hr1)
  exact ⟨g + (q : ℤ) ^ k * s.val, by rwa [primeShellPolynomial_eval] at hs,
    by rwa [primeShellPolynomial_eval] at hsn⟩

/-- At the ramified prime, all shell roots have zero gap; the simple-root API
above deliberately does not cover this sector. -/
theorem primeShell_ramified_root_iff {p : ℕ} (hp : p.Prime) (g u : ZMod p) :
    GTail p 1 g u = 0 ↔ g = 0 := by
  let : Fact p.Prime := ⟨hp⟩
  constructor
  · intro h
    have he := add_pow_eq_mul_GTail_one_add_gap p g u
    rw [h, mul_zero, zero_add, ZMod.pow_card, ZMod.pow_card] at he
    exact add_eq_right.mp he
  · intro h
    rw [h, GN_zero_eval, Nat.choose_one_right]
    simp only [ZMod.natCast_self, zero_mul]

end DkMath.NumberTheory
