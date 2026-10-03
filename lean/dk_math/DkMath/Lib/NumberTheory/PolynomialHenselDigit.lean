/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Lean.Elab.Tactic.Omega

/-!
# Finite polynomial Hensel digits

First-order Taylor expansion yields a unique next prime digit for any simple
integer polynomial root, at every positive finite depth. A different digit
realizes exact divisibility depth. No infinite p-adic completion is required.
-/

namespace DkMath.Lib.NumberTheory

open Polynomial

/-- First-order divisibility at every positive depth, for any integer polynomial. -/
theorem polynomial_powLift_iff (P : ℤ[X]) {q k : ℕ} (x t : ℤ)
    (hq : 0 < q) (hk : 1 ≤ k) (hx : (q : ℤ) ^ k ∣ P.eval x) :
    (q : ℤ) ^ (k + 1) ∣ P.eval (x + (q : ℤ) ^ k * t) ↔
      (q : ℤ) ∣ P.eval x / (q : ℤ) ^ k + t * P.derivative.eval x := by
  obtain ⟨c, hc⟩ := exists_mul_sq_add_linear_part_eq_eval_add P x ((q : ℤ) ^ k * t)
  have hm : (q : ℤ) ^ k * (P.eval x / (q : ℤ) ^ k) = P.eval x :=
    Int.mul_ediv_cancel' hx
  have he : P.eval (x + (q : ℤ) ^ k * t) = (q : ℤ) ^ k *
      (P.eval x / (q : ℤ) ^ k + t * P.derivative.eval x + c * (q : ℤ) ^ k * t ^ 2) := by
    rw [← hc]
    calc
      _ = c * ((q : ℤ) ^ k * t) ^ 2 + P.derivative.eval x * ((q : ℤ) ^ k * t) +
          (q : ℤ) ^ k * (P.eval x / (q : ℤ) ^ k) := by rw [hm]
      _ = _ := by ring
  have hm0 : (q : ℤ) ^ k ≠ 0 := pow_ne_zero _ (by exact_mod_cast hq.ne')
  have htail : (q : ℤ) ∣ c * (q : ℤ) ^ k * t ^ 2 :=
    dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (dvd_pow_self _ (by omega)) _) _
  rw [he, pow_succ, mul_dvd_mul_iff_left hm0]
  exact dvd_add_left htail

/-- A simple root has exactly one next digit; this is independent of polynomial degree. -/
theorem existsUnique_polynomial_powLift_digit (P : ℤ[X]) {q k : ℕ} (x : ℤ)
    (hq : q.Prime) (hk : 1 ≤ k) (hx : (q : ℤ) ^ k ∣ P.eval x)
    (hd : ¬ (q : ℤ) ∣ P.derivative.eval x) :
    ∃! t : Fin q, (q : ℤ) ^ (k + 1) ∣ P.eval (x + (q : ℤ) ^ k * t.val) := by
  let : Fact q.Prime := ⟨hq⟩
  let c : ZMod q := (P.eval x / (q : ℤ) ^ k : ℤ)
  let d : ZMod q := (P.derivative.eval x : ℤ)
  have hd0 : d ≠ 0 := fun h => hd ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h)
  let z : ZMod q := -c * d⁻¹
  let t : Fin q := ⟨z.val, ZMod.val_lt z⟩
  have ht : (t.val : ZMod q) = z := ZMod.natCast_zmod_val z
  have hlin : c + (t.val : ZMod q) * d = 0 := by rw [ht]; simp [z, hd0]
  have hlift : (q : ℤ) ^ (k + 1) ∣ P.eval (x + (q : ℤ) ^ k * t.val) := by
    apply (polynomial_powLift_iff P x _ hq.pos hk hx).mpr
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_natCast] using hlin
  refine ⟨t, hlift, ?_⟩
  intro s hs
  have hs' := (polynomial_powLift_iff P x _ hq.pos hk hx).mp hs
  have hsZ : c + (s.val : ZMod q) * d = 0 := by
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_natCast] using
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hs'
  have he : (s.val : ZMod q) * d = (t.val : ZMod q) * d := by
    linear_combination hsZ - hlin
  have he' := mul_right_cancel₀ hd0 he
  apply Fin.ext
  have hv := congrArg ZMod.val he'
  simpa [ZMod.val_natCast, Nat.mod_eq_of_lt s.isLt, Nat.mod_eq_of_lt t.isLt] using hv

/-- Polynomial evaluation preserves a root under a modulus-sized shift. -/
theorem polynomial_shift_preserves_dvd (P : ℤ[X]) (m x t : ℤ)
    (hx : m ∣ P.eval x) : m ∣ P.eval (x + m * t) := by
  have hstep : m ∣ (x + m * t) - x := by
    convert dvd_mul_right m t using 1
    ring
  exact (dvd_sub_left hx).mp (hstep.trans (sub_dvd_eval_sub _ _ P))

/-- Choosing any digit other than the unique lift realizes exact depth. -/
theorem exists_polynomial_exact_depth_digit (P : ℤ[X]) {q k : ℕ} (x : ℤ)
    (hq : q.Prime) (hk : 1 ≤ k) (hx : (q : ℤ) ^ k ∣ P.eval x)
    (hd : ¬ (q : ℤ) ∣ P.derivative.eval x) :
    ∃ s : Fin q, (q : ℤ) ^ k ∣ P.eval (x + (q : ℤ) ^ k * s.val) ∧
      ¬ (q : ℤ) ^ (k + 1) ∣ P.eval (x + (q : ℤ) ^ k * s.val) := by
  obtain ⟨t, ht, huniq⟩ := existsUnique_polynomial_powLift_digit P x hq hk hx hd
  have : Nontrivial (Fin q) := Fin.nontrivial_iff_two_le.mpr hq.two_le
  obtain ⟨s, hs⟩ := exists_ne t
  refine ⟨s, polynomial_shift_preserves_dvd P _ _ _ hx, ?_⟩
  exact fun h => hs (huniq s h)

end DkMath.Lib.NumberTheory
