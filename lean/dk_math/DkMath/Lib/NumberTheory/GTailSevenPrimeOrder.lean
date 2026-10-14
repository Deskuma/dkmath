/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.Cosmic.GTailNat
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

#print "file: DkMath.Lib.NumberTheory.GTailSevenPrimeOrder"

/-!
# Neutral finite-field prime orders

The seventh order needs a nonzero gap residue; the third order excludes
characteristic three. Their intersection is restricted to the tail branch.
No Fermat equation or typed number-field carrier is imported.
-/

namespace DkMath.Lib.NumberTheory

open DkMath.CosmicFormula

private theorem prime_order_dvd_field_units {q p : ℕ} (hq : Nat.Prime q)
    (hp : Nat.Prime p) (r : ZMod q) (hr0 : r ≠ 0) (hrpow : r ^ p = 1)
    (hr1 : r ≠ 1) : p ∣ q - 1 := by
  let : Fact (Nat.Prime q) := ⟨hq⟩
  let : Fact (Nat.Prime p) := ⟨hp⟩
  let u : (ZMod q)ˣ := Units.mk0 r hr0
  have hupow : u ^ p = 1 := by
    apply Units.ext
    change r ^ p = 1
    exact hrpow
  have hu1 : u ≠ 1 := by
    intro hu
    exact hr1 (congrArg (fun v : (ZMod q)ˣ => (v : ZMod q)) hu)
  have horder : orderOf u = p := orderOf_eq_prime hupow hu1
  rw [← horder]
  exact ZMod.orderOf_units_dvd_card_sub_one u

/-- A nontrivial seven-root from the actual normalized tail forces order seven. -/
theorem seven_dvd_prime_sub_one_of_gtail {q c g : ℕ}
    (hq : Nat.Prime q) (_hq7 : q ≠ 7) (hc : ¬ q ∣ c) (hg : ¬ q ∣ g)
    (hT : q ∣ GTail 7 1 g c) : 7 ∣ q - 1 := by
  let : Fact (Nat.Prime q) := ⟨hq⟩
  have hc0 : (c : ZMod q) ≠ 0 := fun hz => hc ((ZMod.natCast_eq_zero_iff c q).mp hz)
  have hg0 : (g : ZMod q) ≠ 0 := fun hz => hg ((ZMod.natCast_eq_zero_iff g q).mp hz)
  have ht0 : ((GTail 7 1 g c : ℕ) : ZMod q) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hT
  have hshell := congrArg (fun n : ℕ => (n : ZMod q))
    (add_pow_eq_mul_GTail_one_add_gap 7 g c)
  push_cast at hshell
  rw [ht0, mul_zero, zero_add] at hshell
  let r : ZMod q := ((c : ZMod q) + g) / c
  have hrpow : r ^ 7 = 1 := by
    dsimp [r]
    rw [div_pow, add_comm, hshell, div_self (pow_ne_zero _ hc0)]
  have hr0 : r ≠ 0 := by
    intro hz
    rw [hz, zero_pow (by decide : 7 ≠ 0)] at hrpow
    exact zero_ne_one hrpow
  have hr1 : r ≠ 1 := by
    intro hone
    have hsum := (div_eq_one_iff_eq hc0).mp hone
    exact hg0 (add_left_cancel (by simpa only [add_zero] using hsum))
  exact prime_order_dvd_field_units hq (by decide) r hr0 hrpow hr1

/-- The nontrivial seven-root branch cannot lie in characteristic three. -/
theorem prime_ne_three_of_gtail {q c g : ℕ}
    (hq : Nat.Prime q) (hq7 : q ≠ 7) (hc : ¬ q ∣ c) (hg : ¬ q ∣ g)
    (hT : q ∣ GTail 7 1 g c) : q ≠ 3 := by
  have hseven := seven_dvd_prime_sub_one_of_gtail hq hq7 hc hg hT
  intro heq
  rw [heq] at hseven
  norm_num at hseven

/-- A unit quadratic root away from characteristic three has order three. -/
theorem three_dvd_prime_sub_one_of_quadratic {q a b : ℕ}
    (hq : Nat.Prime q) (hq3 : q ≠ 3) (hQ : q ∣ a ^ 2 + a * b + b ^ 2)
    (ha : ¬ q ∣ a) (hb : ¬ q ∣ b) : 3 ∣ q - 1 := by
  let : Fact (Nat.Prime q) := ⟨hq⟩
  have ha0 : (a : ZMod q) ≠ 0 := fun hz => ha ((ZMod.natCast_eq_zero_iff a q).mp hz)
  have hb0 : (b : ZMod q) ≠ 0 := fun hz => hb ((ZMod.natCast_eq_zero_iff b q).mp hz)
  have hquad : (a : ZMod q) ^ 2 + (a : ZMod q) * b + (b : ZMod q) ^ 2 = 0 := by
    have hz := (ZMod.natCast_eq_zero_iff (a ^ 2 + a * b + b ^ 2) q).mpr hQ
    push_cast at hz
    exact hz
  let s : ZMod q := (a : ZMod q) / b
  have hsquad : s ^ 2 + s + 1 = 0 := by
    dsimp [s]
    field_simp [hb0]
    convert hquad using 1 <;> ring
  have hspow : s ^ 3 = 1 := by
    have hfactor : s ^ 3 - 1 = (s - 1) * (s ^ 2 + s + 1) := by ring
    rw [hsquad, mul_zero] at hfactor
    exact sub_eq_zero.mp hfactor
  have hs0 : s ≠ 0 := div_ne_zero ha0 hb0
  have hs1 : s ≠ 1 := by
    intro hone
    rw [hone] at hsquad
    have hthree : (3 : ZMod q) = 0 := by norm_num at hsquad ⊢; exact hsquad
    have hqthree : q ∣ 3 := (ZMod.natCast_eq_zero_iff 3 q).mp hthree
    exact hq3 ((Nat.prime_dvd_prime_iff_eq hq (by decide : Nat.Prime 3)).mp hqthree)
  exact prime_order_dvd_field_units hq (by decide) s hs0 hspow hs1

/-- Independent nontrivial third and seventh roots intersect on the tail branch. -/
theorem twentyOne_dvd_prime_sub_one_of_quadratic_gtail {q a b c g : ℕ}
    (hq : Nat.Prime q) (hq7 : q ≠ 7)
    (hQ : q ∣ a ^ 2 + a * b + b ^ 2) (hT : q ∣ GTail 7 1 g c)
    (ha : ¬ q ∣ a) (hb : ¬ q ∣ b) (hc : ¬ q ∣ c) (hg : ¬ q ∣ g) :
    21 ∣ q - 1 := by
  have hseven := seven_dvd_prime_sub_one_of_gtail hq hq7 hc hg hT
  have hthree := three_dvd_prime_sub_one_of_quadratic hq
    (prime_ne_three_of_gtail hq hq7 hc hg hT) hQ ha hb
  simpa using (show Nat.Coprime 3 7 from by decide).mul_dvd_of_dvd_of_dvd hthree hseven

end DkMath.Lib.NumberTheory
