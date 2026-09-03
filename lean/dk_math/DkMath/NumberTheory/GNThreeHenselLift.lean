/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.Data.Fin.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Basic
import DkMath.NumberTheory.GNThreePrimeArithmetic

#print "file: DkMath.NumberTheory.GNThreeHenselLift"

namespace DkMath.NumberTheory

open DkMath.CosmicFormulaBinom

/-!
## One-step simple-root lifting for the degree-three GN shell

This module implements the elementary `q` to `q^2` lift for
`GN 3 u x = u^2 + 3*u*x + 3*x^2`.  The exact quadratic shift identity reduces
the lift to one linear congruence modulo `q`; GNPC-006 supplies the required
nonzero derivative in the primitive non-ramified sector.

No completion, infinite `q`-adic sequence, valuation classification, or FLT
endpoint is introduced here.
-/

/-! ### Exact shift identities -/

/-- The exact quadratic Taylor identity for the cubic GN shell. -/
theorem GN_three_add_boundary_shift
    (u x m : ℕ) :
    DkMath.CosmicFormulaBinom.GN 3 (u + m) x =
      DkMath.CosmicFormulaBinom.GN 3 u x +
        m * (2 * u + 3 * x) + m ^ 2 := by
  rw [GN_three_dual_explicit, GN_three_dual_explicit]
  ring

/-- The exact shift identity with a prime-sized step. -/
theorem GN_three_add_prime_mul_digit
    (q u x t : ℕ) :
    DkMath.CosmicFormulaBinom.GN 3 (u + q * t) x =
      DkMath.CosmicFormulaBinom.GN 3 u x +
        q * t * (2 * u + 3 * x) + q ^ 2 * t ^ 2 := by
  rw [GN_three_add_boundary_shift]
  ring

/-! ### Linearized divisibility criterion -/

private theorem sq_dvd_GN_three_add_prime_mul_digit_iff
    {q u x t : ℕ}
    (hqpos : 0 < q)
    (hqGN : q ∣ DkMath.CosmicFormulaBinom.GN 3 u x) :
    q ^ 2 ∣ DkMath.CosmicFormulaBinom.GN 3 (u + q * t) x ↔
      q ∣ DkMath.CosmicFormulaBinom.GN 3 u x / q +
        t * (2 * u + 3 * x) := by
  rw [GN_three_add_prime_mul_digit]
  have hmul :
      q * (DkMath.CosmicFormulaBinom.GN 3 u x / q) =
        DkMath.CosmicFormulaBinom.GN 3 u x :=
    Nat.mul_div_cancel' hqGN
  have hshift :
      DkMath.CosmicFormulaBinom.GN 3 u x +
          q * t * (2 * u + 3 * x) + q ^ 2 * t ^ 2 =
        q * (DkMath.CosmicFormulaBinom.GN 3 u x / q +
          t * (2 * u + 3 * x) + q * t ^ 2) := by
    calc
      DkMath.CosmicFormulaBinom.GN 3 u x +
            q * t * (2 * u + 3 * x) + q ^ 2 * t ^ 2 =
          q * (DkMath.CosmicFormulaBinom.GN 3 u x / q) +
            q * t * (2 * u + 3 * x) + q ^ 2 * t ^ 2 := by
              rw [hmul]
      _ = q * (DkMath.CosmicFormulaBinom.GN 3 u x / q +
            t * (2 * u + 3 * x) + q * t ^ 2) := by ring
  constructor
  · intro h
    have h' : q ^ 2 ∣ q *
        (DkMath.CosmicFormulaBinom.GN 3 u x / q +
          t * (2 * u + 3 * x) + q * t ^ 2) := by
      rw [← hshift]
      exact h
    have hE : q ∣
        DkMath.CosmicFormulaBinom.GN 3 u x / q +
          t * (2 * u + 3 * x) + q * t ^ 2 := by
      exact Nat.dvd_of_mul_dvd_mul_left (k := q) (m := q)
        (n := DkMath.CosmicFormulaBinom.GN 3 u x / q +
          t * (2 * u + 3 * x) + q * t ^ 2) hqpos (by
            simpa only [pow_two] using h')
    have htail : q ∣ q * t ^ 2 := dvd_mul_right q (t ^ 2)
    exact (Nat.dvd_add_iff_left htail).mpr hE
  · intro hlin
    have htail : q ∣ q * t ^ 2 := dvd_mul_right q (t ^ 2)
    have hE : q ∣
        DkMath.CosmicFormulaBinom.GN 3 u x / q +
          t * (2 * u + 3 * x) + q * t ^ 2 :=
      (Nat.dvd_add_iff_left htail).mp hlin
    have h' : q ^ 2 ∣ q *
        (DkMath.CosmicFormulaBinom.GN 3 u x / q +
          t * (2 * u + 3 * x) + q * t ^ 2) := by
      simpa only [pow_two] using Nat.mul_dvd_mul_left q hE
    rw [hshift]
    exact h'

/-! ### The unique one-digit lift -/

/-- Every primitive non-ramified cubic root has a unique next base-`q` digit. -/
theorem existsUnique_GN_three_sqLift_digit
    {q u x : ℕ}
    (hq : Nat.Prime q)
    (hcop : Nat.Coprime u x)
    (hqGN : q ∣ DkMath.CosmicFormulaBinom.GN 3 u x)
    (hq3 : q ≠ 3) :
    ∃! t : Fin q,
      q ^ 2 ∣
        DkMath.CosmicFormulaBinom.GN 3
          (u + q * (t : ℕ)) x := by
  letI : Fact q.Prime := ⟨hq⟩
  have hqder : ¬ q ∣ 2 * u + 3 * x :=
    prime_not_dvd_cubic_boundary_derivative hq hcop hqGN hq3
  have hderZ : ((2 * u + 3 * x : ℕ) : ZMod q) ≠ 0 := by
    intro hzero
    exact hqder ((ZMod.natCast_eq_zero_iff (2 * u + 3 * x) q).mp hzero)
  let c : ZMod q :=
    (DkMath.CosmicFormulaBinom.GN 3 u x / q : ℕ)
  let d : ZMod q := (2 * u + 3 * x : ℕ)
  have hd : d ≠ 0 := by
    intro hd0
    apply hderZ
    simpa [d, Nat.cast_add, Nat.cast_mul] using hd0
  let z : ZMod q := -c * d⁻¹
  let t : Fin q := ⟨z.val, ZMod.val_lt z⟩
  have htZ : ((t : ℕ) : ZMod q) = z := by
    exact ZMod.natCast_zmod_val z
  have hlinZ : c + ((t : ℕ) : ZMod q) * d = 0 := by
    rw [htZ]
    simp [z, hd]
  have hlin : q ∣
      DkMath.CosmicFormulaBinom.GN 3 u x / q +
        (t : ℕ) * (2 * u + 3 * x) := by
    apply (ZMod.natCast_eq_zero_iff _ q).mp
    simpa [c, d, Nat.cast_add, Nat.cast_mul] using hlinZ
  have ht_lift : q ^ 2 ∣
      DkMath.CosmicFormulaBinom.GN 3 (u + q * (t : ℕ)) x := by
    exact (sq_dvd_GN_three_add_prime_mul_digit_iff hq.pos hqGN).mpr hlin
  refine ⟨t, ht_lift, ?_⟩
  intro s hs
  have hslin : q ∣
      DkMath.CosmicFormulaBinom.GN 3 u x / q +
        (s : ℕ) * (2 * u + 3 * x) :=
    (sq_dvd_GN_three_add_prime_mul_digit_iff hq.pos hqGN).mp hs
  have hsZ : c + ((s : ℕ) : ZMod q) * d = 0 := by
    simpa [c, d, Nat.cast_add, Nat.cast_mul] using
      ((ZMod.natCast_eq_zero_iff _ q).2 hslin)
  have hstZ : ((s : ℕ) : ZMod q) * d = ((t : ℕ) : ZMod q) * d := by
    linear_combination hsZ - hlinZ
  have hstZ' : ((s : ℕ) : ZMod q) = ((t : ℕ) : ZMod q) :=
    mul_right_cancel₀ hderZ hstZ
  apply Fin.ext
  have hval := congrArg ZMod.val hstZ'
  simpa [ZMod.val_natCast, Nat.mod_eq_of_lt s.isLt,
    Nat.mod_eq_of_lt t.isLt] using hval

/-! ### Optional closed digit formula -/

/-- The Newton/Hensel correction digit as an element of `ZMod q`. -/
def GNThreeNextLiftDigitZMod
    (q u x : ℕ) [Fact q.Prime] : ZMod q :=
  -((DkMath.CosmicFormulaBinom.GN 3 u x / q : ℕ) : ZMod q) *
    ((2 * u + 3 * x : ℕ) : ZMod q)⁻¹

/-- The unique finite digit is the displayed modular Newton correction. -/
theorem GNThreeNextLiftDigitZMod_eq_cast_of_sqLift
    {q u x : ℕ} [Fact q.Prime]
    (hq : Nat.Prime q)
    (hcop : Nat.Coprime u x)
    (hqGN : q ∣ DkMath.CosmicFormulaBinom.GN 3 u x)
    (hq3 : q ≠ 3)
    (t : Fin q)
    (ht : q ^ 2 ∣
      DkMath.CosmicFormulaBinom.GN 3 (u + q * (t : ℕ)) x) :
    GNThreeNextLiftDigitZMod q u x = (t : ZMod q) := by
  have hqder : ¬ q ∣ 2 * u + 3 * x :=
    prime_not_dvd_cubic_boundary_derivative hq hcop hqGN hq3
  have hderZ : ((2 * u + 3 * x : ℕ) : ZMod q) ≠ 0 := by
    intro hzero
    exact hqder ((ZMod.natCast_eq_zero_iff (2 * u + 3 * x) q).mp hzero)
  have hlin : q ∣
      DkMath.CosmicFormulaBinom.GN 3 u x / q +
        (t : ℕ) * (2 * u + 3 * x) :=
    (sq_dvd_GN_three_add_prime_mul_digit_iff hq.pos hqGN).mp ht
  have hlinZ :
      ((DkMath.CosmicFormulaBinom.GN 3 u x / q +
        (t : ℕ) * (2 * u + 3 * x) : ℕ) : ZMod q) = 0 :=
    (ZMod.natCast_eq_zero_iff _ q).2 hlin
  have hlinZ' :
      ((DkMath.CosmicFormulaBinom.GN 3 u x / q : ℕ) : ZMod q) +
        ((t : ℕ) : ZMod q) * ((2 * u + 3 * x : ℕ) : ZMod q) = 0 := by
    simpa [Nat.cast_add, Nat.cast_mul] using hlinZ
  have hsolve :
      ((t : ℕ) : ZMod q) * ((2 * u + 3 * x : ℕ) : ZMod q) =
        -((DkMath.CosmicFormulaBinom.GN 3 u x / q : ℕ) : ZMod q) := by
    linear_combination hlinZ'
  have hderZ' : (2 * (u : ZMod q) + 3 * (x : ZMod q)) ≠ 0 := by
    simpa [Nat.cast_add, Nat.cast_mul] using hderZ
  dsimp [GNThreeNextLiftDigitZMod]
  calc
    -((DkMath.CosmicFormulaBinom.GN 3 u x / q : ℕ) : ZMod q) *
          ((2 * u + 3 * x : ℕ) : ZMod q)⁻¹ =
        (((t : ℕ) : ZMod q) * ((2 * u + 3 * x : ℕ) : ZMod q)) *
          ((2 * u + 3 * x : ℕ) : ZMod q)⁻¹ := by rw [hsolve]
    _ = (t : ZMod q) := by simp [hderZ']

/-! ### Stability and concrete regressions -/

/-- The simple-root derivative remains nonzero after one prime-sized shift. -/
theorem prime_not_dvd_cubic_boundary_derivative_add_prime_mul
    {q u x t : ℕ}
    (hqder : ¬ q ∣ 2 * u + 3 * x) :
    ¬ q ∣ 2 * (u + q * t) + 3 * x := by
  intro hshift
  have hidentity :
      2 * (u + q * t) + 3 * x =
        (2 * u + 3 * x) + 2 * (q * t) := by
    ring
  rw [hidentity] at hshift
  have htail : q ∣ 2 * (q * t) := by
    exact dvd_mul_of_dvd_right (dvd_mul_right q t) 2
  exact hqder ((Nat.dvd_add_iff_left htail).mpr hshift)

example : 7 ∣ DkMath.CosmicFormulaBinom.GN 3 1 1 := by
  rw [GN_three_dual_explicit]
  norm_num

example : 7 ^ 2 ∣ DkMath.CosmicFormulaBinom.GN 3 29 1 := by
  rw [GN_three_dual_explicit]
  norm_num

example : 7 ∣ DkMath.CosmicFormulaBinom.GN 3 3 1 := by
  rw [GN_three_dual_explicit]
  norm_num

example : 7 ^ 2 ∣ DkMath.CosmicFormulaBinom.GN 3 17 1 := by
  rw [GN_three_dual_explicit]
  norm_num

example {t : Fin 7}
    (ht : 7 ^ 2 ∣ DkMath.CosmicFormulaBinom.GN 3 (1 + 7 * (t : ℕ)) 1) :
    t = 4 := by
  have hqGN : 7 ∣ DkMath.CosmicFormulaBinom.GN 3 1 1 := by
    rw [GN_three_dual_explicit]
    norm_num
  have hu := existsUnique_GN_three_sqLift_digit
    (q := 7) (u := 1) (x := 1) (by norm_num) (by norm_num) hqGN (by norm_num)
  exact hu.unique ht (by
    change 49 ∣ DkMath.CosmicFormulaBinom.GN 3 29 1
    rw [GN_three_dual_explicit]
    norm_num)

example {t : Fin 7}
    (ht : 7 ^ 2 ∣ DkMath.CosmicFormulaBinom.GN 3 (3 + 7 * (t : ℕ)) 1) :
    t = 2 := by
  have hqGN : 7 ∣ DkMath.CosmicFormulaBinom.GN 3 3 1 := by
    rw [GN_three_dual_explicit]
    norm_num
  have hu := existsUnique_GN_three_sqLift_digit
    (q := 7) (u := 3) (x := 1) (by norm_num) (by norm_num) hqGN (by norm_num)
  exact hu.unique ht (by
    change 49 ∣ DkMath.CosmicFormulaBinom.GN 3 17 1
    rw [GN_three_dual_explicit]
    norm_num)

example : DkMath.CosmicFormulaBinom.GN 3 17 1 = 7 ^ 3 := by
  rw [GN_three_dual_explicit]
  norm_num

end DkMath.NumberTheory
