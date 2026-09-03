/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.Data.Fin.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Basic
import DkMath.NumberTheory.GNThreeHenselLift

#print "file: DkMath.NumberTheory.GNThreeHenselDepth"

namespace DkMath.NumberTheory

open DkMath.CosmicFormulaBinom

/-!
## Finite arbitrary-depth lifting for the degree-three GN shell

This module extends the GNPC-007 simple-root step from `q` to `q^2` to one
finite step from `q^k` to `q^(k+1)`.  The proof remains elementary: the exact
quadratic shift identity is factored over `ℕ`, and the remaining linear
congruence is solved in `ZMod q`.

No infinite `q`-adic branch, completion, valuation classification, or FLT
endpoint is introduced.
-/

/-! ### Power-sized shifts -/

/-- The exact cubic-shell shift by a power-sized digit step. -/
theorem GN_three_add_prime_pow_mul_digit
    (q k u x t : ℕ) :
    DkMath.CosmicFormulaBinom.GN 3 (u + q ^ k * t) x =
      DkMath.CosmicFormulaBinom.GN 3 u x +
        q ^ k * t * (2 * u + 3 * x) +
        q ^ (2 * k) * t ^ 2 := by
  rw [GN_three_add_boundary_shift]
  have hpow : q ^ (2 * k) = (q ^ k) ^ 2 := by
    rw [show 2 * k = k * 2 by omega, pow_mul]
  rw [hpow]
  ring

/-! ### Arbitrary-depth linearization -/

/-- The `q^(k+1)` divisibility test after a power-sized shift. -/
theorem pow_succ_dvd_GN_three_add_prime_pow_mul_digit_iff
    {q k u x t : ℕ}
    (hqpos : 0 < q)
    (hk : 1 ≤ k)
    (hqkGN : q ^ k ∣ DkMath.CosmicFormulaBinom.GN 3 u x) :
    q ^ (k + 1) ∣
        DkMath.CosmicFormulaBinom.GN 3 (u + q ^ k * t) x ↔
      q ∣ DkMath.CosmicFormulaBinom.GN 3 u x / q ^ k +
        t * (2 * u + 3 * x) := by
  rw [GN_three_add_prime_pow_mul_digit]
  have hmul :
      q ^ k * (DkMath.CosmicFormulaBinom.GN 3 u x / q ^ k) =
        DkMath.CosmicFormulaBinom.GN 3 u x :=
    Nat.mul_div_cancel' hqkGN
  have hpow : q ^ (2 * k) = (q ^ k) ^ 2 := by
    rw [show 2 * k = k * 2 by omega, pow_mul]
  have hshift :
      DkMath.CosmicFormulaBinom.GN 3 u x +
          q ^ k * t * (2 * u + 3 * x) + q ^ (2 * k) * t ^ 2 =
        q ^ k * (DkMath.CosmicFormulaBinom.GN 3 u x / q ^ k +
          t * (2 * u + 3 * x) + q ^ k * t ^ 2) := by
    calc
      DkMath.CosmicFormulaBinom.GN 3 u x +
            q ^ k * t * (2 * u + 3 * x) + q ^ (2 * k) * t ^ 2 =
          q ^ k * (DkMath.CosmicFormulaBinom.GN 3 u x / q ^ k) +
            q ^ k * t * (2 * u + 3 * x) + (q ^ k) ^ 2 * t ^ 2 := by
              rw [hmul, hpow]
      _ = q ^ k * (DkMath.CosmicFormulaBinom.GN 3 u x / q ^ k +
            t * (2 * u + 3 * x) + q ^ k * t ^ 2) := by ring
  have hqpow : q ^ (k + 1) = q ^ k * q := by
    rw [pow_succ]
  have hqkpos : 0 < q ^ k := Nat.pow_pos hqpos
  have hqk_dvd_q : q ∣ q ^ k := dvd_pow_self q (by omega)
  have htail : q ∣ q ^ k * t ^ 2 :=
    dvd_mul_of_dvd_left hqk_dvd_q (t ^ 2)
  constructor
  · intro h
    have h' : q ^ k * q ∣
        q ^ k * (DkMath.CosmicFormulaBinom.GN 3 u x / q ^ k +
          t * (2 * u + 3 * x) + q ^ k * t ^ 2) := by
      have h'' : q ^ k * q ∣
          DkMath.CosmicFormulaBinom.GN 3 u x +
            q ^ k * t * (2 * u + 3 * x) + q ^ (2 * k) * t ^ 2 := by
        rw [← hqpow]
        exact h
      rw [hshift] at h''
      exact h''
    have hE : q ∣
        DkMath.CosmicFormulaBinom.GN 3 u x / q ^ k +
          t * (2 * u + 3 * x) + q ^ k * t ^ 2 := by
      exact Nat.dvd_of_mul_dvd_mul_left hqkpos h'
    exact (Nat.dvd_add_iff_left htail).mpr hE
  · intro hlin
    have hE : q ∣
        DkMath.CosmicFormulaBinom.GN 3 u x / q ^ k +
          t * (2 * u + 3 * x) + q ^ k * t ^ 2 :=
      (Nat.dvd_add_iff_left htail).mp hlin
    have h' : q ^ k * q ∣ q ^ k *
        (DkMath.CosmicFormulaBinom.GN 3 u x / q ^ k +
          t * (2 * u + 3 * x) + q ^ k * t ^ 2) :=
      Nat.mul_dvd_mul_left (q ^ k) hE
    have h'' : q ^ k * q ∣
        DkMath.CosmicFormulaBinom.GN 3 u x +
          q ^ k * t * (2 * u + 3 * x) + q ^ (2 * k) * t ^ 2 := by
      rw [hshift]
      exact h'
    rw [hqpow]
    exact h''

/-! ### Generic unique digit -/

/-- A simple cubic root has one unique next digit at every positive depth. -/
theorem existsUnique_GN_three_powLift_digit
    {q k u x : ℕ}
    (hq : Nat.Prime q)
    (hk : 1 ≤ k)
    (hqkGN : q ^ k ∣ DkMath.CosmicFormulaBinom.GN 3 u x)
    (hqder : ¬ q ∣ 2 * u + 3 * x) :
    ∃! t : Fin q,
      q ^ (k + 1) ∣
        DkMath.CosmicFormulaBinom.GN 3
          (u + q ^ k * (t : ℕ)) x := by
  letI : Fact q.Prime := ⟨hq⟩
  have hderZ : ((2 * u + 3 * x : ℕ) : ZMod q) ≠ 0 := by
    intro hzero
    exact hqder ((ZMod.natCast_eq_zero_iff (2 * u + 3 * x) q).mp hzero)
  let c : ZMod q :=
    (DkMath.CosmicFormulaBinom.GN 3 u x / q ^ k : ℕ)
  let d : ZMod q := (2 * u + 3 * x : ℕ)
  have hd : d ≠ 0 := by
    intro hd0
    apply hderZ
    simpa [d, Nat.cast_add, Nat.cast_mul] using hd0
  let z : ZMod q := -c * d⁻¹
  let t : Fin q := ⟨z.val, ZMod.val_lt z⟩
  have htZ : ((t : ℕ) : ZMod q) = z := ZMod.natCast_zmod_val z
  have hlinZ : c + ((t : ℕ) : ZMod q) * d = 0 := by
    rw [htZ]
    simp [z, hd]
  have hlin : q ∣
      DkMath.CosmicFormulaBinom.GN 3 u x / q ^ k +
        (t : ℕ) * (2 * u + 3 * x) := by
    apply (ZMod.natCast_eq_zero_iff _ q).mp
    simpa [c, d, Nat.cast_add, Nat.cast_mul] using hlinZ
  have ht_lift : q ^ (k + 1) ∣
      DkMath.CosmicFormulaBinom.GN 3 (u + q ^ k * (t : ℕ)) x :=
    (pow_succ_dvd_GN_three_add_prime_pow_mul_digit_iff hq.pos hk hqkGN).mpr hlin
  refine ⟨t, ht_lift, ?_⟩
  intro s hs
  have hslin : q ∣
      DkMath.CosmicFormulaBinom.GN 3 u x / q ^ k +
        (s : ℕ) * (2 * u + 3 * x) :=
    (pow_succ_dvd_GN_three_add_prime_pow_mul_digit_iff hq.pos hk hqkGN).mp hs
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

/-! ### Primitive application wrapper -/

/-- The arbitrary-depth lift for primitive non-ramified GN roots. -/
theorem existsUnique_GN_three_powLift_digit_of_primitive_nonramified
    {q k u x : ℕ}
    (hq : Nat.Prime q)
    (hk : 1 ≤ k)
    (hcop : Nat.Coprime u x)
    (hq3 : q ≠ 3)
    (hqkGN : q ^ k ∣ DkMath.CosmicFormulaBinom.GN 3 u x) :
    ∃! t : Fin q,
      q ^ (k + 1) ∣
        DkMath.CosmicFormulaBinom.GN 3
          (u + q ^ k * (t : ℕ)) x := by
  have hqGN : q ∣ DkMath.CosmicFormulaBinom.GN 3 u x :=
    dvd_trans (dvd_pow_self q (by omega)) hqkGN
  have hqder : ¬ q ∣ 2 * u + 3 * x :=
    prime_not_dvd_cubic_boundary_derivative hq hcop hqGN hq3
  exact existsUnique_GN_three_powLift_digit hq hk hqkGN hqder

/-! ### Derivative stability -/

/-- Derivative nondegeneracy is stable after every positive-depth shift. -/
theorem prime_not_dvd_cubic_boundary_derivative_add_prime_pow_mul
    {q k u x t : ℕ}
    (hk : 1 ≤ k)
    (hqder : ¬ q ∣ 2 * u + 3 * x) :
    ¬ q ∣ 2 * (u + q ^ k * t) + 3 * x := by
  intro hshift
  have hidentity :
      2 * (u + q ^ k * t) + 3 * x =
        (2 * u + 3 * x) + 2 * (q ^ k * t) := by
    ring
  rw [hidentity] at hshift
  have hqk : q ∣ q ^ k := dvd_pow_self q (by omega)
  have hqkt : q ∣ q ^ k * t := dvd_mul_of_dvd_left hqk t
  have htail : q ∣ 2 * (q ^ k * t) :=
    dvd_mul_of_dvd_right hqkt 2
  exact hqder ((Nat.dvd_add_iff_left htail).mpr hshift)

/-! ### Arbitrary-depth correction digit -/

/-- The finite-depth Newton/Hensel correction in `ZMod q`. -/
def GNThreeNextPowLiftDigitZMod
    (q k u x : ℕ) [Fact q.Prime] : ZMod q :=
  -((DkMath.CosmicFormulaBinom.GN 3 u x / q ^ k : ℕ) : ZMod q) *
    ((2 * u + 3 * x : ℕ) : ZMod q)⁻¹

/-- Any finite-depth lift digit is the displayed modular correction. -/
theorem GNThreeNextPowLiftDigitZMod_eq_cast_of_powLift
    {q k u x : ℕ} [Fact q.Prime]
    (hq : Nat.Prime q)
    (hk : 1 ≤ k)
    (hqkGN : q ^ k ∣ DkMath.CosmicFormulaBinom.GN 3 u x)
    (hqder : ¬ q ∣ 2 * u + 3 * x)
    (t : Fin q)
    (ht : q ^ (k + 1) ∣
      DkMath.CosmicFormulaBinom.GN 3 (u + q ^ k * (t : ℕ)) x) :
    GNThreeNextPowLiftDigitZMod q k u x = (t : ZMod q) := by
  have hderZ : ((2 * u + 3 * x : ℕ) : ZMod q) ≠ 0 := by
    intro hzero
    exact hqder ((ZMod.natCast_eq_zero_iff (2 * u + 3 * x) q).mp hzero)
  have hlin : q ∣
      DkMath.CosmicFormulaBinom.GN 3 u x / q ^ k +
        (t : ℕ) * (2 * u + 3 * x) :=
    (pow_succ_dvd_GN_three_add_prime_pow_mul_digit_iff hq.pos hk hqkGN).mp ht
  have hlinZ :
      ((DkMath.CosmicFormulaBinom.GN 3 u x / q ^ k +
        (t : ℕ) * (2 * u + 3 * x) : ℕ) : ZMod q) = 0 :=
    (ZMod.natCast_eq_zero_iff _ q).2 hlin
  have hlinZ' :
      ((DkMath.CosmicFormulaBinom.GN 3 u x / q ^ k : ℕ) : ZMod q) +
        ((t : ℕ) : ZMod q) * ((2 * u + 3 * x : ℕ) : ZMod q) = 0 := by
    simpa [Nat.cast_add, Nat.cast_mul] using hlinZ
  have hsolve :
      ((t : ℕ) : ZMod q) * ((2 * u + 3 * x : ℕ) : ZMod q) =
        -((DkMath.CosmicFormulaBinom.GN 3 u x / q ^ k : ℕ) : ZMod q) := by
    linear_combination hlinZ'
  have hderZ' : (2 * (u : ZMod q) + 3 * (x : ZMod q)) ≠ 0 := by
    simpa [Nat.cast_add, Nat.cast_mul] using hderZ
  dsimp [GNThreeNextPowLiftDigitZMod]
  calc
    -((DkMath.CosmicFormulaBinom.GN 3 u x / q ^ k : ℕ) : ZMod q) *
          ((2 * u + 3 * x : ℕ) : ZMod q)⁻¹ =
        (((t : ℕ) : ZMod q) * ((2 * u + 3 * x : ℕ) : ZMod q)) *
          ((2 * u + 3 * x : ℕ) : ZMod q)⁻¹ := by rw [hsolve]
    _ = (t : ZMod q) := by simp [hderZ']

/-! ### GNPC-007 and depth-three regressions -/

example : ∃! t : Fin 7,
    7 ^ 2 ∣ DkMath.CosmicFormulaBinom.GN 3 (1 + 7 * (t : ℕ)) 1 := by
  have hqGN : 7 ∣ DkMath.CosmicFormulaBinom.GN 3 1 1 := by
    rw [GN_three_dual_explicit]
    norm_num
  have hqder : ¬ 7 ∣ 2 * 1 + 3 * 1 := by norm_num
  simpa using existsUnique_GN_three_powLift_digit
    (q := 7) (k := 1) (u := 1) (x := 1)
    (by norm_num) (by norm_num) hqGN hqder

example : 7 ^ 3 ∣ DkMath.CosmicFormulaBinom.GN 3 323 1 := by
  rw [GN_three_dual_explicit]
  norm_num

example : 7 ^ 3 ∣ DkMath.CosmicFormulaBinom.GN 3 17 1 := by
  rw [GN_three_dual_explicit]
  norm_num

example {t : Fin 7}
    (ht : 7 ^ 3 ∣ DkMath.CosmicFormulaBinom.GN 3 (29 + 7 ^ 2 * (t : ℕ)) 1) :
    t = 6 := by
  have hqkGN : 7 ^ 2 ∣ DkMath.CosmicFormulaBinom.GN 3 29 1 := by
    rw [GN_three_dual_explicit]
    norm_num
  have hu := existsUnique_GN_three_powLift_digit
    (q := 7) (k := 2) (u := 29) (x := 1)
    (by norm_num) (by norm_num) hqkGN (by norm_num)
  exact hu.unique ht (by
    change 7 ^ 3 ∣ DkMath.CosmicFormulaBinom.GN 3 323 1
    rw [GN_three_dual_explicit]
    norm_num)

example {t : Fin 7}
    (ht : 7 ^ 3 ∣ DkMath.CosmicFormulaBinom.GN 3 (17 + 7 ^ 2 * (t : ℕ)) 1) :
    t = 0 := by
  have hqkGN : 7 ^ 2 ∣ DkMath.CosmicFormulaBinom.GN 3 17 1 := by
    rw [GN_three_dual_explicit]
    norm_num
  have hu := existsUnique_GN_three_powLift_digit
    (q := 7) (k := 2) (u := 17) (x := 1)
    (by norm_num) (by norm_num) hqkGN (by norm_num)
  exact hu.unique ht (by
    change 7 ^ 3 ∣ DkMath.CosmicFormulaBinom.GN 3 17 1
    rw [GN_three_dual_explicit]
    norm_num)

end DkMath.NumberTheory
