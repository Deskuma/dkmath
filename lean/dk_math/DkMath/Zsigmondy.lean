/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Algebra.DiffPow
import DkMath.CosmicFormula.CoreBeamGap
import DkMath.NumberTheory.ZsigmondyCyclotomic

#print "file: DkMath.Zsigmondy"

set_option linter.style.longLine false

namespace DkMath.Zsigmondy

open DkMath.Algebra.DiffPow

/-- Cosmic Body over integers: the shifted power difference `(x + u)^d - u^d`. -/
def BodyZ (x u : ℤ) (d : ℕ) : ℤ := BodyPow x u d

/-- Cosmic Body over naturals: the shifted power difference `(x + u)^d - u^d`. -/
def BodyN (x u : ℕ) (d : ℕ) : ℕ := (x + u) ^ d - u ^ d

/-- Natural-number kernel specialized to `a = x + u`, `b = u`. -/
def KernelN (x u : ℕ) (d : ℕ) : ℕ := diffPowSum' (x + u) u d

/-- The DiffPow kernel specialized to `a = x + u`, `b = u`. -/
def KernelZ (x u : ℤ) (d : ℕ) : ℤ := diffPowSum (x + u) u d

/-- A primitive prime divisor of `a^n - b^n`. -/
def PrimitivePrimeDivisor (a b n q : ℕ) : Prop :=
  Nat.Prime q ∧ q ∣ a ^ n - b ^ n ∧ ∀ m : ℕ, 0 < m → m < n → ¬ q ∣ a ^ m - b ^ m

/-- Over `ℤ`, the cosmic body factors through the boundary `x`. -/
theorem body_eq_boundary_mul_kernel_int (x u : ℤ) (d : ℕ) :
    BodyZ x u d = x * KernelZ x u d := by
  simpa [BodyZ, KernelZ, BodyPow] using BodyPow_factor x u d

/-- Over `ℕ`, the cosmic body factors through the boundary `x`. -/
theorem body_eq_boundary_mul_kernel_nat (x u d : ℕ) :
    BodyN x u d = x * KernelN x u d := by
  have hpow :
      (x + u) ^ d = u ^ d + x * KernelN x u d := by
    simpa [KernelN, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.add_sub_cancel_left] using
      (pow_sub_pow_nat (a := x + u) (b := u) (d := d) (Nat.le_add_left u x))
  have hu_le : u ^ d ≤ (x + u) ^ d := Nat.pow_le_pow_left (Nat.le_add_left u x) d
  unfold BodyN
  omega

/-- If a prime divides the body but not the boundary, it must divide the kernel. -/
theorem prime_dvd_body_of_not_dvd_boundary_imp_dvd_kernel
    {x u d q : ℕ}
    (hq : Nat.Prime q)
    (hbody : q ∣ BodyN x u d)
    (hndiv : ¬ q ∣ x) :
    q ∣ KernelN x u d := by
  rw [body_eq_boundary_mul_kernel_nat] at hbody
  have hcop : Nat.Coprime q x := (Nat.Prime.coprime_iff_not_dvd hq).2 hndiv
  exact Nat.Coprime.dvd_of_dvd_mul_left hcop hbody

/-- For positive `x`, the cubic body is exactly `x * GN 3 x u`. -/
theorem body_three_eq_boundary_mul_GN_nat (x u : ℕ) (hx : 0 < x) :
    BodyN x u 3 = x * DkMath.CosmicFormulaBinom.GN 3 x u := by
  have hlt : u < x + u := by
    omega
  simpa [BodyN, Nat.add_sub_cancel_left] using
    (DkMath.NumberTheory.GcdNext.pow_sub_pow_factor_cosmic_N
      (a := x + u) (b := u) (d := 3) (by norm_num) hlt)

/-- The cubic beam is the sum of the two mixed terms. -/
theorem beam_three_explicit_nat (x u : ℕ) :
    DkMath.CosmicFormula.CoreBeamGap.Beam 3 x u = 3 * x ^ 2 * u + 3 * x * u ^ 2 := by
  unfold DkMath.CosmicFormula.CoreBeamGap.Beam
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  ring

/-- For positive `x`, the cubic body splits into core plus beam. -/
theorem body_three_eq_core_add_beam_nat (x u : ℕ) (hx : 0 < x) :
    BodyN x u 3 = x ^ 3 + DkMath.CosmicFormula.CoreBeamGap.Beam 3 x u := by
  calc
    BodyN x u 3 = x * DkMath.CosmicFormulaBinom.GN 3 x u :=
      body_three_eq_boundary_mul_GN_nat x u hx
    _ = x ^ 3 + DkMath.CosmicFormula.CoreBeamGap.Beam 3 x u := by
      simpa [DkMath.CosmicFormulaBinom.BodyN, DkMath.CosmicFormula.CoreBeamGap.Core] using
        (DkMath.CosmicFormula.CoreBeamGap.body_eq_core_add_beam
          (R := ℕ) (d := 3) (by norm_num) x u)

/-- The cubic body written with the explicit cubic `GN` polynomial. -/
theorem body_three_eq_boundary_mul_GN_explicit_nat (x u : ℕ) (hx : 0 < x) :
    BodyN x u 3 = x * (x ^ 2 + 3 * x * u + 3 * u ^ 2) := by
  rw [body_three_eq_boundary_mul_GN_nat x u hx,
    DkMath.NumberTheory.GcdNext.GN_three_explicit]

/-- The cubic body written as core plus the explicit beam. -/
theorem body_three_eq_core_add_beam_explicit_nat (x u : ℕ) (hx : 0 < x) :
    BodyN x u 3 = x ^ 3 + (3 * x ^ 2 * u + 3 * x * u ^ 2) := by
  rw [body_three_eq_core_add_beam_nat x u hx, beam_three_explicit_nat]

/-- Over `ℕ`, a primitive prime divisor exists for the cosmic body. -/
theorem exists_primitive_prime_factor_body_nat {x u d : ℕ}
    (hd_prime : Nat.Prime d) (hd_ge : 3 ≤ d)
    (hx : 0 < x) (hu : 0 < u)
    (hcop : Nat.Coprime (x + u) u)
    (hnd : ¬ d ∣ x) :
    ∃ q : ℕ, Nat.Prime q ∧ q ∣ BodyN x u d ∧ ¬ q ∣ x := by
  have hlt : u < x + u := by
    omega
  obtain ⟨q, hq_prime, hq_body, hq_x⟩ :=
    DkMath.NumberTheory.GcdNext.exists_primitive_prime_factor_basic
      hd_prime hd_ge hlt hu hcop (by simpa [Nat.add_sub_cancel_left] using hnd)
  refine ⟨q, hq_prime, ?_, ?_⟩
  · simpa [BodyN] using hq_body
  · simpa [Nat.add_sub_cancel_left] using hq_x

/-- Prime-exponent Zsigmondy packaged as a primitive-prime-divisor existence theorem. -/
theorem exists_primitivePrimeDivisor_prime_exp {a b d : ℕ}
    (hd_prime : Nat.Prime d) (hd_ge : 3 ≤ d)
    (hab_lt : b < a) (hb : 0 < b) (hab : Nat.Coprime a b)
    (hnd : ¬ d ∣ a - b) :
    ∃ q, PrimitivePrimeDivisor a b d q := by
  obtain ⟨q, hq_prime, hq_div, hq_ndiv⟩ :=
    DkMath.NumberTheory.GcdNext.exists_primitive_prime_factor_prime
      hd_prime hd_ge hab_lt hb hab hnd
  have hd_gt_one : 1 < d := by
    omega
  refine ⟨q, hq_prime, hq_div, ?_⟩
  intro m hm_pos hm_lt
  exact DkMath.NumberTheory.GcdNext.prime_exp_not_dvd_diff_imp_primitive
    hd_prime hd_gt_one hq_prime hab hab_lt hb hq_div hq_ndiv hm_pos hm_lt

/-- Specialized primitive-prime-divisor existence for the cosmic body. -/
theorem exists_primitivePrimeDivisor_body_nat {x u d : ℕ}
    (hd_prime : Nat.Prime d) (hd_ge : 3 ≤ d)
    (hx : 0 < x) (hu : 0 < u)
    (hcop : Nat.Coprime (x + u) u)
    (hnd : ¬ d ∣ x) :
    ∃ q, PrimitivePrimeDivisor (x + u) u d q := by
  have hlt : u < x + u := by
    omega
  simpa [Nat.add_sub_cancel_left] using
    (exists_primitivePrimeDivisor_prime_exp
      (a := x + u) (b := u) (d := d) hd_prime hd_ge hlt hu hcop
      (by simpa [Nat.add_sub_cancel_left] using hnd))

/-- A primitive prime divisor of the body stays primitive for every lower exponent. -/
theorem primitive_prime_factor_body_nat {x u d q : ℕ}
    (hd_prime : Nat.Prime d) (hd_ge : 3 ≤ d)
    (hx : 0 < x) (hu : 0 < u)
    (hcop : Nat.Coprime (x + u) u)
    (hq_prime : Nat.Prime q)
    (hq_div : q ∣ BodyN x u d)
    (hq_ndiv : ¬ q ∣ x) :
    ∀ {k : ℕ}, 0 < k → k < d → ¬ q ∣ BodyN x u k := by
  have hlt : u < x + u := by
    omega
  have hd_gt_one : 1 < d := by
    omega
  have hq_div_diff : q ∣ (x + u) ^ d - u ^ d := by
    simpa [BodyN] using hq_div
  have hq_ndiv_diff : ¬ q ∣ (x + u) - u := by
    simpa [Nat.add_sub_cancel_left] using hq_ndiv
  intro k hk_pos hk_lt
  simpa [BodyN] using
    (DkMath.NumberTheory.GcdNext.prime_exp_not_dvd_diff_imp_primitive
      hd_prime hd_gt_one hq_prime hcop hlt hu hq_div_diff hq_ndiv_diff hk_pos hk_lt)

end DkMath.Zsigmondy
