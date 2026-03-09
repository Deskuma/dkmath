/- 
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Algebra.DiffPow
import DkMath.NumberTheory.ZsigmondyCyclotomic

#print "file: DkMath.Zsigmondy"

set_option linter.style.longLine false

namespace DkMath.Zsigmondy

open DkMath.Algebra.DiffPow

/-- Cosmic Body over integers: the shifted power difference `(x + u)^d - u^d`. -/
def BodyZ (x u : ℤ) (d : ℕ) : ℤ := BodyPow x u d

/-- Cosmic Body over naturals: the shifted power difference `(x + u)^d - u^d`. -/
def BodyN (x u : ℕ) (d : ℕ) : ℕ := (x + u) ^ d - u ^ d

/-- The DiffPow kernel specialized to `a = x + u`, `b = u`. -/
def KernelZ (x u : ℤ) (d : ℕ) : ℤ := diffPowSum (x + u) u d

/-- Over `ℤ`, the cosmic body factors through the boundary `x`. -/
theorem body_eq_boundary_mul_kernel_int (x u : ℤ) (d : ℕ) :
    BodyZ x u d = x * KernelZ x u d := by
  simpa [BodyZ, KernelZ, BodyPow] using BodyPow_factor x u d

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
