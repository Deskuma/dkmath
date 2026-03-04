/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.ZsigmondyCyclotomicResearch

set_option linter.style.longLine false
set_option linter.style.emptyLine false

namespace DkMath.NumberTheory.GcdNext

open DkMath.CosmicFormulaBinom

/--
Phase-15 の最小条件を `NumberTheory` 側へ固定する常設 spine。

primitive prime divisor branch の標準仮定から、cyclotomic factor
`GN d (a - b) b` に 2 段 lift が起きないことを直接与える。
現在の証明は `padicValNat_primitive_prime_factor_le_one` を経由するため、
未解決の研究課題はその valuation spine の上流へ局所化される。
-/
theorem noLift_GN_of_primitive_prime_factor
    {a b d q : ℕ}
    (hd_prime : Nat.Prime d) (hd_ge : 3 ≤ d)
    (hab_lt : b < a) (hb : 0 < b) (hab : Nat.Coprime a b)
    (hd_ndiv : ¬ d ∣ a - b)
    (hq_prime : Nat.Prime q)
    (hq_div : q ∣ a ^ d - b ^ d) (hq_ndiv : ¬ q ∣ a - b) :
    ¬ q ^ 2 ∣ GN d (a - b) b := by
  let N := GN d (a - b) b
  have hd_pos : 0 < d := hd_prime.pos
  have hN_ne : N ≠ 0 := by
    have hgap_pos : 0 < a - b := Nat.sub_pos_of_lt hab_lt
    exact
      GN_ne_zero_nat_of_two_le
        (d := d) (x := a - b) (u := b)
        (le_trans (by decide : 2 ≤ 3) hd_ge)
        hgap_pos
        hb
  have hfactor : a ^ d - b ^ d = (a - b) * N := by
    simpa [N] using pow_sub_pow_factor_cosmic_N hd_pos hab_lt
  have hpadic_eq : padicValNat q (a ^ d - b ^ d) = padicValNat q N := by
    have hpadic :=
      padicValNat_factorization hd_pos hab_lt hq_prime hfactor hN_ne
    have hzero : padicValNat q (a - b) = 0 := by
      exact padicValNat.eq_zero_of_not_dvd hq_ndiv
    rw [hzero, zero_add] at hpadic
    exact hpadic
  have hN_le : padicValNat q N ≤ 1 := by
    rw [← hpadic_eq]
    exact
      padicValNat_primitive_prime_factor_le_one
        (a := a) (b := b) (d := d) (q := q)
        hd_prime
        hd_ge
        hab_lt
        hb
        hab
        hd_ndiv
        hq_prime
        hq_div
        hq_ndiv
  intro hq2_dvd_GN
  have h2_le : 2 ≤ padicValNat q N := by
    exact (@padicValNat_dvd_iff_le q (Fact.mk hq_prime) N 2 hN_ne).1 hq2_dvd_GN
  exact (not_le_of_gt h2_le) hN_le

end DkMath.NumberTheory.GcdNext
