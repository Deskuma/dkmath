/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.ABC.GNValuationSplit
import DkMath.NumberTheory.Gcd.GN

#print "file: DkMath.ABC.GNExceptionalSplit"

set_option linter.style.longLine false
set_option linter.style.emptyLine false

/-!
# Exponent-exceptional and non-exceptional GN channels

For an ABC triple, every common divisor of the boundary `T.a` and the kernel
`GN n T.a T.b` divides the exponent `n`.  Thus a channel `q ∤ n` occurring on
the GN side cannot also occur on the boundary side.
-/

namespace DkMath.ABC

open DkMath.CosmicFormulaBinom

/-- The common boundary–GN divisor is confined to the exponent. -/
theorem Triple.gcd_boundary_GN_dvd_exp
    (T : Triple) {n : ℕ} (hn : 1 ≤ n) (ha : 0 < T.a) :
    Nat.gcd T.a (GN n T.a T.b) ∣ n := by
  have hb_lt : T.b < T.a + T.b := by omega
  have hcop : Nat.Coprime (T.a + T.b) T.b :=
    (Nat.coprime_add_self_left).2 T.hcop
  simpa [Nat.add_sub_cancel_left] using
    (DkMath.NumberTheory.Gcd.gcd_gap_GN_dvd_exp
      (p := n) (z := T.a + T.b) (y := T.b) hn hb_lt hcop)

/-- Every common divisor of the boundary and GN kernel divides the exponent. -/
theorem Triple.dvd_exp_of_dvd_boundary_of_dvd_GN
    (T : Triple) {n q : ℕ}
    (hn : 1 ≤ n) (ha : 0 < T.a)
    (hq_boundary : q ∣ T.a) (hq_GN : q ∣ GN n T.a T.b) :
    q ∣ n := by
  exact dvd_trans (Nat.dvd_gcd hq_boundary hq_GN)
    (T.gcd_boundary_GN_dvd_exp hn ha)

/--
A non-exceptional GN channel `q ∤ n` is absent from the ABC boundary.

No primality assumption is needed: this holds for every divisor occurring on
the GN side.
-/
theorem Triple.not_dvd_boundary_of_not_dvd_exp_of_dvd_GN
    (T : Triple) {n q : ℕ}
    (hn : 1 ≤ n) (ha : 0 < T.a)
    (hq_exp : ¬ q ∣ n) (hq_GN : q ∣ GN n T.a T.b) :
    ¬ q ∣ T.a := by
  intro hq_boundary
  exact hq_exp (T.dvd_exp_of_dvd_boundary_of_dvd_GN
    hn ha hq_boundary hq_GN)

/--
On a non-exceptional prime channel present in GN, the full power-difference
valuation is concentrated on the GN kernel.
-/
theorem Triple.padic_powerDiff_eq_GN_of_not_dvd_exp_of_dvd_GN
    (T : Triple) {n q : ℕ}
    (hn : 2 ≤ n) (ha : 0 < T.a) (hb : 0 < T.b)
    (hq : Nat.Prime q) (hq_exp : ¬ q ∣ n)
    (hq_GN : q ∣ GN n T.a T.b) :
    padicValNat q (T.c ^ n - T.b ^ n) =
      padicValNat q (GN n T.a T.b) := by
  have hq_boundary : ¬ q ∣ T.a :=
    T.not_dvd_boundary_of_not_dvd_exp_of_dvd_GN
      (Nat.le_trans (by decide) hn) ha hq_exp hq_GN
  exact T.padic_powerDiff_eq_GN_of_not_dvd_boundary hn ha hb hq hq_boundary

/-- Coprimality with the exponent removes all boundary–GN overlap. -/
theorem Triple.coprime_boundary_GN_of_coprime_exp
    (T : Triple) {n : ℕ}
    (hn : 1 ≤ n) (ha : 0 < T.a) (hcop_exp : Nat.Coprime T.a n) :
    Nat.Coprime T.a (GN n T.a T.b) := by
  exact
    DkMath.NumberTheory.Gcd.coprime_boundary_GN_of_coprime_add_of_coprime_exp
      hn ha ((Nat.coprime_add_self_left).2 T.hcop) hcop_exp

end DkMath.ABC
