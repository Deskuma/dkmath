/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.ABC.GNPowerLift
import DkMath.ABC.PadicValNat

#print "file: DkMath.ABC.GNValuationSplit"

set_option linter.style.longLine false
set_option linter.style.emptyLine false

/-!
# The boundary–GN valuation split in ABC coordinates

This module applies `padicValNat` to the deterministic factorization underlying
`Triple.gnPowerLift`.  It separates the valuation carried by the ABC boundary
`T.a` from the valuation carried by the kernel `GN n T.a T.b`.

No exceptional-prime layer or valuation-excess notion is introduced here.
-/

namespace DkMath.ABC

open DkMath.CosmicFormulaBinom

/--
The difference of powers in an ABC triple factors into its left boundary and
the corresponding `GN` kernel.

The identity holds for every natural exponent; positivity assumptions are not
needed at this purely algebraic layer.
-/
theorem Triple.powerDiff_eq_boundary_mul_GN (T : Triple) (n : ℕ) :
    T.c ^ n - T.b ^ n = T.a * GN n T.a T.b := by
  rw [← T.gnPowerLift_sum n]
  exact Nat.add_sub_cancel_right (T.a * GN n T.a T.b) (T.b ^ n)

/--
The `q`-adic valuation of the power difference is the sum of the valuation on
the ABC boundary and the valuation on the `GN` kernel.
-/
theorem Triple.padic_powerDiff_eq_boundary_add_GN
    (T : Triple) {n q : ℕ}
    (hn : 2 ≤ n) (ha : 0 < T.a) (hb : 0 < T.b) (hq : Nat.Prime q) :
    padicValNat q (T.c ^ n - T.b ^ n) =
      padicValNat q T.a + padicValNat q (GN n T.a T.b) := by
  have hGN : GN n T.a T.b ≠ 0 :=
    GN_ne_zero_nat_of_two_le hn ha hb
  haveI : Fact q.Prime := ⟨hq⟩
  rw [T.powerDiff_eq_boundary_mul_GN n]
  exact padicValNat.mul (Nat.ne_of_gt ha) hGN

/--
The valuation of the left coordinate of `gnPowerLift` has the same
boundary–kernel decomposition.
-/
theorem Triple.padic_gnPowerLift_a_eq_boundary_add_GN
    (T : Triple) {n q : ℕ}
    (hn : 2 ≤ n) (ha : 0 < T.a) (hb : 0 < T.b) (hq : Nat.Prime q) :
    padicValNat q (T.gnPowerLift n).a =
      padicValNat q T.a + padicValNat q (GN n T.a T.b) := by
  rw [T.gnPowerLift_a]
  have hGN : GN n T.a T.b ≠ 0 :=
    GN_ne_zero_nat_of_two_le hn ha hb
  haveI : Fact q.Prime := ⟨hq⟩
  exact padicValNat.mul (Nat.ne_of_gt ha) hGN

/--
If `q` does not divide the ABC boundary, all of the valuation of the power
difference is carried by the `GN` kernel.
-/
theorem Triple.padic_powerDiff_eq_GN_of_not_dvd_boundary
    (T : Triple) {n q : ℕ}
    (hn : 2 ≤ n) (ha : 0 < T.a) (hb : 0 < T.b) (hq : Nat.Prime q)
    (hq_boundary : ¬ q ∣ T.a) :
    padicValNat q (T.c ^ n - T.b ^ n) =
      padicValNat q (GN n T.a T.b) := by
  rw [T.padic_powerDiff_eq_boundary_add_GN hn ha hb hq,
    padicValNat.eq_zero_of_not_dvd hq_boundary, zero_add]

end DkMath.ABC
