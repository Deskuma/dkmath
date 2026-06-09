/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.WeightedBinomial
import DkMath.CosmicFormula.CosmicFormulaBinom

#print "file: DkMath.NumberTheory.WeightedGNBridge"

namespace DkMath
namespace NumberTheory

open DkMath.CosmicFormulaBinom

/-!
## Weighted Beam bridge to `GN`

This file connects the coefficient/weighted-binomial sieve layer to the legacy
`GN` API used by the Zsigmondy and primitive-prime files.

The main observation is deliberately modest:

* the inner Beam of `GN d x u` is controlled by binomial coefficients;
* the right-boundary term `x^(d-1)` is not controlled by those coefficients;
* therefore prime rows give a congruence
  `GN p x u ≡ x^(p-1) [MOD p]`, not a divisibility statement for all of `GN`.
-/

/--
The legacy `GN` factor splits into the weighted inner Beam plus the
right-boundary term.

This is the `GN`-facing form of `GTail_one_eq_innerBeam_add_right`.
-/
theorem GN_eq_filteredGTailOneSum_true_add_right
    {d x u : ℕ} (hd : 0 < d) :
    GN d x u =
      filteredGTailOneSum d x u (fun _ => True) + x ^ (d - 1) := by
  simpa [GN] using
    (GTail_one_eq_innerBeam_add_right (d := d) (x := x) (u := u) hd)

/--
If the inner Beam is divisible by `m`, then `GN d x u` is congruent to its
right-boundary term modulo `m`.
-/
theorem GN_modEq_rightBoundary_of_dvd_filteredGTailOneSum_true
    {m d x u : ℕ} (hd : 0 < d)
    (hbeam : m ∣ filteredGTailOneSum d x u (fun _ => True)) :
    GN d x u ≡ x ^ (d - 1) [MOD m] := by
  rw [GN_eq_filteredGTailOneSum_true_add_right hd]
  have hzero :
      filteredGTailOneSum d x u (fun _ => True) ≡ 0 [MOD m] :=
    Nat.modEq_zero_iff_dvd.mpr hbeam
  have hright : x ^ (d - 1) ≡ x ^ (d - 1) [MOD m] := Nat.ModEq.refl _
  simpa using hzero.add hright

/--
Prime rows make the `GN` inner Beam vanish modulo `p`, leaving only the
right-boundary term.
-/
theorem prime_GN_modEq_rightBoundary
    {p x u : ℕ} (hp : p.Prime) :
    GN p x u ≡ x ^ (p - 1) [MOD p] := by
  exact
    GN_modEq_rightBoundary_of_dvd_filteredGTailOneSum_true hp.pos
      (prime_dvd_filteredGTailOneSum_true hp)

end NumberTheory
end DkMath
