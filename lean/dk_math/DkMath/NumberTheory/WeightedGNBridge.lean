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
If the inner Beam is divisible by `m`, then the difference between `GN d x u`
and its right-boundary term is divisible by `m`.
-/
theorem dvd_GN_sub_rightBoundary_of_dvd_filteredGTailOneSum_true
    {m d x u : ℕ} (hd : 0 < d)
    (hbeam : m ∣ filteredGTailOneSum d x u (fun _ => True)) :
    m ∣ GN d x u - x ^ (d - 1) := by
  rw [GN_eq_filteredGTailOneSum_true_add_right hd]
  simpa [Nat.add_sub_cancel] using hbeam

/--
If the inner Beam is divisible by `m`, it has an explicit quotient witness.
-/
theorem exists_filteredGTailOneSum_true_eq_mul_of_dvd
    {m d x u : ℕ}
    (hbeam : m ∣ filteredGTailOneSum d x u (fun _ => True)) :
    ∃ B, filteredGTailOneSum d x u (fun _ => True) = m * B := by
  rcases hbeam with ⟨B, hB⟩
  exact ⟨B, hB⟩

/--
If the inner Beam is divisible by `m`, then `GN d x u` has an explicit
boundary-plus-multiple decomposition.
-/
theorem exists_GN_eq_mul_add_rightBoundary_of_dvd_filteredGTailOneSum_true
    {m d x u : ℕ} (hd : 0 < d)
    (hbeam : m ∣ filteredGTailOneSum d x u (fun _ => True)) :
    ∃ B, GN d x u = m * B + x ^ (d - 1) := by
  rcases hbeam with ⟨B, hB⟩
  refine ⟨B, ?_⟩
  rw [GN_eq_filteredGTailOneSum_true_add_right hd, hB]

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

/--
Prime rows make the difference `GN p x u - x^(p-1)` divisible by `p`.
-/
theorem prime_GN_sub_rightBoundary_dvd
    {p x u : ℕ} (hp : p.Prime) :
    p ∣ GN p x u - x ^ (p - 1) := by
  exact
    dvd_GN_sub_rightBoundary_of_dvd_filteredGTailOneSum_true hp.pos
      (prime_dvd_filteredGTailOneSum_true hp)

/--
Prime rows give an explicit quotient witness for the inner Beam of `GN`.
-/
theorem prime_exists_filteredGTailOneSum_true_eq_mul
    {p x u : ℕ} (hp : p.Prime) :
    ∃ B, filteredGTailOneSum p x u (fun _ => True) = p * B := by
  exact
    exists_filteredGTailOneSum_true_eq_mul_of_dvd
      (prime_dvd_filteredGTailOneSum_true hp)

/--
Prime rows decompose `GN p x u` as a `p`-multiple inner Beam plus the
right-boundary term.
-/
theorem prime_exists_GN_eq_mul_add_rightBoundary
    {p x u : ℕ} (hp : p.Prime) :
    ∃ B, GN p x u = p * B + x ^ (p - 1) := by
  exact
    exists_GN_eq_mul_add_rightBoundary_of_dvd_filteredGTailOneSum_true hp.pos
      (prime_dvd_filteredGTailOneSum_true hp)

end NumberTheory
end DkMath
