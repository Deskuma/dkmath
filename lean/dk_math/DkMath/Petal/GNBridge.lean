/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Petal.Forms
import DkMath.FLT.CosmicPetalBridge
import DkMath.NumberTheory.WeightedGNBridge

#print "file: DkMath.Petal.GNBridge"

/-!
# Petal Bridge to `GN`

This file records the first Petal-facing bridge theorems.

The key observation is that the degree-three `GN` kernel is exactly the Petal
detector `S0_nat` after the substitution `x = c - b`, `u = b`.
-/

namespace DkMath
namespace Petal

open DkMath.CosmicFormulaBinom
open DkMath.FLT.PetalDetect

/--
Petal-facing direction of the degree-three GN/S0 bridge.

This reads the Petal detector as the visible degree-three face of `GN`.
-/
theorem S0_nat_eq_GN_three_sub {c b : ℕ} (hbc : b < c) :
    S0_nat c b = GN 3 (c - b) b := by
  exact (DkMath.FLT.GN_three_sub_eq_S0_nat hbc).symm

/--
If the boundary gap `c - b` is not divisible by `3`, then the degree-three Petal
detector is congruent to `1` modulo `3`.

This is the `d = 3` Petal form of the Fermat-boundary GN bridge.
-/
theorem three_S0_nat_modEq_one_of_not_dvd_sub
    {c b : ℕ} (hbc : b < c) (h3 : ¬ 3 ∣ c - b) :
    S0_nat c b ≡ 1 [MOD 3] := by
  rw [S0_nat_eq_GN_three_sub hbc]
  exact
    DkMath.NumberTheory.prime_GN_modEq_one_of_not_dvd_x
      (p := 3) (x := c - b) (u := b) Nat.prime_three h3

/--
If the boundary gap `c - b` is not divisible by `3`, then `3` cannot divide the
degree-three Petal detector.

This transfers the GN non-divisibility bridge to the Petal `S0_nat` surface.
-/
theorem three_not_dvd_S0_nat_of_not_dvd_sub
    {c b : ℕ} (hbc : b < c) (h3 : ¬ 3 ∣ c - b) :
    ¬ 3 ∣ S0_nat c b := by
  rw [S0_nat_eq_GN_three_sub hbc]
  exact
    DkMath.NumberTheory.prime_not_dvd_GN_of_not_dvd_x
      (p := 3) (x := c - b) (u := b) Nat.prime_three h3

end Petal
end DkMath
