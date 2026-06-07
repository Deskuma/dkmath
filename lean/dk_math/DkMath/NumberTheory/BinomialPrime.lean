/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.Data.Nat.Choose.Dvd

#print "file: DkMath.NumberTheory.BinomialPrime"

namespace DkMath
namespace NumberTheory

/-!
## Prime rows in Pascal's triangle

This file records the first stable divisibility layer for the binomial roadmap:
if `p` is prime, then every inner coefficient in row `p` is divisible by `p`.

The converse direction is intentionally left to a later file/checkpoint, where
we can decide whether to use a mathlib theorem or prove the composite witness
directly.
-/

/-- All inner binomial coefficients in row `d` are divisible by `m`. -/
def AllInnerChooseDivisible (d m : ℕ) : Prop :=
  ∀ k, 0 < k → k < d → m ∣ Nat.choose d k

/--
Prime rows carry their prime modulus through every inner binomial coefficient.
-/
theorem prime_allInnerChooseDivisible_self
    {p : ℕ} (hp : p.Prime) :
    AllInnerChooseDivisible p p := by
  intro k hk0 hkp
  exact hp.dvd_choose_self hk0.ne' hkp

/--
Alias phrased as a row theorem. This is the API shape used by the weighted
binomial layer.
-/
theorem prime_dvd_inner_choose
    {p k : ℕ} (hp : p.Prime) (hk0 : 0 < k) (hkp : k < p) :
    p ∣ Nat.choose p k :=
  prime_allInnerChooseDivisible_self hp k hk0 hkp

end NumberTheory
end DkMath
