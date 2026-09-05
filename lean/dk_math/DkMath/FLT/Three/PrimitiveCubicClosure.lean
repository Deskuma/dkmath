/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Three.PrimitiveCubicDescent

#print "file: DkMath.FLT.Three.PrimitiveCubicClosure"

namespace DkMath.FLT.Three

/-!
# Well-founded closure of primitive cubic descent

The strict product decrease from `PrimitiveCubicDescent` is closed by strong
induction on the natural product measure.  This module deliberately ends at
the primitive, coprime-positive theorem; arbitrary gcd normalization remains
the next checkpoint.
-/

/-- No positive primitive cubic pack can exist, by strong induction on `a*b*c`. -/
theorem primitiveCubicPack_false
    {a b c : ℕ} (p : PrimitiveCubicPack a b c) : False := by
  have noAt : ∀ n : ℕ, ∀ {a b c : ℕ},
      PrimitiveCubicPack a b c → a * b * c = n → False := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro a b c p hp
        obtain ⟨x, y, z, next, hlt⟩ :=
          exists_smaller_primitiveCubicPack p
        exact ih (x * y * z)
          (by simpa [hp] using hlt)
          next rfl
  exact noAt (a * b * c) p rfl

/-- The unconditional primitive FLT3 endpoint of the Three tower. -/
theorem FLT_d3_unconditional
    {a b c : ℕ}
    (ha : 0 < a)
    (hb : 0 < b)
    (hc : 0 < c)
    (hab : Nat.Coprime a b) :
    a ^ 3 + b ^ 3 ≠ c ^ 3 := by
  intro hEq
  exact primitiveCubicPack_false
    (primitiveCubicPack_of_hypotheses ha hb hc hab hEq)

end DkMath.FLT.Three
