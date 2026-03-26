/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.ZsigmondyCyclotomic

#print "file: DkMath.NumberTheory.ZsigmondyCyclotomicNoLift"

set_option linter.style.longLine false
set_option linter.style.emptyLine false

namespace DkMath.NumberTheory.GcdNext

open DkMath.CosmicFormulaBinom

/--
墓標: primitive-prime assumptions alone do not force `¬ q^2 ∣ GN`.

The counterexample `(d, a, b, q) = (3, 5, 3, 7)` shows that the old
`noLift_GN_of_primitive_prime_factor` shape is false and must not be used as a
permanent spine.
-/
theorem noLift_GN_of_primitive_prime_factor_is_false :
    ¬ (∀ {a b d q : ℕ},
        Nat.Prime d → 3 ≤ d →
        b < a → 0 < b → Nat.Coprime a b →
        ¬ d ∣ a - b →
        Nat.Prime q → q ∣ a ^ d - b ^ d → ¬ q ∣ a - b →
        ¬ q ^ 2 ∣ GN d (a - b) b) := by
  intro h
  have hbad :=
    h (a := 5) (b := 3) (d := 3) (q := 7)
      (by decide)
      (by decide)
      (by decide)
      (by decide)
      (by decide)
      (by decide)
      (by decide)
      (by decide)
      (by decide)
  exact hbad (by decide)

end DkMath.NumberTheory.GcdNext
