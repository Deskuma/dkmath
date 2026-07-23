/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.ABC.Triple
import DkMath.CosmicFormula.CosmicFormulaBinom

#print "file: DkMath.ABC.GNPowerLift"

set_option linter.style.longLine false
set_option linter.style.emptyLine false

/-!
# ABC triples lifted through `GN`

For an additive coprime triple `a + b = c`, the Cosmic Formula identity

`(a + b) ^ n = a * GN n a b + b ^ n`

produces another additive coprime triple.  This module packages that first
deterministic ABC–GN bridge without making any claim about ABC quality or
valuation excess.
-/

namespace DkMath.ABC

open DkMath.CosmicFormulaBinom

/--
Lift an ABC triple `a + b = c` along the `n`th-power Cosmic Formula identity.

The lifted coordinates are
`a * GN n a b`, `b ^ n`, and `c ^ n`.  This is valid for every natural
exponent, including `n = 0`.
-/
def Triple.gnPowerLift (T : Triple) (n : ℕ) : Triple where
  a := T.a * GN n T.a T.b
  b := T.b ^ n
  c := T.c ^ n
  hsum := by
    calc
      T.a * GN n T.a T.b + T.b ^ n = (T.a + T.b) ^ n := by
        symm
        exact cosmic_id_csr' n T.a T.b
      _ = T.c ^ n := by rw [T.hsum]
  hcop := by
    apply (Nat.coprime_add_self_left).1
    rw [← cosmic_id_csr' n T.a T.b, T.hsum]
    have hcb : Nat.Coprime T.c T.b := by
      rw [← T.hsum]
      exact (Nat.coprime_add_self_left).2 T.hcop
    exact Nat.Coprime.pow n n hcb

@[simp]
theorem Triple.gnPowerLift_a (T : Triple) (n : ℕ) :
    (T.gnPowerLift n).a = T.a * GN n T.a T.b :=
  rfl

@[simp]
theorem Triple.gnPowerLift_b (T : Triple) (n : ℕ) :
    (T.gnPowerLift n).b = T.b ^ n :=
  rfl

@[simp]
theorem Triple.gnPowerLift_c (T : Triple) (n : ℕ) :
    (T.gnPowerLift n).c = T.c ^ n :=
  rfl

/-- The additive equation underlying the GN power lift. -/
theorem Triple.gnPowerLift_sum (T : Triple) (n : ℕ) :
    T.a * GN n T.a T.b + T.b ^ n = T.c ^ n :=
  (T.gnPowerLift n).hsum

/-- The lifted left coordinate is coprime to the lifted right coordinate. -/
theorem Triple.gnPowerLift_coprime (T : Triple) (n : ℕ) :
    Nat.Coprime (T.a * GN n T.a T.b) (T.b ^ n) :=
  (T.gnPowerLift n).hcop

end DkMath.ABC
