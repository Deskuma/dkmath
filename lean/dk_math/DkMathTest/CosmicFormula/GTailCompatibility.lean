/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.CosmicFormula.CosmicFormulaBinom
import DkMath.Lib.Cosmic.GTail

#print "file: DkMathTest.CosmicFormula.GTailCompatibility"

open scoped BigOperators

namespace DkMathTest.CosmicFormula

open DkMath.CosmicFormula

example (d : ℕ) (x u : ℚ) :
    (x + u) ^ d = x * GTail d 1 x u + u ^ d := by
  exact add_pow_eq_mul_GTail_one_add_gap d x u

example (d : ℕ) (x u : ℚ) :
    DkMath.CosmicFormulaBinom.GN d x u = DkMath.CosmicFormula.GN d x u := by
  rfl

example (d : ℕ) (x u : ℚ) :
    DkMath.CosmicFormulaBinom.GN d x u =
      ∑ k ∈ Finset.range d, (Nat.choose d (k + 1) : ℚ) * x ^ k * u ^ (d - 1 - k) := by
  exact DkMath.CosmicFormulaBinom.GN_eq_sum d x u

example (d : ℕ) (x u : ℚ) :
    (x + u) ^ d = x * DkMath.CosmicFormulaBinom.GN d x u + u ^ d := by
  exact DkMath.CosmicFormulaBinom.cosmic_id_csr' d x u

example (x u : ℚ) :
    GTail 3 1 x u =
      (Nat.choose 3 1 : ℚ) * u ^ (3 - 1) + x * GTail 3 2 x u := by
  exact Gbinom_tail_rec 3 x u (by norm_num)

example (u : ℚ) :
    GTail 3 1 0 u = (Nat.choose 3 1 : ℚ) * u ^ (3 - 1) := by
  exact Gbinom_zero_eval 3 u

end DkMathTest.CosmicFormula
