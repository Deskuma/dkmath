/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.PrimeProvider.TriominoCosmicPrimeGe5Core
import DkMath.FLT.Basic

set_option linter.style.longLine false
set_option linter.style.emptyLine false

namespace DkMath.FLT

/-- `p ≥ 5` の素数指数に対する FLT 供給。 -/
theorem FLT_prime_ge5 (p : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p) :
    FermatLastTheoremFor p := by
  intro a b c ha hb hc hEq
  have _hp_pos : 0 < p := hp.pos
  have hpos : 0 < a ∧ 0 < b ∧ 0 < c :=
    ⟨Nat.pos_of_ne_zero ha, Nat.pos_of_ne_zero hb, Nat.pos_of_ne_zero hc⟩
  have hp3 : 3 ≤ p := le_trans (by decide : 3 ≤ 5) hp5
  exact DkMath.FLT (x := a) (y := b) (z := c) p hpos hp3 hEq

#print axioms FLT_prime_ge5  -- NG so#rryAx connection root

end DkMath.FLT
