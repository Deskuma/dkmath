/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.ABC.Basic
import DkMath.ABC.PadicValNat
import DkMath.ABC.Rad
import DkMath.ABC.RpowExtras
import DkMath.ABC.Square
import DkMath.Basic.Nat

#print "file: DkMath.ABC.Core"

set_option linter.style.longLine false
set_option linter.style.emptyLine false
set_option linter.style.whitespace false

-- `RpowExtras` は `DkMath.ABC.RpowExtras` に切り出した (2026/04/21)。

-- ------------------------------------------------------------------------------------------------------------------------------------

namespace DkMath.ABC

export DkMath.Basic.Nat (succ_sub_self dvd_one_iff gcd_succ coprime_succ)

open scoped BigOperators

open Nat Real Rat Filter Finset
open MeasureTheory ProbabilityTheory

-- Auxiliary lemma: 3^(X+1) ≥ 2X+1 for all X (帰納法で証明)
lemma three_pow_ge_linear (X : ℕ) : 3 ^ (X + 1) ≥ 2 * X + 1 := by
  induction X with
  | zero =>
      norm_num
  | succ n ih =>
      -- 3^(n+2) = 3 * 3^(n+1) ≥ 3 * (2n+1) = 6n+3 ≥ 2(n+1)+1
      have : (3 : ℕ) ^ (n + 2) = 3 * 3 ^ (n + 1) := by
        rw [Nat.pow_succ]; ring
      calc
        3 ^ (n + 2)
            = 3 * 3 ^ (n + 1) := this
        _ ≥ 3 * (2 * n + 1) := Nat.mul_le_mul_left _ ih
        _ = 6 * n + 3 := by ring
        _ ≥ 2 * (n + 1) + 1 := by omega

-- valuation の基本補題は `DkMath.ABC.PadicValNat` に集約した (2026/04/21)。

/- ============================================================================
     0. Basic helpers & notations
   ============================================================================ -/

-- squarefree / squarefull の定義は `DkMath.ABC.Square` に集約した (2026/04/21)。

/- ============================================================================
     1. gcd / coprimality lemmas
   ============================================================================ -/

-- gcd / coprimality の基本補題は `DkMath.Basic.Nat` に集約した (2026/04/21)。

/- ============================================================================
     2. rad: definition + basic facts
   ============================================================================ -/

-- `DkMath.ABC.Rad` に `rad` 定義補題を移動した (2026/04/20 17:35)

-- radical kernel の補題群は `DkMath.ABC.Rad` に集約した (2026/04/20)。

/- ============================================================================
     3. squarefree / squarefull controls
   ============================================================================ -/

-- squarefree / squarefull controls の定義 owner は `DkMath.ABC.Square` (2026/04/21)。

end DkMath.ABC

-- ------------------------------------------------------------------------------------------------------------------------------------
