/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

-- cid: 697d62b5-312c-83a8-a917-f4aca8fa80ca

import DkMath.Algebra.DiffPow
import DkMath.NumberTheory.GdcDivD
import DkMath.NumberTheory.GcdNext

set_option linter.style.longLine false
set_option linter.style.multiGoal false

namespace DkMath

open DkMath.NumberTheory
open DkMath.Algebra
open DkMath.CosmicFormulaBinom

set_option linter.unusedTactic false in
/-- Fermat's Last Theorem (FLT)
Cosmic Formula を用いた新しい証明
$$
\Large
z^n = x\ G + y^n\\[16pt]
\normalsize
x^n = x\ G, \quad y^n = u^d, \quad z^n = (x+u)^d\\[4pt]
x^{n-1} = G_{d-1}(x,u) = \frac{(x+u)^d - u^d}{x}\\[16pt]
G_{d-1}(x,u) = \sum_{k=0}^{d-1} \binom{d}{k+1} x^k\ u^{d-1-k}
$$
-/
theorem FLT
  {x y z : ℕ} (n : ℕ)
  (hpos_xyz : 0 < x ∧ 0 < y ∧ 0 < z)
  (hn : 3 ≤ n)
  (hxy : x ^ n + y ^ n = z ^ n) : False := by

  let body : x ^ n = BodyN n x y
  let gap : y ^ n = GapN n y

  have p2p : x ^ n = x * x + 2 * x * y := by
    ring_nf
    have : n = 2 := by
      sorry
    try done
    sorry

  have big : z ^ n = BigN n x y := by
    refine Eq.symm (Nat.sub_one_cancel ?_ ?_ ?_)
    · -- 0 < BigN n x y
      apply Nat.pow_pos
      cases z
      · -- 0 < x + y
        refine Nat.add_pos_iff_pos_or_pos.mpr ?_
        cases hpos_xyz with
        | intro hx hy =>
          left; exact hx
      · -- 0 < z ^ n
        refine Nat.add_pos_right x ?_
        exact (hpos_xyz.right.left)
    · -- 0 < z ^ n
      apply Nat.pow_pos
      exact (hpos_xyz.right.right)
    · -- ⊢ BigN n x y - 1 = z ^ n - 1
      rw [BigN]
      sorry
    done
  · exact rfl
  · -- x ^ n = BodyN n x y
    sorry
  -- False
  obtain ⟨left, right⟩ := hpos_xyz
  obtain ⟨left_1, right⟩ := right
  sorry

end DkMath
