/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Basic
import DkMath.CosmicFormula.CosmicFormulaBinom
-- import Mathlib
-- import Mathlib.NumberTheory.Padics.PadicVal.Basic

namespace DkMath

open Nat

/-- `p ∤ b` なら `v_p(a*b) = v_p(a)`（非ゼロ仮定つき） -/
lemma padicValNat_mul_eq_left
    {p a b : ℕ} [Fact (Nat.Prime p)]
    (ha : a ≠ 0) (hb : b ≠ 0) (hpb : ¬ p ∣ b) :
    padicValNat p (a * b) = padicValNat p a := by
  have hb0 : padicValNat p b = 0 := by
    exact padicValNat.eq_zero_of_not_dvd (p := p) (n := b) hpb
  -- padicValNat.mul : v_p(a*b) = v_p(a) + v_p(b)
  calc
    padicValNat p (a * b)
        = padicValNat p a + padicValNat p b := by
            simpa using (padicValNat.mul (p := p) (a := a) (b := b) ha hb)
    _ = padicValNat p a := by simp [hb0]

/-- 指数整合の破綻（最小版）：
`x^d = u*G` で、ある素数 `p` が `u` にちょうど 1 回だけ現れ（`v_p(u)=1`）、
しかも `p ∤ G` なら、`d ≥ 2` の下で矛盾。 -/
lemma exponent_alignment_failure_of_val_eq_one
    {p x u G d : ℕ}
    (hp : Nat.Prime p)
    (hd : 2 ≤ d)
    (hx : x ≠ 0)
    (hu0 : u ≠ 0)
    (hG0 : G ≠ 0)
    (hu : padicValNat p u = 1)
    (hG : ¬ p ∣ G)
    (h : x ^ d = u * G) : False := by
  -- `padicValNat.*` の補題は `[Fact (Nat.Prime p)]` を要求する
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  -- 左：v_p(x^d) = d * v_p(x)
  have hpow : padicValNat p (x ^ d) = d * padicValNat p x := by
    simpa using (padicValNat.pow (p := p) (a := x) d hx)
  -- よって d | v_p(x^d)
  have hdvd_left : d ∣ padicValNat p (x ^ d) := by
    -- d | d * (v_p x)
    simp [hpow, Nat.dvd_mul_right d (padicValNat p x)]
  -- 右：x^d = u*G で書き換え
  have hdvd_right : d ∣ padicValNat p (u * G) := by
    simpa [h] using hdvd_left
  -- p ∤ G なので v_p(u*G) = v_p(u)
  have hval_right : padicValNat p (u * G) = padicValNat p u :=
    padicValNat_mul_eq_left (p := p) (a := u) (b := G) hu0 hG0 hG
  -- 結局 d | v_p(u) = 1
  have : d ∣ padicValNat p u := by
    simpa [hval_right] using hdvd_right
  have : d ∣ 1 := by
    simpa [hu] using this
  -- しかし d ≥ 2 なので d ∤ 1（= d=1 が必要）で矛盾
  have hd' : 1 < d := lt_of_lt_of_le (by decide : 1 < 2) hd
  have : d = 1 := Nat.dvd_one.mp this
  exact (Nat.ne_of_gt hd') this

end DkMath
