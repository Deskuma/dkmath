/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.CosmicFormula.CosmicFormulaBinom
import DkMath.FLT.PetalDetect
import DkMath.NumberTheory.ZsigmondyCyclotomic
import DkMath.Zsigmondy

namespace DkMath.FLT

open DkMath.CosmicFormulaBinom
open DkMath.FLT.PetalDetect
open DkMath.NumberTheory.GcdNext

/--
Cosmic Formula（無減算形）から、減算形
`(x+u)^d - u^d = x * GN d x u` を得る。
-/
lemma sub_eq_mul_GN (d x u : ℕ) :
    (x + u) ^ d - u ^ d = x * GN d x u := by
  have hbig : (x + u) ^ d = x * GN d x u + u ^ d := cosmic_id_csr' d x u
  have hpow : u ^ d ≤ (x + u) ^ d := by
    exact Nat.pow_le_pow_left (Nat.le_add_left u x) d
  omega

/--
差の冪版:
`z^d - y^d = (z-y) * GN d (z-y) y`。

`z < y` の場合も、Nat の切り捨て減算により両辺とも 0 になる。
-/
lemma sub_pow_eq_mul_GN (d z y : ℕ) :
    z ^ d - y ^ d = (z - y) * GN d (z - y) y := by
  by_cases hyz : y ≤ z
  · simpa [Nat.sub_add_cancel hyz] using sub_eq_mul_GN d (z - y) y
  · have hzy : z ≤ y := Nat.le_of_not_ge hyz
    have hpow : z ^ d ≤ y ^ d := Nat.pow_le_pow_left hzy d
    have hdiff0 : z ^ d - y ^ d = 0 := Nat.sub_eq_zero_of_le hpow
    have hgap0 : z - y = 0 := Nat.sub_eq_zero_of_le hzy
    simp [hdiff0, hgap0]

/--
`q ∣ ((x+u)^d - u^d)` かつ `q ∤ x` なら `q ∣ GN d x u`。
-/
lemma prime_dvd_GN_of_dvd_sub_not_dvd_left {d x u q : ℕ}
    (hq : Nat.Prime q)
    (hq_dvd : q ∣ (x + u) ^ d - u ^ d)
    (hq_ndvd : ¬ q ∣ x) :
    q ∣ GN d x u := by
  have hmul : q ∣ x * GN d x u := by
    simpa [sub_eq_mul_GN d x u] using hq_dvd
  exact (hq.dvd_mul.mp hmul).resolve_left hq_ndvd

/--
`d = 3` の場合、`prime_dvd_GN_of_dvd_sub_not_dvd_left` は
`DkMath.Zsigmondy` の Body -> GN bridge からも読める。
-/
lemma prime_dvd_GN_three_of_dvd_sub_not_dvd_left_via_zsigmondy {x u q : ℕ}
    (hx : 0 < x)
    (hq : Nat.Prime q)
    (hq_dvd : q ∣ (x + u) ^ 3 - u ^ 3)
    (hq_ndvd : ¬ q ∣ x) :
    q ∣ GN 3 x u := by
  have hq_dvd_body : q ∣ DkMath.Zsigmondy.BodyN x u 3 := by
    simpa [DkMath.Zsigmondy.BodyN] using hq_dvd
  simpa using
    (DkMath.Zsigmondy.prime_dvd_body_three_of_not_dvd_boundary_imp_dvd_GN
      (x := x) (u := u) hx hq hq_dvd_body hq_ndvd)

/--
`q ∣ (z^d - y^d)` かつ `q ∤ (z-y)` なら `q ∣ GN d (z-y) y`。
-/
lemma dvd_GN_of_dvd_sub_pow {d z y q : ℕ}
    (hq : Nat.Prime q)
    (hq_dvd : q ∣ z ^ d - y ^ d)
    (hq_ndvd : ¬ q ∣ (z - y)) :
    q ∣ GN d (z - y) y := by
  have hmul : q ∣ (z - y) * GN d (z - y) y := by
    simpa [sub_pow_eq_mul_GN d z y] using hq_dvd
  exact (hq.dvd_mul.mp hmul).resolve_left hq_ndvd

/--
`x = c-b`, `u = b` を代入した d=3 の橋:
`GN 3 (c-b) b = S0_nat c b`。
-/
/-
NOTE: 将来エラーで引っかかる可能性があるため、`GN 3 (c-b) b` を `S0_nat c b` に置き換えるのは避けるべきである。
参照先: prime_dvd_S0_via_cosmic_bridge

---

MathlibDemo.lean:530:36
Tactic state
1 goal
c b : ℕ
hbc : b < c
⊢ GN 3 (c - b) b = S0_nat c b
Messages (1)
MathlibDemo.lean:530:35

unsolved goals
c b : ℕ
hbc : b < c
⊢ ↑c * ↑b * Nat.rawCast 1 + ↑c ^ 2 + ↑b ^ 2 * Nat.rawCast 1 = ↑c * ↑b + ↑c ^ 2 + ↑b ^ 2

All Messages (2)
MathlibDemo.lean:17:0

DkMath.FLT.docs.StandAlone.FLT3#StandAlone-NC

MathlibDemo.lean:530:35

unsolved goals
c b : ℕ
hbc : b < c
⊢ ↑c * ↑b * Nat.rawCast 1 + ↑c ^ 2 + ↑b ^ 2 * Nat.rawCast 1 = ↑c * ↑b + ↑c ^ 2 + ↑b ^ 2
---
-/
lemma GN_three_sub_eq_S0_nat {c b : ℕ} (hbc : b < c) :
    GN 3 (c - b) b = S0_nat c b := by
  rw [GN_three_explicit (c - b) b]
  unfold S0_nat
  zify [hbc]
  ring_nf

/--
CosmicFormulaBinom -> Petal の接続補題:
`q ∣ c^3-b^3` かつ `q ∤ c-b` なら `q ∣ S0_nat c b`。
-/
lemma prime_dvd_S0_via_cosmic_bridge {c b q : ℕ}
    (hbc : b < c)
    (hq : Nat.Prime q)
    (hq_dvd : q ∣ c ^ 3 - b ^ 3)
    (hq_ndvd : ¬ q ∣ c - b) :
    q ∣ S0_nat c b := by
  have hgap_pos : 0 < c - b := Nat.sub_pos_of_lt hbc
  have hq_dvd_body : q ∣ DkMath.Zsigmondy.BodyN (c - b) b 3 := by
    simpa [DkMath.Zsigmondy.BodyN, Nat.sub_add_cancel hbc.le] using hq_dvd
  have hq_dvd_GN : q ∣ GN 3 (c - b) b := by
    simpa using
      (DkMath.Zsigmondy.prime_dvd_body_three_of_not_dvd_boundary_imp_dvd_GN
        (x := c - b) (u := b) hgap_pos hq hq_dvd_body hq_ndvd)
  have hGN_eq : GN 3 (c - b) b = S0_nat c b := GN_three_sub_eq_S0_nat hbc
  rw [hGN_eq] at hq_dvd_GN
  exact hq_dvd_GN

end DkMath.FLT
