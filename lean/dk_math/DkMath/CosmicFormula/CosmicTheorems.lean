/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

-- import Mathlib
import DkMath.CosmicFormula.CosmicFormulaBinom  -- Cosmic Formula Binomial Expansion

namespace DkMath.CosmicFormula.CosmicTheorems

open DkMath.CosmicFormulaBinom

/-- BigN: 宇宙式の大きな単位部分
宇宙式の大きな単位部分を表す関数。引数は次の通り：
- x : 基本単位量
- u : ギャップ単位量
- d : 宇宙式の次元
-/
def BigN' (d x u : ℕ) : ℕ := BodyN d x u + GapN d u

def BodyN' (d x u : ℕ) : ℕ := BigN d x u - GapN d u

def GapN' (d x u : ℕ) : ℕ := BigN d x u - BodyN d x u

example {d x u} : BodyN' d x u = BodyN d x u := by
  simp [BodyN', cosmic_id_csr']

example {d x u} : GapN' d x u = GapN d u := by
  simp [GapN', cosmic_id_csr']

example {d x u} : BigN' d x u = BigN d x u := by
  simp [BigN', cosmic_id_csr']

lemma cid_csr_iff {N : Type _} [CommSemiring N] (d : ℕ) (x u : N) :
  (cosmic_id_csr' d x u) = (cosmic_id_csr d x u) := by simp

lemma cid_csr_iff' {R : Type _} [CommSemiring R] (d : ℕ) (x u : R) :
    (x + u) ^ d = x * GN d x u + u ^ d ↔ (x + u) ^ d = BodyN d x u + GapN d u := by
    simp [BodyN, GapN, GN]


def BodyN_finset (d x u : ℕ) : ℕ :=
  ∑ i ∈ Finset.range d, Nat.choose d i * x ^ i * u ^ (d - i)

-- ----------------------------------------------------------------------------

/-- pow_sub_pos  (a > b, p は素数 のとき 0 < a^p - b^p)
~~無次元単位宇宙式より、~~ 別にいらなかった。（TODO: これは別のところに移動）
a > b かつ p が素数のとき、a^p - b^p > 0 であることを示す定理。
戦略：
1. a > b より a^p > b^p （p ≠ 0 の場合）
2. したがって 0 < a^p - b^p
-/
theorem pow_sub_pos {a b : ℕ} {p : ℕ}
  (hp : Nat.Prime p) (ha : a > b) : 0 < a ^ p - b ^ p := by
  -- p が素数なら p ≠ 0
  have hp_ne_zero : p ≠ 0 := Nat.Prime.ne_zero hp
  -- a > b より a^p > b^p
  have han : a ^ p > b ^ p := Nat.pow_lt_pow_left ha hp_ne_zero
  -- したがって 0 < a^p - b^p
  omega


end DkMath.CosmicFormula.CosmicTheorems
