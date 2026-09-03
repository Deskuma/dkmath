/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.Tactic

namespace DkMath.Sample
namespace CosmicFormula

/-! # 宇宙式 Cosmic Formula
恒等式 $N+1=(P+1)^2$ の証明
-/

-- 定義

/-- $P(x) = x$
受け取った値をそのまま返す.
$P$ 成分は素スケールゲージの積の結果である.
素数積構造と名付け呼称する.
-/
def P (x : ℕ) : ℕ := x

/-- $N(x) = P(x)*(P(x)+2)$
宇宙式において $P$ に対応する $N$ 成分.
素数積構造との関係は後続の定理で扱う.
-/
def N (x : ℕ) : ℕ := P x * (P x + 2)

/-- N'(x) = P(x) ^ 2 + P(x) * 2 -/
def N' (x : ℕ) : ℕ := P x ^ 2 + P x * 2

/- 素数積構造により得られる自然数の上限の解説 -/
#eval N  30   -- `960` は 素数積構造 `P={2,3,5}=2*3*5=30` によって得られる最大の自然数となる.
/-
自然数 `961` を得るには素数積 `P={31}=31^2=961` が必要であり `P={2,3,5}` では得られない事が分かる.
-/

#eval P  123  -- x = 123
#eval N  123  -- 15375 = 123 * (123 + 2) = 123 * 125
#eval N' 123  -- 15375 = 123 ^ 2 + 123 * 2 = 15129 + 246

#eval N  12  -- 168 = 12 * (12 + 2) = 12 * 14
#eval N' 12  -- 168 = 12 ^ 2 + 12 * 2 = 144 + 24

/-
(x+1)^2 - x(x + 2) = 1
-/

abbrev P2 (x : ℕ) : ℕ := (P x + 1) ^ 2
abbrev N2 (x : ℕ) := N x
abbrev N2' (x : ℕ) := N' x
def P2_sub_N2 (x : ℕ) : ℕ := P2 x - N2 x
def P2_sub_N2' (x : ℕ) : ℕ := P2 x - N2' x

#eval P2 123  -- 15376 = (123 + 1) ^ 2 = 124 ^ 2
#eval N2 123  -- 15375 = 123 * (123 + 2) = 123 * 125
#eval P2_sub_N2  123  -- 1 = 15376 - 15375
#eval P2_sub_N2' 123  -- 1 = 15376 - 15375

/-
(x+1)^3 - (x^3 + 3 * x^2 + 3 * x) = 1
-/

def P3 (x : ℕ) : ℕ := (P x + 1) ^ 3
def N3 (x : ℕ) : ℕ := P x ^ 3 + 3 * P x ^ 2 + 3 * P x
def P3_sub_N3 (x : ℕ) : ℕ := P3 x - N3 x

#eval P3 123  -- 1906624 = (123 + 1) ^ 3 = 124 ^ 3
#eval N3 123  -- 1906623 = 123 ^ 3 + 3 * 123 ^ 2 + 3 * 123
#eval P3_sub_N3 123  -- 1 = 1906624 - 1906623

-- 整数
def PZ (x : ℤ) : ℤ := x
def NZ (x : ℤ) : ℤ := PZ x * (PZ x + 2)
def NZ' (x : ℤ) : ℤ := PZ x ^ 2 + PZ x * 2

-- 複素数
def PC (x : ℂ) : ℂ := x
def NC (x : ℂ) : ℂ := PC x * (PC x + 2)
def NC' (x : ℂ) : ℂ := PC x ^ 2 + PC x * 2

-- 実数
def PR (x : ℝ) : ℝ := x
def NR (x : ℝ) : ℝ := PR x * (PR x + 2)
def NR' (x : ℝ) : ℝ := PR x ^ 2 + PR x * 2

end CosmicFormula
end DkMath.Sample
