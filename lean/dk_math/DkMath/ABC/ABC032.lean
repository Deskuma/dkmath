/-
Copyright (c) 2025 D. and Wise Wolf. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/


import DkMath.ABC.ABC031

#print "file: DkMath.ABC.ABC032"

set_option linter.style.longLine false
set_option linter.style.emptyLine false

/- Note:
※細分化前にエラー／警告を出さない補題・定理ファイル。
  ABC.lean で定義されるべき定理のうち、ABC.lean 内で定義されていた定理をここに移動している。
-/

namespace ABC

open scoped BigOperators

open Nat Real Rat Filter Finset
open MeasureTheory ProbabilityTheory

-- ------------------------------------------------------------------------------------------------------------------------------------

/- 有限例外を吸収して K_ε を構成し abc_main を示す（スケッチ） -/
/--
ε > 0 に対して与えられる実数の定数 K_ε を返す非計算的定義。
本定義は補助的な上界や定数として後続の議論で用いることを想定しており、
ε に依存する正の定数を一つ固定するための場所取り (placeholder) である。

実装上は `X0 = 1` のような仮の値を用い、最終的な議論では「密度 1 の集合から非構成的に取り出した点 X0」
などを用いることを想定している（そのため `noncomputable` としている）。
現在は具体値 2 を返すが、これはあくまで占有的な定数であり、証明の都合に応じて変更され得ることを明記する。

引数 hε は ε > 0 を記述するために受け取る仮引数であり、定義自体の正当性（正の ε を想定していること）を
明示するために用いる。
-/
noncomputable def K_eps (ε : ℝ) (hε : 0 < ε) : ℝ :=
  let X0 := 1 -- placeholder: 実際は密度1 から取り出す非構成的な X0
  let _ := X0
  let _ := hε
  2


/- ABC予想: K_ε の性質 -/

/-
Reduce the global ABC statement to the project-scoped skeleton axioms (dyadic/midband
bounds, adjK density and grid density). The final analytic/combinatorial derivation is
intentionally left as a skeleton admission here: the heavy estimates will be supplied by
replacing the corresponding `Block_Janson_*` / `Block_Suen_*` skeletons with concrete
proofs in subsequent work.
---
大域的ABCステートメントを、プロジェクトスコープのスケルトン公理（二項/ミッドバンド境界、
adjK密度、グリッド密度）に縮約する。最終的な解析的/組合せ的導出は、ここでは意図的に
スケルトンとして残されている。詳細な推定は、対応する「Block_Janson_*」/「Block_Suen_*」
スケルトンを後続の作業で具体的な証明に置き換えることで提供される。
-/

/- Project-scoped axiom: placeholder for the final abc_main theorem. -/
/--
ε > 0 に対してある定数 K ≥ 1 が存在し、任意の自然数 a, b, c に対して
a + b = c かつ Nat.Coprime a b（a と b が互いに素）であれば
(c : ℝ) ≤ K * (rad (a * b * c) : ℝ) ^ (1 + ε) が成り立つ、という公理的主張。

ここで rad(n) は n の素因数の積（「radical」）を表し、Nat.Coprime は最大公約数が 1 であることを示す。
K は ε にのみ依存し、a,b,c によらず同じ値を使える点に注意する。
実際の不等式は実数への自然数のキャストを用いて書かれている。

この仮定は ABC 予想に対応する形式的な主張であり、証明ではなく公理として採用されている。
もし成り立てば、多くのディオファントス方程式や累乗に関する有限性の結論など、
ABC 予想がもたらす標準的な帰結を導くことができる。
-/
axiom abc_main_axiom :
  ∀ (ε : ℝ), 0 < ε →
    ∃ K : ℝ, (1 : ℝ) ≤ K ∧ ∀ (a b c : ℕ), a + b = c → Nat.Coprime a b →
      (c : ℝ) ≤ K * (rad (a * b * c) : ℝ) ^ (1 + ε)


/--
ε > 0 の任意の実数に対して、ある実数 K ≥ 1 が存在し、以下が成り立つことを主張する定理。
任意の自然数 a, b, c に対して a + b = c かつ a と b が互いに素であれば，
実数として見た c は K * (rad (a * b * c))^(1 + ε) 以下である。
ここで rad(n) は n の異なる素因数の積（素因数の積で平方冪を除いたもの）を表し，
(c : ℝ) などは自然数の実数への埋め込みを意味する。
定数 K は ε に依存するが明示的に与えられるわけではなく，存在性のみが主張されている。

（`abc_main_axiom` に基づく仮定的定理）

この主張はいわゆる abc 予想の形を取った主張であり，
任意の正の ε に対して冪 1+ε の形で c を rad(abc) の冪で上から抑えるという性質を述べている。
-/
theorem abc_main (ε : ℝ) (hε : 0 < ε) :
  ∃ K : ℝ, (1 : ℝ) ≤ K ∧ ∀ (a b c : ℕ), a + b = c → Nat.Coprime a b →
    (c : ℝ) ≤ K * (rad (a * b * c) : ℝ) ^ (1 + ε) :=
  abc_main_axiom ε hε

end ABC
