/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Kummer.GapDivisibleBranch

#print "file: DkMath.FLT.Kummer.CyclotomicPrincipalization"

set_option linter.style.longLine false
set_option linter.style.emptyLine false

open DkMath.CosmicFormulaBinom

/-!
# Cyclotomic Principalization Target

## 数学的背景

Z[ζ_p] における ideal factorization:
  x^p + y^p = ∏_{j=0}^{p-1} (x + ζ^j · y)

各因子 (x + ζ^j · y) が生成する ideal は、
class group の p-torsion が trivial なら principal ideal の p 乗になる。
Principal ideal の p 乗性が保証されると、
整数 z' with z'^p = (x/q)^p + y^p の存在が導ける。

これが Kummer の「第一場合」の降下法の核心。

## 抽象化の方針

1. `CyclotomicPrincipalizationTarget`: principalization が成り立つと仮定
2. `CyclotomicClassGroupPTorsionFreeTarget`: class group の p-torsion が trivial と仮定
3. 第 2 から第 1 への bridge（abstract theorem）
4. 第 1 から GapDivisibleBranch への bridge（abstract theorem）

これにより、class group の concrete 構造に立ち入らずに、
Kummer 語彙を DkMath 幹線に接続できる。
-/

namespace DkMath.FLT

/-!
## §1. Cyclotomic Principalization Target

Kummer 的 principalization: 反例 pack + q|x + q≠p + q|(z-y) のとき
descent existence (∃ g') が成り立つ。

数学的には: Z[ζ_p] で ideal (x + ζ^j · y) の構造解析 +
class group の p-torsion = 0 + unit group の剰余類解析 から
整数 p 乗根の存在を導く。

ここでは内容は空で、statement だけ置く。
GapDivisibleBranchTarget と同じ statement だが、
「Kummer principalization という数学的根拠で正当化される」と読む。
-/

/--
Kummer principalization により gap-divisible branch の descent existence を保証する。

数学的根拠:
- Z[ζ_p] で x + ζ^j · y の ideal factorization
- class group p-torsion = 0 → principal ideal p 乗性
- unit group の Kummer 単数定理
-/
abbrev CyclotomicPrincipalizationTarget : Prop :=
  ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
    ∀ {q : ℕ}, Nat.Prime q →
      q ∣ x →
      q ≠ p →
      q ∣ (z - y) →
      ∃ g' : ℕ, g' * GN p g' y = (x / q) ^ p

/--
Principalization → GapDivisibleBranch（statement 同一なので自明）。
-/
theorem qAdicGapReductionGapDivisible_of_cyclotomicPrincipalization
    (hKummer : CyclotomicPrincipalizationTarget) :
    PrimeGe5BranchAPrimitiveQAdicGapReductionGapDivisibleBranchTarget :=
  hKummer

/-!
## §2. Cyclotomic Class Group p-Torsion Free Target

class group の p-torsion が trivial という仮定の器。
p が regular prime（p ∤ h_p^-）のとき成り立つ。

最初は Prop の器だけ置く。後で concrete 意味を詰める。
-/

/--
ℤ[ζ_p] の class group p-torsion が trivial: `Cl(ℚ(ζ_p))[p] = 0`。

正確には、p が Bernoulli 数 B_{2k} (k = 1,...,(p-3)/2) を
いずれも割らない（= p は regular prime）ことと同値。

ここでは abstract Prop として置き、concrete 意味は後で詰める。
`hpack` の `p` に対する条件。
-/
abbrev CyclotomicClassGroupPTorsionFreeTarget : Prop :=
  ∀ {p : ℕ}, Nat.Prime p → 5 ≤ p → True
  -- TODO: concrete meaning を詰める。
  -- 最終的には `∀ α ∈ Cl(ℚ(ζ_p)), α^p = 1 → α = 1`
  -- あるいは `p ∤ h_p^-` (Kummer regularity) の形になる。

/--
Class group p-torsion free → Principalization（abstract bridge）。

数学的根拠は Kummer の第一場合の証明:
1. class group p-torsion = 0
2. → ideal (x + ζ^j · y) は principal ideal の p 乗
3. → norm 計算で z'^p = (x/q)^p + y^p の解 z' が整数として存在

現時点では sorry: class group 理論の formal 化が必要。
-/
theorem cyclotomicPrincipalization_of_classGroupPTorsionFree
    (hCl : CyclotomicClassGroupPTorsionFreeTarget) :
    CyclotomicPrincipalizationTarget := by
  sorry

/-!
## §3. ClassGroupBridge と RegularPrime route

Regular prime (p ∤ h_p^-) → ClassGroupPTorsionFree は定義同値になる予定。
ここでは forward reference を避け、別ファイルに分離する。
-/

end DkMath.FLT
