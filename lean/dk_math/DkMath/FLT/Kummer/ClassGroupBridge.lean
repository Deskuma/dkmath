/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Kummer.CyclotomicPrincipalization

#print "file: DkMath.FLT.Kummer.ClassGroupBridge"

set_option linter.style.longLine false
set_option linter.style.emptyLine false

/-!
# Class Group Bridge

## 目的

`CyclotomicClassGroupPTorsionFreeTarget` から
`CyclotomicPrincipalizationTarget` への橋を明示的に固定する。

現時点では `cyclotomicPrincipalization_of_classGroupPTorsionFree` が
CyclotomicPrincipalization.lean に直接置かれている（sorry）。

このファイルは将来的に:
- Regular prime の定義（p ∤ h_p^-）
- Bernoulli 数の p-divisibility
- Class number formula との接続
を配置するための receiver として機能する。

## 設計

```
Regular prime condition
  ↓ (定義同値)
ClassGroupPTorsionFree
  ↓ cyclotomicPrincipalization_of_classGroupPTorsionFree
CyclotomicPrincipalization
  ↓ qAdicGapReductionGapDivisible_of_cyclotomicPrincipalization
GapDivisibleBranch
```
-/

namespace DkMath.FLT

/-!
## §1. Regular prime の placeholder

p が regular prime: p ∤ class number h_p の条件。
等価形は「p が B_{2k} (k = 1,...,(p-3)/2) のいずれも割らない」。
-/

/--
Regular prime 条件の placeholder。
正式には「p ∤ h_p^-」または等価な Bernoulli 数条件。
-/
abbrev IsRegularPrime (_p : ℕ) : Prop := True
  -- TODO: 正式な定義に置き換える。
  -- Bernoulli 数の p-divisibility check
  -- Mathlib の `NumberField.classNumber` と接続

/--
Regular prime → ClassGroupPTorsionFree（定義同値の予定）。
-/
theorem classGroupPTorsionFree_of_regularPrime
    (_h : ∀ {p : ℕ}, Nat.Prime p → 5 ≤ p → IsRegularPrime p) :
    CyclotomicClassGroupPTorsionFreeTarget := by
  intro p _hp _h5
  trivial

/-!
## §2. Full chain: Regular prime → Principalization → GapDivisible

上の要素を単に合成。
-/

/--
Regular prime assumption から gap-divisible branch が閉じる。
-/
theorem qAdicGapReductionGapDivisible_of_regularPrime
    (hReg : ∀ {p : ℕ}, Nat.Prime p → 5 ≤ p → IsRegularPrime p) :
    PrimeGe5BranchAPrimitiveQAdicGapReductionGapDivisibleBranchTarget :=
  qAdicGapReductionGapDivisible_of_cyclotomicPrincipalization
    (cyclotomicPrincipalization_of_classGroupPTorsionFree
      (classGroupPTorsionFree_of_regularPrime hReg))

end DkMath.FLT
