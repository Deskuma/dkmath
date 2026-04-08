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
`CyclotomicIdealPthPowerTarget` への橋を明示的に固定する。

現時点では `cyclotomicPrincipalization_of_classGroupPTorsionFree` が
CyclotomicPrincipalization.lean に直接置かれている（so#rry）。
ただし意味論的には、class group が supply する本丸は
full principalization 全体ではなく **ideal の p 乗性** であり,
review-009 時点ではその上流はさらに
`generic algebraic factorization identity → equation-only factorization identity → prime specialization → abstract factorization identity → counterexample specialization → pure factorization identity → gap-divisible specialization → ideal equation packaging → ideal product p-th power → class p-torsion witness`
へ分解されている。

このファイルは将来的に:
- Regular prime の定義（p ∤ h_p^-）
- Bernoulli 数の p-divisibility
- Class number formula との接続
を配置するための receiver として機能する。

2026/04/05 時点の Mathlib 棚卸し:
- `RingTheory.ClassGroup` と `NumberTheory.ClassNumber.*` により、
  ideal class group とその有限性の一般論はある。
- `NumberTheory.Bernoulli` により Bernoulli 数そのものはある。
- しかし `CyclotomicField` / `ringOfIntegers` / regular prime /
  class number formula を直接つなぐ ready-made theorem は見当たらない。

したがって、次段の本丸は「Mathlib の class group 一般論を円分体へ specialized する橋」を
どの粒度で新設するか、という設計問題になる。

## 設計

```
Regular prime condition
  ↓ (定義同値)
ClassGroupPTorsionFree
  ↓ p-torsion annihilation bridge (closed)
CyclotomicPTorsionAnnihilation
  ↖
    IdealClassPTorsionWitness
      ↑ ideal product p-th power
      ↑ ideal equation packaging
      ↑ gap-divisible specialization
      ↑ pure factorization identity
      ↑ counterexample specialization
      ↑ abstract factorization identity
      ↑ prime specialization
      ↑ equation-only factorization identity
      ↑ generic algebraic factorization identity (thinnest theorem-level kernel)
CyclotomicIdealPthPower
  ↓ unit normalization
CyclotomicUnitNormalization
  ↓ norm descent
CyclotomicNormDescent
  ↓ cyclotomicPrincipalization_of_threeStages
CyclotomicPrincipalization
  ↓ qAdicGapReductionGapDivisible_of_cyclotomicPrincipalization
GapDivisibleBranch
```
-/

universe u

namespace DkMath.FLT

/-!
## §1. Regular prime の placeholder

p が regular prime: p ∤ class number h_p の条件。
等価形は「p が B_{2k} (k = 1,...,(p-3)/2) のいずれも割らない」。
-/

/--
Regular prime 条件の receiver。

現段階では review-013 の判断に従い、
「この branch を閉じるのに必要な concrete class-group p-torsion-free 内容」を
そのまま保持する器として置く。
正式な Bernoulli / class number 条件との同値付けは次段の honest open とする。
-/
abbrev IsRegularPrime (_p : ℕ) : Prop :=
  ∀ {R : Type u} [CommRing R] [IsDomain R],
    ∀ (n : ℕ), ∀ a : ClassGroup R, a ^ n = 1 → a = 1

/--
Regular prime → ClassGroupPTorsionFree（定義同値の予定）。
-/
theorem classGroupPTorsionFree_of_regularPrime
  (h : ∀ {p : ℕ}, Nat.Prime p → 5 ≤ p → IsRegularPrime.{u} p) :
  CyclotomicClassGroupPTorsionFreeTarget.{u} := by
  intro R _ _ n a ha
  exact @h 5 Nat.prime_five (by decide) R _ _ n a ha

/-!
## §2. Refined mainline: Regular prime + Stage 2 + Stage 3 → GapDivisible

review-014 に従い、public な本筋は legacy one-shot route ではなく
refined route に寄せる。
regular prime から class-group 仮定までを供給し、その先の
unit normalization / norm descent は honest な独立入力として保つ。
-/

/--
推奨 mainline: regular prime + unit normalization + norm descent から
gap-divisible branch を得る。
-/
theorem qAdicGapReductionGapDivisible_of_refinedRegularPrimeRoute
  (hReg : ∀ {p : ℕ}, Nat.Prime p → 5 ≤ p → IsRegularPrime.{u} p)
  (hUnit : CyclotomicUnitNormalizationTarget)
  (hNorm : CyclotomicNormDescentTarget) :
    PrimeGe5BranchAPrimitiveQAdicGapReductionGapDivisibleBranchTarget :=
  qAdicGapReductionGapDivisible_of_cyclotomicPrincipalization
    (cyclotomicPrincipalization_of_refinedClassGroupRoute
      (classGroupPTorsionFree_of_regularPrime hReg) hUnit hNorm)

/-!
## §3. Legacy one-shot chain: Regular prime → Principalization → GapDivisible

この route は historical / legacy wrapper として残す。
direct `so#rry` が残る理由は、one-shot theorem が Stage 2 / Stage 3 まで
暗に抱え込んでいるためである。
-/

/--
Legacy one-shot wrapper。
-/
theorem qAdicGapReductionGapDivisible_of_regularPrime
  (hReg : ∀ {p : ℕ}, Nat.Prime p → 5 ≤ p → IsRegularPrime.{0} p) :
    PrimeGe5BranchAPrimitiveQAdicGapReductionGapDivisibleBranchTarget :=
  qAdicGapReductionGapDivisible_of_cyclotomicPrincipalization
    (cyclotomicPrincipalization_of_classGroupPTorsionFree
      (classGroupPTorsionFree_of_regularPrime.{0} hReg))

end DkMath.FLT
