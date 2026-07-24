# ABC–GN M1: Odd-Prime Exponent Exceptional Excess

作成日: 2026-07-25  
Status: **WIP / campaign initialized**

Repository: `Deskuma/dkmath`  
Base branch: `feature/ABC-GN-valuation-excess-260724-v0`  
Work branch: `wip/ABC-GN-M1-odd-p-exp-exceptional-excess-260725-v0`

## 1. Mission

ABC–GN deterministic spine が残した三つの一様予算のうち、第一魔核 M1 を討伐する。

```text
M1  uniform exponent-exceptional valuation excess
M2  uniform lifted-radical support growth
M3  uniform non-exceptional valuation excess
```

本プロジェクトの目標は、指数を奇素数 `p` に固定したとき、指数例外 prime channel の valuation excess が完全に消えることを Lean で証明することである。

最終目標は、正の ABC triple `T` と奇素数 `p` に対して次を得ること。

$$GNExceptionalValuationExcess\ p\ T.a\ T.b=0$$

その結果、既存の exceptional affine budget を係数・定数ともにゼロで供給する。

```lean
GNExceptionalExcessBudgetAffine T p 0 0
```

すなわち、最終 budget contract の第一成分を

```text
τe = 0
De = 0
```

へ固定する。

## 2. Existing deterministic spine

基底ブランチには、次の構造が既に実装されている。

```text
DkMath/ABC/GNExceptionalSplit.lean
  Triple.gcd_boundary_GN_dvd_exp
  Triple.dvd_exp_of_dvd_boundary_of_dvd_GN
  Triple.not_dvd_boundary_of_not_dvd_exp_of_dvd_GN

DkMath/ABC/GNValuationExcess.lean
  GNExceptionalValuationExcess
  GNNonExceptionalValuationExcess
  GNValuationExcess_eq_exceptional_add_nonExceptional

DkMath/ABC/GNFinalBudgetBridge.lean
  GNExceptionalExcessBudgetAffine
  GNNonExceptionalExcessBudgetAffine
  GNValuationExcessBudgetAffine.of_split
  ABCGNFinalBudgetContract
```

現在の `GNExceptionalValuationExcess p a b` は、`GN p a b` の factorization support のうち `q ∣ p` を満たす prime `q` に対し、

$$\bigl(v_q(GN_p(a,b))-1\bigr)\log q$$

を合計する。

`p` が素数なら、例外 support は `q = p` の一箇所に潰れる。したがって M1 の核心は、`p` が GN に現れた場合の valuation が正確に一であることを示す点にある。

## 3. Mathematical target

`T : Triple`、`p : ℕ` とし、

```text
Nat.Prime p
2 < p
0 < T.a
0 < T.b
```

を仮定する。

攻略核は次の連鎖である。

```text
p ∣ GN p T.a T.b
  -> p ∣ T.a
  -> p ∤ T.b                  by T.hcop
  -> ¬ p^2 ∣ GN p T.a T.b
  -> padicValNat p (GN p T.a T.b) = 1
  -> factorization multiplicity = 1
  -> exceptional summand = 0
  -> GNExceptionalValuationExcess p T.a T.b = 0
```

一般奇素数 proof では、次のいずれかを採用する。

1. binomial expansion modulo `p^2`;
2. LTE on `(T.a + T.b)^p - T.b^p`, followed by the exact GN product split;
3. existing Mathlib / DkMath valuation lemmas capable of expressing the same local statement.

実装では、最小依存・最小 theorem surface を優先する。

## 4. Two-stage assault

### Stage A: exponent five reconnaissance

まず `p = 5` を固定し、既存の GN5 観測と同じ算術を一般 `GN` 座標上で再現する。

目標:

```lean
Triple.GNExceptionalValuationExcess_five_eq_zero
```

この checkpoint は、一般化 API を先に設計しすぎず、exceptional support sum を実際にゼロへ落とせることを確認する。

ただし production ABC module から `DkMath.FLT.Five.*` を import しない。必要な恒等式は一般 GN 側で証明するか、適切な NumberTheory / CosmicFormula 層へ置く。

### Stage B: odd-prime exponent theorem

Stage A の局所構造を奇素数 `p` へ一般化する。

主目標:

```lean
Triple.GNExceptionalValuationExcess_eq_zero_of_oddPrime
```

続いて budget wrapper を供給する。

```lean
Triple.GNExceptionalExcessBudgetAffine_zero_of_oddPrime
```

## 5. Planned implementation surface

第一候補:

```text
DkMath/ABC/GNOddPrimeExceptionalExcess.lean
```

必要に応じて補助層を分離する。

```text
DkMath/NumberTheory/GN/OddPrimeExceptional.lean
DkMath/ABC/GNOddPrimeExceptionalExcess.lean
```

配置原則:

```text
一般 GN の合同・valuation 定理
  -> NumberTheory / CosmicFormulaBinom

ABC Triple wrapper と budget bridge
  -> DkMath.ABC
```

## 6. Completion criteria

M1 完了条件は次のすべて。

```text
1. odd-prime exponent の exceptional support が singleton 以下へ潰れる
2. support 上の exceptional valuation が exact 1 と証明される
3. GNExceptionalValuationExcess = 0 が閉じる
4. GNExceptionalExcessBudgetAffine T p 0 0 が得られる
5. 既存 split budget に無損失で接続される
6. focused build が通る
7. representative endpoint の axiom audit に新規 project axiom がない
```

## 7. Scope boundary

本プロジェクトは次を主張しない。

```text
ABC conjecture is proved
M2 support-growth budget is solved
M3 non-exceptional high-lift budget is solved
GN is generally squarefree
all composite exponents have zero exceptional excess
all prime exponents including p = 2 are covered
```

また、次を行わない。

```text
no modification of abc_main_axiom
no FLT7 dependency
no unrelated refactor
no new axiom
no sorry
no native_decide proof
```

## 8. Documents

```text
README.md
ABC-GN-M1-IMPLEMENTATION-DESIGN.md
ABC-GN-M1-ROADMAP.md
```

読む順序:

```text
README.md
  -> ABC-GN-M1-IMPLEMENTATION-DESIGN.md
  -> ABC-GN-M1-ROADMAP.md
```

## 9. Campaign doctrine

M1 は三予算のうち、指数を奇素数へ固定することで局所算術へ圧縮できる魔核である。

```text
exceptional support width = at most one prime p
exceptional multiplicity = exactly one copy
exceptional excess = zero
```

ここを確実に閉じ、残る戦線を M2 と M3 の二体へ縮退させる。