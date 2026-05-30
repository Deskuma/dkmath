# roadmap: DKMK-009

DKMK-009 は、DKMK-007/008 で整えた hitting route と descent path route を、
既存の `CapacityKernel` 層へ明示的に戻す章である。

DKMK-007 では、log-capacity shadow を primitive hitting bound へ載せる
mass / hitting route が整った。
DKMK-008 では、その chain 側を one-step divisor descent から
multi-step `AdjacentDivisorPathFamily`、さらに witness-derived
quotient path family へ拡張した。

次の DKMK-009 では、新しい path を増やすのではなく、

```text
capacity kernel
  → normalized sub-probability
  → SubMarkovShadow
  → primitive weightedHitMass bound
```

という核の流れを theorem-facing API として固定する。

重要なのは、`CapacityKernel` 自体はすでに存在していることだ。
したがって DKMK-009 の主目的は、新しい抽象を大きく発明することではない。
既存の kernel / shadow / hitting 層を、DKMK route の本線として束ね直すことにある。

## 1. 現在ある kernel 層

現時点で、次の一般 kernel API は実装済みである。

```lean
CapacityKernel
```

これは有限 outgoing channel、parent capacity、channel cost、非負性、
および outgoing cost bound を持つ。

```text
children : α → Finset β
capacity : α → ℝ
cost : α → β → ℝ
cost_nonneg
outgoing_le : Σ cost ≤ capacity
```

さらに normalize 層では、

```lean
CapacityKernel.normalizedWeight
CapacityKernel.normalizedOutgoing
CapacityKernel.normalizedOutgoing_le_one
CapacityKernel.normalizedWeight_subProbability
```

があり、positive capacity のもとで

```text
Σ cost / capacity ≤ 1
```

を得る。

provider / shadow 層では、

```lean
CapacityKernel.normalizedRealWeightProvider
SubMarkovShadow.ofCapacityKernel
SubMarkovShadow.ofCapacityKernel_subProbability
```

があり、capacity kernel の normalized shadow を既存の
`RealWeightProvider` / `SubMarkovShadow` へ落とせる。

したがって、DKMK-009 はこの既存 API を前提に始める。

## 2. DKMK-009 の主題

DKMK-009 の主題は次である。

```text
CapacityKernel route を primitive hitting route へ接続する。
```

より具体的には、

```text
CapacityKernel K
+ positive capacity
+ source-controlled chain family F
+ index compatibility
+ source mass bound
+ PrimitiveOn A
→ weightedHitMass A ≤ C
```

という汎用 wrapper を用意する。

これは数学的には、capacity bound

$$
\sum_{i\in I} cost(s,i)\le capacity(s)
$$

を正規化して

$$
\sum_{i\in I}\frac{cost(s,i)}{capacity(s)}\le 1
$$

とし、その normalized weight を primitive hitting bound に流す形である。

## 3. DKMK-009A: scope 固定

最初の作業は、この roadmap により scope を固定することである。

DKMK-009 で扱うものは次。

```text
generic capacity-kernel hitting bridge
global log-capacity kernel への特殊化
witness-derived quotient path family への接続
docs/report 更新
```

DKMK-009 では扱わないものは次。

```text
tail / truncation estimate
1 + O(1/log x) 型の解析評価
infinite primitive set statement
Mertens 型評価
```

これらは DKMK-010 以降の対象とする。

## 4. DKMK-009B: generic capacity-kernel hitting bridge

次に、一般 `CapacityKernel` から hitting bound へ行く薄い bridge を作る。

候補ファイルは次。

```text
DkMath/NumberTheory/PrimitiveSet/CapacityKernelHittingBridge.lean
```

想定する theorem-facing API は次の形。

```text
K : CapacityKernel σ ι
hcap : ∀ s, 0 < K.capacity s
s : σ
F : SourceControlledChainFamily M ι
hindex : K.children s = F.index
hA : PrimitiveOn A
hC : 0 ≤ C
hsource : ∀ i ∈ F.index, (M.μ (F.source i) : ℝ) ≤ C
------------------------------------------------------------
weightedHitMass A ≤ C
```

実装上は、新しい proof を大きく書く必要はない。
既存の

```lean
SubMarkovShadow.ofCapacityKernel
SubMarkovShadow.ofCapacityKernel_subProbability
SubMarkovShadow.weightedHitMass_le_const_applyAtToSourceControlled
```

を合成するだけでよい。

この bridge は DKMK-009 の核である。
ここにより、「Markov kernel は capacity kernel の normalized shadow」と
いう方針が Lean API として直接読めるようになる。

## 5. DKMK-009C: global log-capacity kernel への特殊化

次に、generic bridge を existing concrete kernel へ特殊化する。

既存の concrete kernel は次。

```lean
PrimePowerWitnessProvider.globalLogCapacityKernel
```

これは source state `n > 1` に対して、

```text
children(s) = IOf s.1
capacity(s) = log(s.1)
cost(s,q) = vonMangoldtShadowCost(s.1,q)
```

を持つ。

すでに

```lean
PrimePowerWitnessProvider.globalLogCapacitySubMarkovShadow
PrimePowerWitnessProvider.globalLogCapacitySubMarkovShadow_subProbability
```

もある。

したがって DKMK-009C では、重複した theorem を増やすのではなく、
必要に応じて `CapacityKernelHittingBridge` 側の generic theorem から
global log-capacity route が得られることを示す薄い wrapper に留める。

## 6. DKMK-009D: witness-derived quotient path family への接続

DKMK-008 の最終到達点は、witness-derived quotient path family だった。

```text
q = p(q)^k(q)
→ n → n/p(q) → ... → n/p(q)^k(q)
```

DKMK-009D では、これを capacity kernel route と明示的に接続する。

目標の読み方は次。

```text
PrimePowerWitnessProvider
→ globalLogCapacityKernel
→ normalized SubMarkovShadow
→ primePowerQuotientPathFamily
→ weightedHitMass bound
```

既存の DKMK-008L theorem はすでに weightedHitMass bound まで到達している。
DKMK-009D の役割は、その route が
`globalLogCapacityKernel` の normalized shadow から来ていることを
API と docs で明確化することにある。

## 7. DKMK-009E: public aggregator

新規 Lean file を追加する場合は、最後に public aggregator を更新する。

候補は次。

```text
DkMath/NumberTheory/PrimitiveSet.lean
```

必要なら、上位 entrypoint 側も確認する。
ただし DKMK-009 では既存 import topology を壊さない。
古い theorem 名や route は互換維持する。

## 8. DKMK-009F: docs/report

実装後、次を更新する。

```text
report-DKMK-009.md
DkMath_Markov_kernel-to-ck.md
History.md
```

`History.md` への追記は、最終 build 結果が出てから EOF に追加する。

## 9. build checkpoints

実装単位ごとの checkpoint は次。

```text
DKMK-009A:
  docs only
  git diff --check

DKMK-009B:
  lake build DkMath.NumberTheory.PrimitiveSet.CapacityKernelHittingBridge

DKMK-009C-D:
  lake build DkMath.NumberTheory.PrimitiveSet.LogCapacityHittingBridge
  lake build DkMath.NumberTheory.PrimitiveSet

DKMK-009E-F:
  lake build DkMath.NumberTheory.PrimitiveSet
```

もし generic bridge が既存 theorem の単なる rename wrapper になりすぎる場合は、
定理数を抑え、docs 側で route の意味を固定する。

## 10. DKMK-009 の到達目標

DKMK-009 の到達目標は、次の一文にまとめられる。

```text
DKMK capacity kernel の normalized shadow が、
primitive hitting route の正式な入力であることを Lean API と docs で固定する。
```

DKMK-007 は質量の器を作った。
DKMK-008 は下降路の地図を作った。
DKMK-009 は、その器と地図を動かす capacity kernel を本線へ戻す章である。

## 11. 実装メモ: DKMK-009B

DKMK-009B では、generic capacity-kernel hitting bridge を追加した。

追加ファイルは次。

```text
DkMath/NumberTheory/PrimitiveSet/CapacityKernelHittingBridge.lean
```

主な API は次。

```lean
CapacityKernel.normalizedSubMarkovShadow_providerAt_compatible
CapacityKernel.applyAtToSourceControlled
CapacityKernel.applyAtToSourceControlled_weightSubProbability
CapacityKernel.weightedHitMass_le_const_applyAtToSourceControlled
```

これにより、positive capacity を持つ任意の `CapacityKernel` から、
normalized `SubMarkovShadow` を経由して `SourceControlledChainFamily` に重みを載せ、
primitive `weightedHitMass` bound へ進む入口が固定された。

実装は新しい hitting proof を作らず、既存の
`SubMarkovShadow.ofCapacityKernel` と `SubMarkovShadow` の hitting bridge を
合成する薄い wrapper に留めた。

また、新規ファイルを public aggregator
`DkMath/NumberTheory/PrimitiveSet.lean` に追加した。

build checkpoint:

```text
lake build DkMath.NumberTheory.PrimitiveSet.CapacityKernelHittingBridge
lake build DkMath.NumberTheory.PrimitiveSet
```

いずれも成功。
