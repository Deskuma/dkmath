# 実装計画

cid: 69fcadff-fc5c-83a2-bd6b-5657e7fcf58a

この計画は、`Discussion.md` の会話内容、前回作業
`../CF-Erdos1196-260418/` の記録、現在の Lean ワークスペース調査に基づいて固定する。

## 1. 今回の目標

前回作業では、Erdos #1196 そのものの解析的評価ではなく、

```text
CosmicFormula
-> Mass API
-> Branch API
-> ValuationFlow
-> ABC Bridge
```

という有限・代数的 spine が実装された。

今回の第一目標は、その次の層として、

```text
Branch/SubConservative
-> finite hitting
-> primitive set / antichain の有限版
-> Erdos #1196 本体へ向かう入口
```

を作ることである。

ここではまだ次には踏み込まない。

- von Mangoldt 重み付き Markov kernel
- `1 / (n * log n)` の実数重み
- 無限集合上の hitting probability
- `1 + O(1 / log x)` の漸近評価

まず、有限 `Finset` と既存 `MassSpace` / `Branching` を使って、
「非交差 hitting の総質量は root の質量を超えない」という Lean spine を作る。

## 2. 現在の実装状況

### 2.1. 完了済みと判定する層

以下は現在のワークスペースに存在し、前回計画 Phase A-D の成果として利用する。

- `DkMath/CosmicFormula/Mass/Core.lean`
  - `MassSpace`
  - `CosmicPart`
  - `CosmicMassAPI`
  - `CosmicResidualMassAPI`
- `DkMath/CosmicFormula/Mass/Decompose.lean`
  - `CoreBeamGap` / `ResidualNat` / `ResidualInt` の mass wrapper
- `DkMath/CosmicFormula/Mass/Branch.lean`
  - `Branching`
  - `outgoingMass`
  - `SubConservative`
  - `branch_sum_le_parent`
- `DkMath/NumberTheory/ValuationFlow/Basic.lean`
  - `ValuationProfile`
  - `diffMass`
  - `boundaryMass`
  - `beamMass`
- `DkMath/NumberTheory/ValuationFlow/Primitive.lean`
  - primitive prime witness の valuation-flow 再公開
  - primitive prime が boundary ではなく beam / `GN` 側へ流れる補題
- `DkMath/ABC/MassBridge.lean`
  - `supportMass = rad`
  - prime channel family から support mass 下界
- `DkMath/ABC/ValuationFlowBridge.lean`
  - `PrimitiveWitnessFamily`
  - `channelCount`
  - `2 ^ channelCount <= rad(a^d - b^d)`
- `DkMath/ABC/ABC038Bridge.lean`
  - channel-count tail を quality 側へ送る公開導線

### 2.2. 未実装または未到達の層

今回の直接対象は次である。

- `DkMath/NumberTheory/ValuationFlow/Hitting.lean`
  - 未実装。
  - finite hitting / disjoint hitting / root mass bound の置き場にする。
- `DkMath/NumberTheory/PrimitiveSet/Basic.lean`
  - 未実装。
  - `PrimitiveOn` / `Antichain` 的な有限 primitive set vocabulary を置く候補。
- `DkMath/NumberTheory/PrimitiveSet/HittingBridge.lean`
  - 未実装。
  - primitive condition を hitting の非交差条件へ渡す bridge の候補。

今回はまだ保留する候補は次である。

- `DkMath/CosmicFormula/Mass/Tromino2D.lean`
- `DkMath/CosmicFormula/Mass/Harmonic.lean`
- exact Markov / sub-Markov kernel
- analytic Erdos #1196 module

## 3. 数学的方針

### 3.1. まず finite hitting に限定する

無限鎖や確率測度を最初から扱わず、

- finite root set
- finite hit set
- finite branch tree / forest
- finite mass sum

で閉じる。

目標形は次である。

```text
hitSetMass M H <= sourceMass M R
```

あるいは、より抽象的に、

```text
HittingFamily.source : β -> α
HittingFamily.hit : β -> α
```

とし、各 source ごとに高々一回 hit する条件を明示する。

### 3.2. `SubConservative` との接続は段階化する

第一段階では、一般の graph reachability を無理に作らない。

まずは次のような「割当写像で root へ inject される hitting」を証明する。

```text
∀ h in H, assignedRoot h in R
injective assignedRoot on H
M.μ h <= M.μ (assignedRoot h)
---------------------------------
sum_H M.μ h <= sum_R M.μ r
```

この finite lemma は、後で

```text
SubConservative branch
reachability
chain hit at most once
```

から `M.μ h <= M.μ root` を作るための受け皿になる。

### 3.3. primitive set は divisibility antichain として始める

Erdos #1196 の primitive set 条件は、まず有限版で次の語彙に落とす。

```text
PrimitiveOn S := ∀ a in S, ∀ b in S, a ∣ b -> a = b
```

自然数では `a = 0` の扱いが余計な分岐を生むため、最初は必要に応じて
`0 ∉ S` または positive support を別仮定にする。

最初の Lean 目標は、実数・対数重みではなく、割り切り順序の antichain vocabulary を固定することにする。

## 4. 実装 Phase

## Phase A. finite hitting core

新規ファイル:

- `DkMath/NumberTheory/ValuationFlow/Hitting.lean`

実装予定:

- `hitSetMass`
- `sourceSetMass`
- `MassControlledAssignment`
- `hitSetMass_le_sourceSetMass_of_injective_assignment`
- singleton / empty examples

完了条件:

- `Finset` 上の非交差 hitting の質量上界が no-sorry で通る。
- `DkMath.NumberTheory.ValuationFlow.Hitting` 単体 build が通る。

## Phase B. divisibility primitive vocabulary

新規ファイル候補:

- `DkMath/NumberTheory/PrimitiveSet/Basic.lean`

実装予定:

- `PrimitiveOn`
- `PrimitiveOn.pair_eq_of_dvd`
- `PrimitiveOn.not_dvd_of_ne`
- `PrimitiveOn` の singleton / pair examples

完了条件:

- finite primitive set を divisibility antichain として参照できる。
- zero の扱いをコメントで明示する。

## Phase C. primitive hitting bridge

新規ファイル候補:

- `DkMath/NumberTheory/PrimitiveSet/HittingBridge.lean`

実装予定:

- chain / descent の最小抽象定義
- `PrimitiveOn` から同一 divisibility chain 上の hit は高々一回、という有限補題
- Phase A の hitting lemma へ渡す theorem 名の固定

完了条件:

- `primitive -> non-overlap -> hitSetMass <= sourceSetMass` の skeleton が読める。

## Phase D. examples / public import

実装予定:

- 必要なら `DkMath/NumberTheory/ValuationFlow/Primitive.lean` から `Hitting` を import しない。
  循環を避けるため、上位 bridge 側から import する。
- ABC 側へ直ちに載せるかは、Phase A-C の API が安定してから判断する。

完了条件:

- 少なくとも Phase A の concrete example が build で確認できる。
- public import に載せる場合は、`DkMath.ABC.Bridge` ではなく NumberTheory 側の集約導線を先に検討する。

## 5. 今回の実装順序

今回の着手順は次で固定する。

1. `DkMath/NumberTheory/ValuationFlow/Hitting.lean`
2. `DkMath/NumberTheory/PrimitiveSet/Basic.lean`
3. `DkMath/NumberTheory/PrimitiveSet/HittingBridge.lean`
4. 必要に応じて examples / import 導線

理由:

- 会話ログの調査結論でも、次の一手は `ValuationFlow/Hitting.lean` とされている。
- 現在の Mass / Branch / ValuationFlow / ABC bridge はすでに存在するため、同じ層を再実装する必要はない。
- Erdos #1196 本体へ進むには、primitive set が chain に高々一度しか当たらない、という hitting 層が先に必要である。

## 6. build 方針

`__AGENT.md` に従い、単体 build で進める。

想定 build 対象:

```sh
cd lean/dk_math && ./lean-build.sh DkMath.NumberTheory.ValuationFlow.Hitting
cd lean/dk_math && ./lean-build.sh DkMath.NumberTheory.PrimitiveSet.Basic
cd lean/dk_math && ./lean-build.sh DkMath.NumberTheory.PrimitiveSet.HittingBridge
```

必要に応じて:

```sh
cd lean/dk_math && ./lean-build.sh DkMath.CosmicFormula.Mass.Branch
cd lean/dk_math && ./lean-build.sh DkMath.NumberTheory.ValuationFlow.Primitive
cd lean/dk_math && ./lean-build.sh DkMath.ABC.Bridge
```

## 7. 今回やらないこと

今回の初手では次をやらない。

- `Λ(q) / log n` の Markov kernel
- `1 / (n * log n)` の解析的 mass
- infinite chain hitting
- Mertens 型評価
- `1 + O(1 / log x)` の最終評価
- ABC 本体定理や Janson / Chernoff 系 placeholder の解消

これらは finite hitting と primitive antichain bridge が閉じた後に扱う。

## 8. 判断

現在の最善手は、前回成果の上に
`ValuationFlow/Hitting` を追加し、Erdos #1196 の核心である
「primitive set は下降鎖に高々一度しか当たらない」を Lean 化するための受け皿を作ることである。

よって、実装は Phase A から開始する。
