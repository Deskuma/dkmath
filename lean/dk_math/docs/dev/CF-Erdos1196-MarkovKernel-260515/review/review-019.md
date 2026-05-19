# review

うむ。DKMK-007D は **DKMK-007C の最後の外部入力を、最小 concrete model で閉じた段階** じゃ。
前回までは、log-capacity shadow を primitive hitting に渡すには、compatible な `SourceControlledChainFamily F` と、`F.index = IOf s.1` や `F.index = canonicalExponentSlotLabels s.1` を外から渡す必要があった。今回、その `F` を作る標準的な最小 constructor が入り、少なくとも singleton model では compatibility が `rfl` で閉じるようになった。

## 1. 今回の核心

追加された中心は `BranchBridge.lean` 側のこれじゃ。

```lean
SourceControlledChainFamily.ofIndex
SourceControlledChainFamily.singletonSelf
SourceControlledChainFamily.natSingletonSelf
```

`ofIndex` は、index / chain / source / mass control をそのまま束ねる named constructor。
`singletonSelf` は、各 index `i` に singleton chain `{label i}` を割り当て、source も `label i` にする最小 model。
`natSingletonSelf` は、Nat-indexed route 用に `label := id` としたものじゃ。

数学的には、各 channel \(q\) に対して chain をただ一つの点 \({q}\) にする。

$$
chain(q)={q},\qquad source(q)=q
$$

この model では、chain は自明に divisibility chain であり、source mass control も自明に

$$
\mu(q)\le \mu(q)
$$

で閉じる。だから Lean 的にも `rfl` で多くが落ちる。

## 2. DKMK-007C から何が改善されたか

DKMK-007C では、selected route で次が必要だった。

```lean
hindex : IOf s.1 = F.index
```

canonical route では次が必要だった。

```lean
hindex : canonicalExponentSlotLabels s.1 = F.index
```

今回 DKMK-007D では、`F` 自体を次のように選べる。

```lean
SourceControlledChainFamily.natSingletonSelf (IOf s.1)
```

または、

```lean
SourceControlledChainFamily.natSingletonSelf (canonicalExponentSlotLabels s.1)
```

すると `F.index` は定義上その集合そのものなので、compatibility が `rfl` で閉じる。

つまり、DKMK-007C の theorem-facing API に対し、呼び出し側の負担が一段減った。

## 3. LogCapacityHittingBridge 側の追加

`LogCapacityHittingBridge.lean` には、selected / canonical route の convenience API が追加された。

selected route 側：

```lean
PrimePowerWitnessProvider.globalLogCapacitySubMarkovShadow_applyAtToNatSingletonSelf
PrimePowerWitnessProvider.globalLogCapacitySubMarkovShadow_natSingletonSelf_weightedHitMass_le_const
```

canonical route 側：

```lean
canonicalExponentSlotMarkovShadow_applyAtToNatSingletonSelf
canonicalExponentSlotMarkovShadow_natSingletonSelf_weightedHitMass_le_const
```

これで、到達形はこうなった。

```text
selected route:
  globalLogCapacitySubMarkovShadow
  → natSingletonSelf (IOf s.1)
  → primitive real-weighted hit mass ≤ C
```

```text
canonical route:
  canonicalExponentSlotMarkovShadow
  → natSingletonSelf (canonicalExponentSlotLabels s.1)
  → primitive real-weighted hit mass ≤ C
```

これはかなり使いやすい。

## 4. 数学的な意味

今回の singleton family は、まだ本格的な divisor-chain / descent-chain ではない。
しかし、 **shadow の重みを primitive hitting API へ流す最小モデル** としては十分に意味がある。

特に、いまの route では次が閉じた。

```text
log-capacity shadow
  → concrete SourceControlledChainFamily
  → primitive weighted hitting bound
```

つまり、前回までの「compatible な \(F\) があれば」という条件が、少なくとも singleton model では「この \(F\) を選べばよい」に変わった。

これは API の段差を減らす大事な進歩じゃ。

## 5. ただし、これは最終 hitting model ではない

ここは留意点じゃ。

`natSingletonSelf` の chain は \(\{q\}\) だけなので、実際の下降過程

$$
n\mapsto n/q
$$

や divisibility chain の途中構造を表すものではない。

したがって、これは **最小 concrete model** であって、Erdős #1196 の本格的な descent/hitting chain を表す完成形ではない。

docs でも次課題として、singleton family ではなく、実際の divisor-chain / descent-chain content を持つ constructor へ拡張すること、また source mass bound を具体的な mass model から供給することが挙げられている。

## 6. DKMK-007 系の現在地

ここまでの流れは、かなり綺麗じゃ。

```text
DKMK-007A:
  RealWeightProvider
  → RealWeightedPathFamily
  → primitive weighted hit bound

DKMK-007B:
  SubMarkovShadow / MarkovShadow
  → primitive hitting wrapper

DKMK-007C:
  globalLogCapacitySubMarkovShadow / canonicalExponentSlotMarkovShadow
  → hitting wrapper

DKMK-007D:
  natSingletonSelf により index compatibility を rfl 化
```

つまり、DKMK-007D は **接続に必要だった形式的な compatibility 入力を、標準 constructor で消した** フェーズじゃ。

## 7. 次の一手

次は、いよいよ singleton を越える段階じゃな。

わっちなら DKMK-007E はこう切る。

```text
DKMK-007E:
  SourceControlledChainFamily.ofDivisorStep
  または SourceControlledChainFamily.ofDescentChain
```

目標は、各 channel \(q\) に対して singleton \(\{q\}\) ではなく、実際の chain を持たせることじゃ。

候補は二つある。

```text
短い descent:
  chain(q) := {s.1, s.1 / q}

ラベル側 descent:
  chain(q) := {q, basePrimeOf(q), 1} など
```

どちらを選ぶかは、今後の hitting 対象 \(A\) をどこに置くかで変わる。Erdős #1196 本線に寄せるなら、親状態 \(n\) から \(n/q\) へ下る chain family の方が自然じゃ。

## 8. 総合判定

DKMK-007D は **小さいが実用上かなり大きい接続改善** じゃ。

新しい大定理というより、既存の DKMK-007C route を「実際に呼びやすい API」にした。
`IOf s.1` や `canonicalExponentSlotLabels s.1` をそのまま index に選べば、compatibility が `rfl` で閉じる。これは後続実装で効く。

現在の到達点はこうじゃ。

```text
selected / canonical log-capacity shadow
  → natSingletonSelf concrete family
  → primitive real-weighted hit mass ≤ C
```

次はこの singleton model を、実際の divisor-chain / descent-chain model へ厚くする段階じゃ。
ぬしよ、これは橋の舗装が済んだ状態じゃな。次はその橋を渡って、川の向こうに本物の下降路を敷く番じゃ。
