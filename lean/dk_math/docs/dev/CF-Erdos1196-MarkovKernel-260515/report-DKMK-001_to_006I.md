# report: DKMK-001 to 006I

## 1. 現在地

DKMK-001 から DKMK-006I までで、Markov kernel route は次の三本に整理された。

```text
canonical equality route:
  full exponent-slot labels
  → full log-capacity equality
  → MarkovShadow

selected inequality route:
  selected prime-power channels
  → log-capacity inequality
  → SubMarkovShadow

future equivalence route:
  external slot representation
  ≃ canonical exponent-slot labels
  with weight/cost preservation
```

この整理の中心は、Markov kernel を最初から置かず、

```text
capacity / cost / prime-power witness
```

を先に置き、その正規化像として Markov 的構造を読むことである。

## 2. selected inequality route

DKMK-001 から DKMK-005 では、selected channel set に対する sub-probability route を整備した。

```text
CapacityKernel
  → normalizedRealWeightProvider
  → SubProbability
  → SubMarkovShadow
```

number theory 側では、prime-power witness `q = p ^ k` から base prime `p` を読み、

```text
vonMangoldtShadowCost(n, q) = log p
```

を finite shadow cost として扱う。

selected route では、外部から

```lean
IOf : ℕ → Finset ℕ
hIOf : ∀ n q, q ∈ IOf n → q ∈ T.toDivisorTransitionKernel.index n
```

を受け取る。
一般に `IOf n` は full channel ではないため、得られる結論は outgoing mass `≤ 1` であり、
`SubMarkovShadow` のまま保持する。

この route は、部分 channel や hitting bound 側の柔軟性を失わないための inequality 本線である。

## 3. canonical equality route

DKMK-006A から DKMK-006F では、full channel equality route を段階的に閉じた。

まず full channel を

```lean
FullPrimePowerChannelSet
```

として interface 化し、full channel 上で log-cost が capacity を使い切る条件を

```lean
FullChannelLogCostComplete
```

として分離した。

次に、full channel が exponent slot 全体であることを

```lean
FullExponentSlotChannelSet
```

で表し、そこから exact multiplicity coverage と finite log sum を経由して
`FullChannelLogCostComplete` を導いた。

最終的に DKMK-006F で concrete reference model を置いた。

```lean
canonicalExponentSlotLabels n
```

これは次の finite label set である。

```text
{ p ^ k | Nat.Prime p, 1 ≤ k, k ≤ n.factorization p }
```

この canonical labels から

```lean
canonicalExponentSlotKernel
canonicalExponentSlotWitnessProvider
canonicalExponentSlotMarkovShadow
```

まで no-sorry で到達した。

## 4. external equality bridge

DKMK-006G では、外部 kernel を canonical equality route へ接続する条件を切り出した。

```lean
structure CanonicalExponentSlotIndex
    (T : PrimePowerDivisorTransitionKernel) : Prop where
  index_eq :
    ∀ n, T.toDivisorTransitionKernel.index n =
      canonicalExponentSlotLabels n
```

この条件があれば、任意の witness provider `W` について

```lean
W.fullGlobalLogCapacityMarkovShadow_of_canonicalExponentSlotIndex
```

で Markov shadow へ進める。

したがって、外部 kernel 接続の等号版 target は明確である。

```text
prove:
  T.toDivisorTransitionKernel.index n = canonicalExponentSlotLabels n

then:
  T has the full log-capacity Markov shadow route
```

## 5. candidate inventory

DKMK-006H と DKMK-006I では、候補分類を docs と Lean theorem の両側で固定した。

positive case:

```lean
kernelInventory_canonicalExponentSlotKernel_ready :
  CanonicalExponentSlotIndex canonicalExponentSlotKernel
```

negative toy cases:

```lean
sampleTenPrimePowerDivisorTransitionKernel_not_canonicalExponentSlotIndex :
  ¬ CanonicalExponentSlotIndex sampleTenPrimePowerDivisorTransitionKernel

sampleTenToyWeightKernel_not_canonicalExponentSlotIndex :
  ¬ CanonicalExponentSlotIndex sampleTenToyWeightKernel
```

`sampleTen...` 系は state `10` の local sanity check であり、global canonical equality route の本命ではない。
証明上は state `2` で sample-ten index が空である一方、`canonicalExponentSlotLabels 2` には `2` が入ることを使う。

## 6. 分岐表

現時点の実装判断表は次の通りである。

| 対象 | 現在の分類 | 到達点 |
|---|---|---|
| `canonicalExponentSlotKernel` | canonical equality reference model | `MarkovShadow` |
| `T` with `CanonicalExponentSlotIndex T` | external equality bridge | `MarkovShadow` |
| selected `IOf` route | selected inequality route | `SubMarkovShadow` |
| `sampleTen...` | local toy / sanity check | global equality route には乗せない |
| non-equal external slot representation | future equivalence route | 未設計 |

## 7. 次の判断

次に具体的な外部 kernel が現れた場合、最初に確認する条件は次である。

```lean
CanonicalExponentSlotIndex T
```

これが狙えるなら equality route に乗せる。
狙えないが selected channel として十分なら、`SubMarkovShadow` route のまま使う。
label 表現が `q = p ^ k` そのものではなく、別表現の slot である場合だけ、
weight-preserving equivalence bridge を新しく設計する。

この時点では、同型 bridge を先回りして追加しない。
等号 route、selected route、future route の分岐を保ったまま、次の concrete kernel を待つ。
