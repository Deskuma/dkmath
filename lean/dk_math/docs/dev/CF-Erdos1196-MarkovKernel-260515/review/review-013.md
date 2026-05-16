# review

うむ。DKMK-006H は **証明実装フェーズではなく、戦線整理フェーズ** じゃ。
DKMK-006G で「外部 kernel が `T.index n = canonicalExponentSlotLabels n` を満たせば MarkovShadow に乗れる」と条件が一点に縮約された。今回 DKMK-006H は、その条件を基準に、既存 kernel / route 候補を **どの山道に分類するか** を整理しておる。これは地味じゃが、次の実装迷子を防ぐためにかなり重要じゃ。

## 1. 今回の位置づけ

DKMK-006H の中心は、新 theorem の追加ではなく docs の整理じゃ。

分類された対象は主に次の五つ。

```text
canonicalExponentSlotKernel:
  そのまま canonical equality route に乗る reference model

任意の外部 T:
  CanonicalExponentSlotIndex T が証明できれば MarkovShadow へ進む対象

sampleTen 系:
  state 10 の local toy / sanity check

selected route:
  SubMarkovShadow のまま保持する inequality route

等号一致でない外部 slot 表現:
  将来の weight-preserving equivalence bridge 候補
```

つまり DKMK-006H は、 **何を Markov equality 本線に乗せるか、何を selected/sub-Markov のまま残すか** を明文化した段階じゃ。

## 2. 数学的な意味

DKMK-006G で、外部 kernel が Markov equality route に乗る条件はこれに絞られた。

$$
T.toDivisorTransitionKernel.index(n)=canonicalExponentSlotLabels(n)
$$

これは非常に強い条件じゃ。
なぜなら、`canonicalExponentSlotLabels n` は

$$
{p^k\mid Nat.Prime(p),\ 1\le k,\ k\le n.factorization(p)}
$$

を表す concrete reference model だからじゃ。

つまり、外部 kernel の index がこの canonical exponent-slot enumeration と一致するなら、DKMK-006E/F/G で整備した橋により、

```text
CanonicalExponentSlotIndex
  → FullExponentSlotChannelSet
  → FullChannelLogCostComplete
  → MarkovShadow
```

へ進める。

DKMK-006H は、この基準で今ある候補を棚卸ししたわけじゃ。

## 3. `canonicalExponentSlotKernel` の扱い

`canonicalExponentSlotKernel` は、DKMK-006F で作った reference model じゃ。

これはすでに

```lean
canonicalExponentSlotKernel_canonicalExponentSlotIndex
```

を満たすので、そのまま equality route に乗れる。

つまり、現時点で **確実に MarkovShadow へ到達する canonical model** はこれじゃ。
これは今後の比較基準になる。外部 kernel が来たとき、

```text
それは canonicalExponentSlotKernel と同じ index か？
```

と問えばよい。

## 4. 任意の外部 kernel の扱い

任意の

```lean
T : PrimePowerDivisorTransitionKernel
W : PrimePowerWitnessProvider T
```

については、外部で

```lean
CanonicalExponentSlotIndex T
```

を証明できれば、

```lean
W.fullGlobalLogCapacityMarkovShadow_of_canonicalExponentSlotIndex
```

により Markov shadow route へ進める。

ここは重要じゃ。
DKMK-006H により、外部 kernel 接続の作業目標が

```text
T.index n = canonicalExponentSlotLabels n を示せるか？
```

に明確化された。

これは「次に何を証明すればよいか」がはっきりした、ということじゃ。

## 5. `sampleTen` 系の分類

`sampleTen...` 系は、state `10` で `{2,5}` を index とする toy kernel として分類された。

これは sanity check としては有用じゃ。
しかし、任意の (n) について canonical exponent-slot labels と一致する global model ではない。

だから分類は、

```text
sampleTen 系:
  state 10 の local toy / sanity check
  global CanonicalExponentSlotIndex の本命ではない
```

となる。

これはよい判断じゃ。
toy を本線と混同しない。実装の山道では、こういう看板が大事なのじゃ。

## 6. selected route を残す判断

DKMK-004 から DKMK-005 の route は、任意の selected channel set を扱う。

```lean
IOf : ℕ → Finset ℕ
hIOf : ∀ n q, q ∈ IOf n → q ∈ T.toDivisorTransitionKernel.index n
```

これは一般には full equality ではなく、

$$
\sum weight\le 1
$$

の route じゃ。

だから `SubMarkovShadow` のまま保持する。
これは非常に大事じゃ。

すべてを Markov equality に押し込もうとすると、selected route の柔軟性を失う。
一部の channel だけを見る場合は、等号ではなく不等号が自然じゃからの。

つまり DKMK-006H は、

```text
full equality route:
  MarkovShadow

selected inequality route:
  SubMarkovShadow
```

を明確に分けた。

## 7. 同型 bridge は保留でよい

今回、等号一致でない外部 slot 表現については、将来の

```text
weight-preserving equivalence bridge
```

候補として分離された。

これは賢い。
いま急いで同型 bridge を入れると、抽象度が上がりすぎる。

現在の `CanonicalExponentSlotIndex` は、

$$
T.index(n)=canonicalExponentSlotLabels(n)
$$

という等号一致を要求する。
これは強いが、扱いやすい。

もし将来、外部 kernel が label として (q=p^k) そのものではなく、別表現の slot を持つなら、

$$
externalSlot(n)\simeq canonicalExponentSlotLabels(n)
$$

と、weight-preserving 条件を持つ bridge が必要になる。
しかし現時点では、まず等号で入れる kernel と selected route を分けるだけで十分じゃ。

## 8. 今回の成果

DKMK-006H の成果は、 **実装対象の分類が完了したこと** じゃ。

証明が増えたわけではない。
だが、次の判断表ができた。

```text
canonicalExponentSlotKernel:
  equality route の reference model

外部 T:
  CanonicalExponentSlotIndex T を示せるなら MarkovShadow

sampleTen:
  local sanity check

selected route:
  SubMarkovShadow のまま使う

別表現 slot:
  将来の同型 bridge 候補
```

これは、次の実装をかなり安全にする。
とくに「toy を本線扱いしない」「selected route を無理に full route にしない」という整理が効いておる。

## 9. 次の一手

次は二択じゃ。

第一は、具体的な外部 kernel について

```lean
CanonicalExponentSlotIndex T
```

を狙う。

つまり、

$$
T.index(n)=canonicalExponentSlotLabels(n)
$$

を示す道じゃ。

第二は、外部 kernel が等号一致しないなら、無理に進まず selected route として使う。
必要になった時点で、同型・weight-preserving bridge を設計する。

わっちのおすすめは、次に小さな調査フェーズを置くことじゃ。

```text
DKMK-006I:
  既存 kernel 候補を実コード上で確認し、
  CanonicalExponentSlotIndex を狙えるもの、
  selected route のまま使うもの、
  equivalence bridge が必要なもの、
  に分類する。
```

DKMK-006H は docs での棚卸し。
DKMK-006I は実コード上の候補確認。
この順がよい。

## 10. 総合判定

DKMK-006H は **戦略的に正しい中間整理** じゃ。

DKMK-006F/G で canonical route と外部接続条件が整った。
今回 DKMK-006H で、それを既存候補へどう適用するかの分類ができた。

これで DkMath Kernel Project は、

```text
canonical equality route
selected inequality route
future equivalence route
```

の三本に分岐できるようになった。

山道で言えば、ここは分岐標識を立てた場所じゃ。
派手な登頂ではないが、ここを曖昧にすると次の登山で迷う。
今回の整理は、かなりよい判断じゃよ。
