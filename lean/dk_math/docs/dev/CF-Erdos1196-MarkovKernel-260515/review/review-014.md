# review

うむ。DKMK-006I は、 **DKMK-006H の分類を Lean 側でも固定した inventory フェーズ** じゃ。
派手な新理論ではないが、かなり大事な **交通整理の theorem 化** になっておる。docs 上の「これは本線、これは toy、これは将来 bridge」といった分類を、実コード上でも positive / negative theorem として刻んだわけじゃな。

## 1. 今回の中心

新規ファイルはこれじゃ。

```lean
DkMath.NumberTheory.PrimitiveSet.KernelCandidateInventory
```

追加された主 theorem は次の通り。

```lean
kernelInventory_canonicalExponentSlotKernel_ready
sampleTenPrimePowerDivisorTransitionKernel_index_two_empty
two_mem_canonicalExponentSlotLabels_two
sampleTenPrimePowerDivisorTransitionKernel_not_canonicalExponentSlotIndex
sampleTenToyWeightKernel_not_canonicalExponentSlotIndex
```

これにより、DKMK-006H で docs 上に書いた分類のうち、

```text
canonicalExponentSlotKernel:
  equality route の reference model

sampleTen 系:
  local toy / sanity check
  global CanonicalExponentSlotIndex ではない
```

が Lean theorem として固定された。

## 2. positive case の固定

まず、

```lean
kernelInventory_canonicalExponentSlotKernel_ready :
  CanonicalExponentSlotIndex canonicalExponentSlotKernel
```

が追加された。

これは既存の

```lean
canonicalExponentSlotKernel_canonicalExponentSlotIndex
```

を inventory 名で再掲しているだけじゃが、意味は大きい。

「現時点で Markov equality route の reference model はこれである」という看板を、`KernelCandidateInventory` 側に立てたことになる。

つまり、今後「どの kernel が canonical equality route に乗るのか？」と見たとき、まず参照する入口ができた。

## 3. sampleTen 系の negative case

次に重要なのが、`sampleTen...` 系の否定を theorem 化したことじゃ。

証明の観察点は state `2`。

sample-ten kernel 側は state `10` 用の toy なので、

```lean
sampleTenPrimePowerDivisorTransitionKernel.toDivisorTransitionKernel.index 2 = ∅
```

一方、canonical exponent-slot labels では state `2` に label `2` が入る。

```lean
2 ∈ canonicalExponentSlotLabels 2
```

したがって、もし

```lean
CanonicalExponentSlotIndex sampleTenPrimePowerDivisorTransitionKernel
```

が成り立つなら、state `2` で index が一致するはずだが、片方は空で片方は `2` を含む。矛盾じゃ。

これで、

```lean
¬ CanonicalExponentSlotIndex sampleTenPrimePowerDivisorTransitionKernel
```

が閉じる。

さらに、`sampleTenToyWeightKernel` も index は同じ local toy なので、同様に

```lean
¬ CanonicalExponentSlotIndex sampleTenToyWeightKernel
```

が閉じている。

## 4. 数学的な意味

これは単なる「サンプルが違う」と言っているだけではない。

DKMK-006G で、外部 kernel が Markov equality route に乗る条件は

$$
T.toDivisorTransitionKernel.index(n)=canonicalExponentSlotLabels(n)
$$

に縮約された。

今回 DKMK-006I では、この条件を実際の候補に当てて、

* `canonicalExponentSlotKernel` は yes
* `sampleTen...` 系は no

と判定した。

つまり、 **canonical equality route に乗せるべき対象と、local sanity check に留める対象が Lean 上で分離された** ことになる。

これはかなり健全じゃ。
toy を本線に誤って持ち込まないための安全柵になる。

## 5. なぜ state `2` を使うのが良いか

state `2` は非常に良い反例点じゃ。

canonical route では、

$$
2=2^1
$$

なので、当然 `canonicalExponentSlotLabels 2` に `2` が入る。

一方 sampleTen 系は state `10` 専用なので state `2` では空。

この差は最小で明快じゃ。

$$
\emptyset\ne{2}
$$

という違いで global canonical index ではないことが即座に見える。
こういう反例は Lean でも読み手にも優しい。

## 6. 今回の位置づけ

DKMK-006H は docs 上の棚卸しだった。

DKMK-006I は、そのうちの一部を Lean 側へ移した。

```text
DKMK-006H:
  分類方針を docs で整理

DKMK-006I:
  positive case と negative toy case を theorem 化
```

これは自然な流れじゃ。

とくに `KernelCandidateInventory.lean` というファイル名が良い。
ここは大定理の置き場ではなく、候補分類の置き場であることが明確じゃからの。

## 7. 何がまだ残っているか

今回、selected route と future equivalence route については新 interface を追加していない。

これは正しい。
今はまだ必要以上に抽象化しない方がよい。

残る課題は、History にもある通り、

```text
本線で使う具体的な外部 kernel が現れたら、
CanonicalExponentSlotIndex T を直接狙う。
```

また、等号一致ではない external slot 表現が必要になった場合だけ、

```text
同型・weight-preserving bridge
```

を設計する。

つまり、現時点での残課題は「今すぐ bridge を増やす」ではなく、 **具体的な外部 kernel が出た時に適切に分類する** ことじゃ。

## 8. DKMK-006 系全体での現在地

DKMK-006I まで来て、DKMK-006 系はかなり整理された。

```text
006A:
  FullPrimePowerChannelSet

006B:
  MarkovShadow / FullChannelLogCostComplete

006C:
  FullExponentSlotCoverage

006D:
  FullChannelLogSum

006E:
  FullExponentSlotChannelSet → MarkovShadow

006F:
  canonicalExponentSlotLabels → MarkovShadow

006G:
  外部 T.index = canonical labels なら MarkovShadow

006H:
  kernel 候補の docs 棚卸し

006I:
  positive / negative 候補を Lean theorem 化
```

これはかなりよい流れじゃ。
抽象 route、canonical route、外部 bridge、候補分類まで、一通り揃ってきた。

## 9. 総合判定

DKMK-006I は **小さいが重要な堅めの一手** じゃ。

数学的に新しい等式を増やしたわけではない。
しかし、理論運用上の混線を防いだ。

特に、

```text
canonicalExponentSlotKernel は equality route の本命
sampleTen 系は local toy であって global canonical index ではない
```

を Lean theorem として固定したのは大きい。

これで、DkMath Kernel Project は次の状態になった。

```text
本線:
  canonicalExponentSlotKernel / CanonicalExponentSlotIndex

玩具:
  sampleTen 系

汎用:
  selected SubMarkov route

将来:
  weight-preserving equivalence bridge
```

賢狼の見立てでは、次は慌てて抽象 bridge を増やすより、ここで一度 **DKMK-001 から 006I までの登頂整理** を行うのがよい。
どこが canonical equality route で、どこが selected inequality route で、どこが future equivalence route なのかを 1 枚にしておくと、次の外部 kernel 接続で迷わぬ。

よいぞ、ぬしよ。
今回は派手な旗ではなく、山道の分岐に立てた堅牢な標識じゃ。こういう標識が、後の大登頂で効いてくるのじゃ。
