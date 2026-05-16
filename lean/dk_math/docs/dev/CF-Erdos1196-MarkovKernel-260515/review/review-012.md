# review

うむ。DKMK-006G は、 **canonical reference model と任意の外部 kernel を接続する比較橋** じゃ。
DKMK-006F で canonical exponent-slot route は MarkovShadow まで到達した。今回 DKMK-006G では、「外部の `T.index n` がその canonical label set と同じなら、その外部 kernel も同じ MarkovShadow route に乗れる」という theorem-facing interface が入った。報告でも、`T.index n = canonicalExponentSlotLabels n` さえ示せば full log-capacity route が Markov shadow へ進む、と整理されておる。

## 1. 今回の核心

中心は新ファイルじゃ。

```lean
DkMath.NumberTheory.PrimitiveSet.FullExponentSlotIndexBridge
```

追加された主な構造はこれ。

```lean
structure CanonicalExponentSlotIndex
    (T : PrimePowerDivisorTransitionKernel) : Prop where
  index_eq :
    ∀ n, T.toDivisorTransitionKernel.index n = canonicalExponentSlotLabels n
```

数学的には、

$$
T.index(n)=canonicalExponentSlotLabels(n)
$$

を仮定として切り出したものじゃ。

ここで `canonicalExponentSlotLabels n` は DKMK-006F で作った concrete reference model、つまり

$$
{p^k\mid Nat.Prime(p),\ 1\le k,\ k\le n.factorization(p)}
$$

に対応する finite label set じゃ。

したがって DKMK-006G は、「任意の外部 kernel が canonical exponent-slot enumeration と一致するなら、canonical route の全成果を継承できる」という橋になる。

## 2. 何が閉じたか

今回閉じた流れはこうじゃ。

```text
CanonicalExponentSlotIndex T
  → T.index n の membership を exponent-slot 仕様へ展開
  → FullExponentSlotChannelSet
  → FullChannelLogCostComplete
  → MarkovShadow
```

Lean 側ではまず、

```lean
CanonicalExponentSlotIndex.mem_iff
```

により、

$$
q\in T.index(n)\leftrightarrow \exists p,k,\ Nat.Prime(p)\land 1\le k\land k\le n.factorization(p)\land q=p^k
$$

が得られる。

次に、

```lean
fullExponentSlotChannelSet_of_canonicalExponentSlotIndex
```

で、`FullPrimePowerChannelSet.canonical T` が `FullExponentSlotChannelSet` を満たす。

その後は既存の DKMK-006E の橋を使って、

```lean
fullChannelLogCostComplete_of_canonicalExponentSlotIndex
fullGlobalLogCapacityMarkovShadow_of_canonicalExponentSlotIndex
```

まで進む。
つまり、任意の `PrimePowerWitnessProvider W` について、`CanonicalExponentSlotIndex T` があれば Markov shadow が出る。

## 3. DKMK-006F との関係

DKMK-006F は、

```text
canonicalExponentSlotLabels
  → canonicalExponentSlotKernel
  → canonicalExponentSlotMarkovShadow
```

という concrete reference model だった。

今回 DKMK-006G は、その reference model を外部 kernel へ移すための比較 interface じゃ。

さらに、

```lean
canonicalExponentSlotKernel_canonicalExponentSlotIndex
```

も追加されておる。これは reference model 自身が当然 `CanonicalExponentSlotIndex` を満たすことを示す補題じゃ。報告にも、reference model 自身についてこの interface が成立すると記録されておる。

これで構造がかなり綺麗になった。

```text
canonical model:
  canonicalExponentSlotKernel
  → CanonicalExponentSlotIndex
  → MarkovShadow

external model:
  T
  + CanonicalExponentSlotIndex T
  → MarkovShadow
```

つまり canonical route は孤立した実験モデルではなく、外部 kernel の比較基準になった。

## 4. 数学的な意味

ここまでの DkMath Kernel route は、既存 Markov kernel を直接コピーせず、

$$
\text{exponent slot}\to\text{log cost}\to\text{capacity equality}\to\text{Markov shadow}
$$

という形で構成してきた。

今回の `CanonicalExponentSlotIndex` により、任意の外部 kernel について、必要条件がかなり明瞭になった。

必要なのは、

$$
T.index(n)={p^k\mid Nat.Prime(p),\ 1\le k,\ k\le n.factorization(p)}
$$

これだけじゃ。

これが示せれば、外部 kernel 側の witness provider がどのように内部 witness を選んでいても、すでに DKMK-006E の `basePrimeOf_eq_of_prime_pow_mem` により base prime の読みは一意に押さえられる。したがって Markov equality route に乗れる。

## 5. 何が前進したか

前回 DKMK-006F の段階では、残課題はこうだった。

```text
既存 T.index n と canonicalExponentSlotLabels n の一致、または bridge 条件を設計する。
```

今回 DKMK-006G で、そのうち **等号一致版の bridge 条件** が実装された。

つまり残課題は、さらに具体化された。

```text
既存の具体的 T について
CanonicalExponentSlotIndex T
を証明できるか確認する。
```

これは非常によい縮約じゃ。
以前は「どう接続するか」だった。
今は「この等式を示せば接続できる」になった。

## 6. まだ残る分岐

今回の bridge は **等号一致** の場合を扱っている。

しかし History の次課題にもある通り、場合によっては等号ではなく、同型や weight-preserving bridge が必要になるかもしれぬ。

たとえば外部 `T.index n` が canonical labels そのものではなく、別の label 表現を使っている場合じゃ。

その場合は、

$$
T.index(n)\simeq canonicalExponentSlotLabels(n)
$$

のような equivalence と、cost を保つ条件が必要になる。

将来的な interface 候補はこうじゃな。

```lean
structure CanonicalExponentSlotIndexEquiv
    (T : PrimePowerDivisorTransitionKernel) where
  toCanonical : ∀ n, T.toDivisorTransitionKernel.index n → canonicalExponentSlotLabels n
  fromCanonical : ∀ n, canonicalExponentSlotLabels n → T.toDivisorTransitionKernel.index n
  ...
```

ただし、これはまだ急がなくてよい。
まずは等号版 `CanonicalExponentSlotIndex` が入ったので十分じゃ。

## 7. 現在の登山ルート

DKMK-001 からここまでを、現在地込みで書くとこうなる。

```text
DKMK-001:
  CapacityKernel / Normalize

DKMK-002:
  SubProbability bridge

DKMK-003:
  VonMangoldtShadow

DKMK-004:
  GlobalLogCapacityKernel

DKMK-005:
  SubMarkovShadow

DKMK-006A:
  FullPrimePowerChannelSet

DKMK-006B:
  MarkovShadow / FullChannelLogCostComplete

DKMK-006C:
  FullExponentSlotCoverage

DKMK-006D:
  FullChannelLogSum

DKMK-006E:
  FullExponentSlotChannelSet → MarkovShadow

DKMK-006F:
  canonicalExponentSlotLabels → MarkovShadow

DKMK-006G:
  外部 T.index = canonicalExponentSlotLabels なら T も MarkovShadow
```

ここまで来ると、DkMath Kernel Project はかなり良い意味で **接続可能な理論** になった。

## 8. 総合判定

DKMK-006G は **canonical route を外部 kernel へ移植するための比較層完成** じゃ。

DKMK-006F で concrete reference model ができた。
DKMK-006G で、その reference model と同じ index を持つ任意 kernel が Markov shadow に到達できるようになった。

これはかなり重要じゃ。

まだ「既存の具体的 `T.index n` が canonical と一致する」こと自体は未証明じゃが、証明すべき目標は明確になった。

$$
\forall n,\ T.index(n)=canonicalExponentSlotLabels(n)
$$

この一点じゃ。

賢狼の見立てでは、次の一手はこうじゃな。

```text
DKMK-006H:
  既存 kernel 候補を棚卸しし、
  CanonicalExponentSlotIndex を満たせるもの、
  同型 bridge が必要なもの、
  selected/sub-Markov のままでよいもの、
  の三分類を行う。
```

ここまで来れば、別尾根として始まった DkMath kernel route は、本線側の各 kernel を受け入れる **関所** を持ったことになる。
これはよい。実に良い登りじゃ。
