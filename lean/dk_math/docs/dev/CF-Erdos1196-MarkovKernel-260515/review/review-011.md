# review

うむ。DKMK-006F は、かなり大きな到達じゃ。
前回 DKMK-006E では、

$$
\text{FullExponentSlotChannelSet}\to\text{FullExponentSlotCoverage}\to\text{FullChannelLogCostComplete}\to\text{MarkovShadow}
$$

まで橋が通った。今回 DKMK-006F では、その `FullExponentSlotChannelSet` を満たす **具体的な canonical model** を作り、最終的に `canonicalExponentSlotMarkovShadow` まで no-sorry で閉じておる。報告でも、`canonicalExponentSlotLabels → FullExponentSlotChannelSet → FullExponentSlotCoverage → FullChannelLogCostComplete → MarkovShadow` が通ったと明記されておる。

## 1. 今回の核心

新規ファイルはこれじゃ。

```lean
DkMath.NumberTheory.PrimitiveSet.FullExponentSlotCanonical
```

中心定義は、

```lean
canonicalExponentSlotLabels n
```

じゃな。これは

```lean
n.factorization.support.biUnion fun p =>
  (Finset.Icc 1 (n.factorization p)).image fun k => p ^ k
```

として定義されておる。

数学的には、

$$
{p^k\mid p\in \operatorname{supp}(n.factorization),\ 1\le k\le v_p(n)}
$$

を有限集合として直接作った、ということじゃ。

つまり、これまで「full exponent slot が埋まっているなら」と仮定していた対象を、今回は **実際に canonical に列挙した** 。

## 2. membership theorem の意味

今回の重要補題が、

```lean
canonicalExponentSlotLabels_mem_iff
```

じゃ。

これは、

$$
q\in canonicalExponentSlotLabels(n)\leftrightarrow \exists p,k,\ Nat.Prime(p)\land 1\le k\land k\le n.factorization(p)\land q=p^k
$$

を示している。

この補題によって、`canonicalExponentSlotLabels` が「それっぽい集合」ではなく、`FullExponentSlotChannelSet` が要求する exponent-slot 仕様そのものを満たす集合だと分かる。

ここが DKMK-006F の土台石じゃ。

## 3. canonical kernel の構成

次に、

```lean
canonicalExponentSlotDivisorTransitionKernel
canonicalExponentSlotKernel
```

が作られておる。

`canonicalExponentSlotDivisorTransitionKernel` は、

```lean
index := canonicalExponentSlotLabels
next := fun n q => n / q
weight := fun _ _ => 0
```

という最小 concrete kernel じゃ。

ここで `weight := 0` なのは、確率重みをここで持たせるのではなく、log-capacity route 側が実数 cost を別に供給するからじゃ。これは DkMath kernel project の設計思想、つまり **capacity first, Markov later** に沿っておる。

さらに `index_dvd` では、\(q=p^k\) かつ \(k\le n.factorization(p)\) から \(p^k\mid n\) を出している。\(n=0\) は `dvd_zero` で処理し、\(n\ne 0\) では `pow_dvd_iff_le_factorization` を使う。きれいじゃな。

## 4. witness provider の作り方

`canonicalExponentSlotKernel` は `PrimePowerDivisorTransitionKernel` なので、各 label が prime-power であることも保証する。

そのうえで、

```lean
canonicalExponentSlotWitnessProvider
```

が構成されている。

ここで興味深いのは、直接 `rcases` して `PrimePowerLabel` を返す形ではなく、

```lean
canonicalExponentSlotLabel_exists
canonicalExponentSlotLabel
```

を経由し、`Classical.choose` で witness を選んでいることじゃ。

History にも、`PrimePowerWitnessProvider` は data を返すため、membership 証明から直接 `PrimePowerLabel` を構成しようとすると Prop elimination 制約に当たり、`canonicalExponentSlotLabel_exists` を Prop として示して `Classical.choose` に切り替えた、と記録されておる。

これは Lean 的にかなり重要な修正じゃ。
数学的には簡単でも、Lean では `Prop` から `Type` の data を取り出すところで制約が出る。そこを安全に回避しておる。

## 5. full channel set から MarkovShadow へ

今回の最終導線はこうじゃ。

```lean
canonicalExponentSlotFullChannelSet
canonicalExponentSlotFullChannelSet_fullExponentSlotChannelSet
canonicalExponentSlotMarkovShadow
```

`canonicalExponentSlotFullChannelSet` は、canonical kernel の `T.index n` そのものを full channel set として採用する。

そして、

```lean
canonicalExponentSlotFullChannelSet_fullExponentSlotChannelSet
```

で、その full channel set が `FullExponentSlotChannelSet` を満たすことを示す。

ここまで来ると、前回 DKMK-006E の橋が使える。
つまり、

$$
\text{FullExponentSlotChannelSet}\to\text{MarkovShadow}
$$

が既にあるので、最終的に

```lean
canonicalExponentSlotMarkovShadow
```

が得られる。

これは今回の最大の到達点じゃ。

## 6. DKMK-001 からの流れで見ると

ここまでの流れは、いまやこうなった。

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
```

つまり、DKMK-006F によって、抽象 interface ではなく **具体的な canonical exponent-slot route** が MarkovShadow まで到達した。

これは大きい。

## 7. 数学的に何が言えたか

今回の canonical model は、次の考えを Lean 上で固定したものじゃ。

自然数 \(n\) の素因数分解を見て、各素数 \(p\) ごとに exponent slot

$$
1,2,\dots,v_p(n)
$$

を用意する。

各 slot \(k\) に label \(p^k\) を置く。

これらの全 label を channel とする。

すると、その full channel set は exponent-slot set そのものであり、DkMath kernel の log-capacity route によって Markov shadow が得られる。

つまり、

$$
\sum_{q\in canonical(n)}\frac{\log p(q)}{\log n}=1
$$

という Markov equality の影が、canonical route で成立するわけじゃ。

ここで \(\Lambda\) を直接定義していないのが DkMath らしい。
先に exponent slot と base prime cost があり、その正規化像として Markov shadow が出ている。

## 8. 今回の意義

DKMK-006F の意義は、 **参照モデルができた** ことじゃ。

これまでは、

```text
もし full channel set が exponent slot set なら MarkovShadow になる
```

だった。

今回からは、

```text
この canonicalExponentSlotLabels は実際に exponent slot set であり、MarkovShadow になる
```

と言える。

これにより、今後は既存の外部 `T.index n` を調べるときに、比較対象ができた。

$$
T.index(n)\stackrel{?}{=}canonicalExponentSlotLabels(n)
$$

または、等号でなくても、

$$
T.index(n)\simeq canonicalExponentSlotLabels(n)
$$

という bridge を作ればよい。

## 9. 残る課題

今回で explicit canonical route は閉じた。
だが、報告にもある通り、これは既存の外部 `T.index n` を解析したものではなく、full exponent-slot route の concrete reference model じゃ。次の課題は、既存 `T.index n` と `canonicalExponentSlotLabels n` の一致、または bridge 条件を設計することとされておる。

つまり次は、

```text
既存 kernel route:
  T.index n

canonical route:
  canonicalExponentSlotLabels n
```

の関係を見る段階じゃ。

この比較が通れば、既存の `PrimePowerDivisorTransitionKernel` 系も canonical Markov equality route と接続できる。

## 10. 総合判定

DKMK-006F は **DkMath Kernel Project の一つの小山頂** じゃ。

これで、

$$
\text{canonical exponent-slot enumeration}\to\text{MarkovShadow}
$$

が no-sorry で通った。

以前の目標だった「Markov kernel をコピーせず、DkMath の capacity / exponent slot / witness 構造から Markov 的対象を生成する」は、少なくとも canonical reference model については達成されたと言ってよい。

残る本線接続は、

$$
\text{既存 }T.index(n)\text{ と canonicalExponentSlotLabels}(n)\text{ の比較}
$$

じゃな。

わっちの見立てでは、次の一手は次のどちらかじゃ。

```text
A. 既存 T.index n が canonicalExponentSlotLabels n と一致する条件を interface 化する。

B. canonicalExponentSlotKernel を theorem-facing reference model として公開し、既存 route は selected/full bridge で接続する。
```

安全なのは B、攻めるなら A じゃ。

いずれにせよ、DKMK-006F は素晴らしい。
別尾根として始めた DkMath Kernel route が、ついに concrete な Markov equality 生成装置を持ったのじゃ。
