# report #009

## DKMK-001 to 006[A-D]

うむ、ここまでを一度きれいに束ねよう。
DKMK-001 から DKMK-006D までで、DkMath Kernel branch は **「Markov kernel を写経する」のではなく、「DkMath の capacity / cost / valuation slot から Markov 的構造を生成する」** ところまで、かなり明確な形になった。

結論から言えば、ここまでで閉じたのは次の稜線じゃ。

$$
\text{CapacityKernel}\to\text{SubMarkovShadow}\to\text{MarkovShadow}
$$

そして number theory 側では、

$$
\text{prime-power witness}\to\text{vonMangoldtShadowCost}\to\text{log-capacity equality}
$$

まで、ほぼ一本の道になった。

## 1. DKMK-001：CapacityKernel の立ち上げ

最初の一歩では、Markov kernel を直接定義せず、まず `CapacityKernel` を置いた。

考え方はこうじゃ。

$$
\sum_{b\in children(a)}\mathrm{cost}(a,b)\le \mathrm{capacity}(a)
$$

つまり、確率ではなく **容量保存・劣保存** を先に置く。
ここで `children`、`capacity`、`cost`、`cost_nonneg`、`outgoing_le` を持つ抽象構造を作り、正規化前の DkMath kernel の核を固定した。

この段階で、合言葉はすでに定まっていた。

$$
\text{Capacity first, Markov later.}
$$

## 2. DKMK-002：SubProbability bridge

次に、`CapacityKernel` の normalized weights を、既存の `RealWeightProvider / SubProbability` API に接続した。

追加された中心は、

```lean
normalizedRealWeightProvider
normalizedRealWeightProvider_totalWeight
normalizedRealWeightProvider_subProbability
```

じゃ。これは positive-capacity parent に対して、正規化 weight を既存の finite real provider として包装するものじゃった。差分でも、`CapacityKernel` の normalized weights を既存 `RealWeightProvider` / `SubProbability` API へ接続したと記録されておる。

数学的には、

$$
\sum \mathrm{cost}\le \mathrm{capacity}
$$

から、

$$
\sum \frac{\mathrm{cost}}{\mathrm{capacity}}\le 1
$$

を得る一般橋じゃ。

この段階で、DkMath kernel は単なる抽象構造ではなく、既存の weighted path / hitting 側へ接続可能な部品になった。

## 3. DKMK-003：VonMangoldtShadow

DKMK-003 では、prime-power witness 由来の

$$
\log p
$$

を theorem-facing な von-Mangoldt-like shadow として固定した。

追加された主な入口は、

```lean
PrimePowerLabel.vonMangoldtLogCost
PrimePowerWitnessProvider.witnessLogCost
PrimePowerWitnessProvider.vonMangoldtShadowCost
PrimePowerWitnessProvider.normalizedVonMangoldtShadowWeight
```

じゃ。報告にも、これは解析的 von Mangoldt 関数へ直接進まず、prime-power witness 由来の `log p` channel cost を finite shadow として固定するものだと書かれておる。

数学的には、

$$
q=p^k
$$

から base prime \(p\) を読み、

$$
\mathrm{vonMangoldtShadowCost}(q)=\log p
$$

とする。

ここで重要なのは、\(\Lambda(q)\) を先に持ち込んでいないことじゃ。
DkMath 的には、まず witness があり、そこから \(\log p\) が出る。既存 Markov route の \(\Lambda(p^k)=\log p\) は、その後に現れる影として扱う。

## 4. DKMK-004：GlobalLogCapacityKernel

DKMK-004 では、local な \((n,I)\) kernel を、状態空間上の global kernel へ持ち上げた。

親状態は、

```lean
LogCapacityState := { n : ℕ // 1 < n }
```

じゃ。これにより、すべての状態で

$$
0<\log n
$$

が保証される。差分でも、`LogCapacityState := { n : ℕ // 1 < n }` と `globalLogCapacityKernel` が追加され、local kernel から `n > 1` 状態空間上の global kernel へ拡張されたと記録されておる。

この global kernel は、外部から

```lean
IOf : ℕ → Finset ℕ
hIOf : ∀ n q, q ∈ IOf n → q ∈ T.toDivisorTransitionKernel.index n
```

を受け取り、

$$
\mathrm{children}(n)=IOf(n)
$$

$$
\mathrm{capacity}(n)=\log n
$$

$$
\mathrm{cost}(n,q)=\mathrm{vonMangoldtShadow\mathrm{cost}}(n,q)
$$

を定義する。

これで、状態 \(n > 1\) ごとに finite log-capacity route を走らせる global framework ができた。

## 5. DKMK-005：SubMarkovShadow

DKMK-005 では、selected channel / inequality route を `SubMarkovShadow` として切り出した。

`SubMarkovShadow` は状態ごとに有限 index と非負 weight を持つ構造で、

$$
\forall s,\quad \sum_{i\in \mathrm{index}(s)}\mathrm{weight}(s,i)\le 1
$$

を `SubProbability` として扱う。

報告では、selected channel route の inequality 側を Markov 風に読める sub-Markov shadow 語彙として切り出した、と整理されている。

ここで大事なのは、full channel ではなく selected channel の場合、等号ではなく不等号が自然だということじゃ。

$$
I(n)\subseteq \mathrm{Full}(n)
$$

なら、

$$
\sum_{q\in I(n)}\frac{\mathrm{cost}(n,q)}{\log n}\le 1
$$

となる。
これが `SubMarkovShadow`。

この時点で、DkMath kernel は、

```text
CapacityKernel
  保存核

SubMarkovShadow
  正規化された劣確率影

RealWeightProvider
  既存 finite weight API
```

という三層を持つようになった。

## 6. DKMK-006A：FullPrimePowerChannelSet

DKMK-006A では、full equality route に入る前提として、full channel set の interface を分離した。

追加された中心は、

```lean
FullPrimePowerChannelSet
```

じゃ。これは、

```lean
channels : ℕ → Finset ℕ
subset_index : ∀ n q, q ∈ channels n → q ∈ T.toDivisorTransitionKernel.index n
full : ∀ n q, q ∈ T.toDivisorTransitionKernel.index n → q ∈ channels n
```

を持つ。つまり、

$$
C.\text{channels}(n)=T.\text{index}(n)
$$

を外延的に表す。報告でも、`channels n` が `T.toDivisorTransitionKernel.index n` と同じ finite channel set であることを `subset_index` / `full` で表す interface と説明されている。

この段階ではまだ、

$$
\sum_{q\in \mathrm{Full}(n)}\mathrm{cost}(n,q)=\log n
$$

は主張しない。
「full channel を選んだ」という条件だけを分離したのが DKMK-006A じゃ。

## 7. DKMK-006B：MarkovShadow と FullChannelLogCostComplete

DKMK-006B では、等号側の語彙 `MarkovShadow` と、full channel 上の log-cost completeness interface を追加した。

`MarkovShadow` は `SubMarkovShadow` に

$$
\mathrm{totalWeightAt}(s) = 1
$$

を加えたものじゃ。報告にも、`MarkovShadow` は `SubMarkovShadow` に `totalWeightAt = 1` を加えた equality 側の語彙だと明記されておる。

また、

```lean
FullChannelLogCostComplete
```

は、

$$
\sum_{q\in C.\text{channels}(n)}\mathrm{vonMangoldtShadowCost}(n,q)=\log n
$$

を仮定 interface として切り出したものじゃ。

この段階の成果は、

$$
\text{FullChannelLogCostComplete}\to \text{MarkovShadow}
$$

を no-sorry で閉じたこと。

つまり、full channel の log-cost equality が供給されれば、正規化 kernel は Markov shadow へ昇格できる。

## 8. DKMK-006C：FullExponentSlot

DKMK-006C では、full equality を将来証明するため、exponent slot coverage の interface を追加した。

中心は、

```lean
NatBaseMultiplicityCompleteOn
FullExponentSlotChannelSet
FullExponentSlotCoverage
```

じゃ。報告では、selected route の `≤` budget に対して、full route 用の `=` multiplicity 条件を入れたと説明されている。

数学的には、selected route では、

$$
# {q\in I\mid p(q)=p}\le n.\mathrm{factorization}(p)
$$

だった。
full route ではこれを、

$$
# {q\in \mathrm{Full}(n)\mid p(q)=p}=n.\mathrm{factorization}(p)
$$

に強める。

これが `NatBaseMultiplicityCompleteOn`。

また `FullExponentSlotChannelSet` は、

$$
q\in C.\text{channels}(n)\leftrightarrow \exists p,k,\ p\text{ prime}\land 1\le k\land k\le n.\mathrm{factorization}(p)\land q=p^k
$$

を表す仕様じゃ。

これで、full channel が「全 exponent slot」を表すための語彙が整った。

## 9. DKMK-006D：FullChannelLogSum

DKMK-006D はここまでの中で、かなり大きな接続じゃ。

追加された中心は、

```lean
FullChannelLogSum.lean
```

であり、

```lean
sum_log_base_eq_sum_image_multiplicity_mul_log
sum_factorization_mul_log_eq_log_nat
fullExponentSlotCoverage_sum_log_base_eq_log_nat
fullChannelLogCostComplete_of_fullExponentSlotCoverage
```

が入った。

報告では、`FullExponentSlotCoverage` から `FullChannelLogCostComplete` を導く有限和/log の橋を追加した、と整理されている。

数学的には、まず有限和を fiber ごとにまとめる。

$$
\sum_{q\in I}\log(p(q))=\sum_{p\in I.\text{image}(p)}\#{q\in I:p(q)=p}\log p
$$

次に、full coverage により、

$$
\#{q\in \mathrm{Full}(n):p(q)=p}=n.\mathrm{factorization}(p)
$$

へ置き換える。

さらに、

$$
\sum_{p\in n.\mathrm{factorization.support}}n.\mathrm{factorization}(p)\log p=\log n
$$

を使う。

これにより、

$$
\text{FullExponentSlotCoverage}\to \text{FullChannelLogCostComplete}
$$

が no-sorry で閉じた。

そして DKMK-006B と合成すれば、

$$
\text{FullExponentSlotCoverage}\to \text{MarkovShadow}
$$

まで届く。

## 10. ここまでの全体構造

ここまでで、DkMath kernel branch は次の構造を得た。

```text
CapacityKernel
  Σ cost ≤ capacity

Normalize / RealWeightProvider
  weight = cost / capacity

SubMarkovShadow
  selected channel route
  Σ weight ≤ 1

FullPrimePowerChannelSet
  full channel route の対象指定

FullChannelLogCostComplete
  Σ cost = capacity

MarkovShadow
  full channel equality route
  Σ weight = 1

FullExponentSlotCoverage
  full channel の multiplicity = factorization

FullChannelLogSum
  FullExponentSlotCoverage から FullChannelLogCostComplete へ接続
```

つまり、最初の標語だった

$$
\text{Markov kernel is a normalized shadow of DkMath capacity kernel.}
$$

が、今では Lean の構造としてかなり明確になった。

## 11. 何が完了したか

完了したのは、次の橋じゃ。

$$
\text{CapacityKernel}\to\text{SubMarkovShadow}
$$

$$
\text{FullChannelLogCostComplete}\to\text{MarkovShadow}
$$

$$
\text{FullExponentSlotCoverage}\to\text{FullChannelLogCostComplete}
$$

したがって、

$$
\text{FullExponentSlotCoverage}\to\text{MarkovShadow}
$$

の道がほぼ通った。

つまり、 **全 exponent slot coverage が得られれば、DkMath kernel は Markov equality へ昇格する** ところまで閉じた。

## 12. 何がまだ未完か

残る本丸は一つに絞られた。

$$
\text{FullExponentSlotCoverage}
$$

そのものを、canonical/full channel enumeration からどう供給するか。

報告でも、次の課題は `FullExponentSlotCoverage` 自体を canonical/full channel enumeration から供給できるか確認すること、必要なら explicit slot \((p,k)\) 形式の補助 interface を追加することだと書かれておる。

つまり未踏部分は、

$$
\text{canonical full channels}\to\text{all exponent slots are filled}
$$

じゃ。

ここが閉じれば、DkMath kernel branch は既存 Markov route の核心等式、

$$
\sum_{q\mid n}\Lambda(q)=\log n
$$

に対応する DkMath 版を、自前の言葉で再構成したことになる。

## 13. 数学的な意味

ここまでの成果は、既存 Markov kernel の単なる再実装ではない。

既存 route は、

$$
\Lambda(q)
$$

を主語にして、

$$
\sum_{q\mid n}\Lambda(q)=\log n
$$

を見る。

DkMath route は、

$$
q=p^k
$$

という prime-power witness から始め、

$$
\mathrm{cost}(q)=\log p
$$

を定義し、

$$
\sum \mathrm{cost}\le \mathrm{capacity}
$$

を `CapacityKernel` として見て、

$$
\frac{\mathrm{cost}}{\mathrm{capacity}}
$$

を正規化影として `SubMarkovShadow` / `MarkovShadow` にする。

つまり、

$$
\Lambda
$$

は最初から置かれた関数ではなく、

$$
\text{prime-power witness の log cost}
$$

として現れる。

ここが DkMath らしい新開拓路じゃ。

## 14. 次のおすすめ

次は二択じゃ。

第一に、既存 `T.index n` が本当に full exponent slot set になっているかを調べる。
もしそうなら、それを証明して `FullExponentSlotCoverage` を供給する。

第二に、explicit slot set を別に作る。

$$
(p,k),\quad p\in n.\mathrm{factorization.support},\quad 1\le k\le n.\mathrm{factorization}(p)
$$

を Finset として構成し、そこから \(q=p^k\) へ写す。

わっちは第二案を先に少し推す。
slot 形式なら、

$$
\sum_p\sum_{k=1}^{v_p(n)}\log p=\sum_p v_p(n)\log p
$$

が自然に出るからじゃ。
その後、label \(q=p^k\) 側へ bridge すればよい。

## 15. 総括

DKMK-001 から DKMK-006D までで、DkMath Kernel branch は **構想段階から、Markov equality 直前の形式化構造** まで進んだ。

今の地図はこうじゃ。

```text
DkMath capacity route:
  cost / capacity を先に作る

Selected route:
  selected channels
  → SubMarkovShadow

Full route:
  full exponent-slot coverage
  → Σ cost = capacity
  → MarkovShadow
```

まだ最後の `FullExponentSlotCoverage` 供給は残っている。
しかし、そこから先の道はすでに舗装済みじゃ。

ぬしよ、これはかなり良い登山じゃ。
既存 Markov route のコピーではなく、DkMath の valuation slot と capacity kernel から、同じ稜線へ登る別尾根が形になってきた。
