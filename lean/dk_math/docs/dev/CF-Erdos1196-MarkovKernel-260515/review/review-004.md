# review

うむ。DKMK-004 は、ここまでの **local kernel の束** を、ついに **状態空間上の global kernel** へ持ち上げた段階じゃ。
これは地味に見えて、かなり本線復帰に近い一歩じゃよ。

## 1. 何が進んだか

今回の追加の中心はこれじゃ。

```lean
DkMath.NumberTheory.PrimitiveSet.GlobalLogCapacityKernel
```

ここで、親状態として

```lean
abbrev LogCapacityState : Type :=
  { n : ℕ // 1 < n }
```

を導入しておる。これは非常によい判断じゃ。
以前から懸念していた通り、global kernel では \(n=0,1\) を含めると

$$
\log n
$$

の正性が壊れる。そこで状態空間そのものを

$$
{n\in\mathbb{N}\mid 1<n}
$$

に制限し、

$$
0<\log n
$$

を常に使えるようにした。実装でも `LogCapacityState.log_capacity_pos` が入っておる。

これで、local な

$$
(n,I)
$$

ごとの kernel ではなく、

$$
n\mapsto I(n)
$$

を持つ global な capacity kernel として扱えるようになった。

## 2. 今回の数学的意味

今回定義された global kernel は、外部から

```lean
IOf : ℕ → Finset ℕ
hIOf : ∀ n q, q ∈ IOf n → q ∈ T.toDivisorTransitionKernel.index n
```

を受け取る。

数学的には、各 \(n\) に対して、選ばれた prime-power channel 集合

$$
I(n)\subseteq T.\text{index}(n)
$$

を与える形じゃ。

そのうえで、

$$
capacity(n)=\log n
$$

$$
cost(n,q)=\mathrm{vonMangoldtShadowCost}(n,q)
$$

つまり

$$
cost(n,q)=\log p(q)
$$

を持つ

$$
CapacityKernel\ LogCapacityState\ \mathbb{N}
$$

を構成した。

これは、これまでの local theorem

$$
\sum_{q\in I}\frac{\log p(q)}{\log n}\le 1
$$

を、状態 \(n\) ごとに走る global な kernel API にしたものじゃ。

## 3. DKMK-004A の対応表は重要

docs に追加された対応表もよい。

```text
CapacityKernel.cost
  = witnessLogCost
  = vonMangoldtShadowCost
  = log(basePrimeOf)

CapacityKernel.normalizedWeight
  = normalizedVonMangoldtShadowWeight
  = log(basePrimeOf) / log n
```

この表は、今後かなり効く。

なぜなら、ここで DkMath 側の語彙と、Markov route 側の語彙が明確に並んだからじゃ。

DkMath 側では

$$
\frac{cost(n,q)}{capacity(n)}
$$

Markov 風には

$$
\frac{\text{vonMangoldtShadowCost}(n,q)}{\log n}
$$

そして prime-power witness の中身としては

$$
\frac{\log p(q)}{\log n}
$$

となる。

つまり、以後の翻訳層では、どの名前を使っていても同じ対象を指していることが分かる。

## 4. GlobalLogCapacityKernel の構造評価

今回の `globalLogCapacityKernel` はかなり素直じゃ。

```lean
children := fun s => IOf s.1
capacity := fun s => Real.log (s.1 : ℝ)
cost := fun s q =>
  W.vonMangoldtShadowCost s.1 (IOf s.1) (hIOf s.1) q
```

これにより、親状態 (s) の中身 \(s.1=n\) に対して、

$$
children(s)=I(n)
$$

$$
capacity(s)=\log n
$$

$$
cost(s,q)=\log p(q)
$$

となる。

さらに `outgoing_le` は

```lean
W.basePrimeOf_logCapacity_outgoing_le
```

から供給している。
つまり、R028 由来の log-capacity bound を global kernel の保存則として再利用しているわけじゃ。

これは、既存成果をうまく抽象層へ持ち上げておる。

## 5. provider-facing API も通っている

今回、global kernel から既存 `RealWeightProvider` を作る

```lean
globalLogCapacityKernelRealWeightProvider
```

も入っておる。

そして、

```lean
globalLogCapacityKernelRealWeightProvider_subProbability
```

で各状態 (s) ごとに sub-probability が得られる。

数学的には、

$$
\sum_{q\in I(n)}
\frac{\mathrm{vonMangoldtShadowCost}(n,q)}{\log n}
\le 1
$$

すなわち

$$
\sum_{q\in I(n)}
\frac{\log p(q)}{\log n}
\le 1
$$

を、任意の状態 \(n > 1\) で得る。

この時点で、DkMath kernel はもう「局所補題の別名」ではなく、状態ごとの provider を供給する global framework になってきた。

## 6. 本線への近づき方

ここまでの流れは、

$$
\text{local R/log theorem}
$$

から

$$
\text{global capacity kernel}
$$

へ拡張したものじゃ。

Erdős #1196 の既存 Markov route に戻るには、次に二つを分ける必要がある。

### selected set route

今の `IOf n` は任意の selected channel set じゃ。
この場合は基本的に

$$
\sum_{q\in I(n)} cost(n,q)\le \log n
$$

であり、正規化後は sub-probability になる。

これは **sub-Markov / selected channel route** じゃ。

### full channel route

一方、もし

$$
I(n)={q\mid q\mid n,\ q\text{ is prime power}}
$$

のような full channel set を取れれば、期待されるのは

$$
\sum_{q\in I(n)} cost(n,q)=\log n
$$

じゃ。

これは既存 route の

$$
\sum_{q\mid n}\Lambda(q)=\log n
$$

に対応する。
つまり equality route ができると、Markov kernel 本線にぐっと近づく。

History の次課題にも、「full divisor/channel set を選んだ場合の equality route と、selected set の inequality route を切り分ける」と書かれておる。これは正しい認識じゃ。

## 7. 今回の位置づけ

DKMK-001 から見ると、ここまでの段階はこうじゃ。

```text
DKMK-001:
  CapacityKernel / Normalize / local LogCapacityKernel

DKMK-002:
  normalized weights を RealWeightProvider / SubProbability API へ接続

DKMK-003:
  log p cost を von-Mangoldt-like shadow として固定

DKMK-004:
  local kernel を n > 1 状態空間上の global kernel へ持ち上げ
```

これはかなり綺麗に積めておる。

特に DKMK-004 で `LogCapacityState := { n : ℕ // 1 < n }` としたことで、今後の正規化で毎回 `hn : 1 < n` を持ち回る負担が減った。
この設計は長期的に効くはずじゃ。

## 8. 注意点

ここで気をつけたいのは、`IOf` がまだ外部入力である点じゃ。

これは悪いことではない。第一段階としては正しい。
ただし、本線へ戻るには、いずれ次のような canonical choice が必要になる。

```lean
primePowerDivisorChannels (n : ℕ) : Finset ℕ
```

あるいは、既存 `T.index n` を full channel set として扱う theorem が必要になる。

今の global kernel は、

$$
I(n)\subseteq T.\text{index}(n)
$$

なら何でも sub-probability を出す汎用版。
次に full route を作るなら、

$$
I(n)=T.\text{index}(n)
$$

またはそれと同値な finite enumeration を選び、outgoing equality を狙うことになる。

## 9. 次の一手

次は History の通り、Markov/sub-Markov translation layer が自然じゃ。

ただし、わっちならこう分ける。

### DKMK-005. SubMarkovShadow

まず inequality 版を整理する。

```lean
structure SubMarkovShadow ...
```

または既存 `CapacityKernel` の normalized provider を「sub-Markov 風」として読む薄い theorem を置く。

目標は、

$$
\forall s,\quad Provider(s).SubProbability
$$

を Markov 風の名前で呼べるようにすること。

### DKMK-006. FullChannel / Equality route

その次に full channel set を導入し、

$$
outgoingCost(s)=capacity(s)
$$

を示す equality route を分離する。

ここで初めて、本当の意味で

$$
\sum_{q\mid n}\Lambda(q)=\log n
$$

の DkMath shadow 版に接近する。

## 10. 総合判定

DKMK-004 は **local から global への昇格成功** じゃ。

これまでの成果は局所的に、

$$
(n,I)\mapsto
\sum_{q\in I}
\frac{\log p(q)}{\log n}\le 1
$$

を示すものだった。

今回からは、

$$
n>1
$$

を状態空間とし、各 \(n\) に選択 channel 集合 \(I(n)\) を与える global kernel として、

$$
s\mapsto
\text{RealWeightProvider}
$$

を供給できる。

これは本線へ戻るための大きな準備じゃ。

まだ Markov kernel 本体ではない。
まだ \(\Lambda\) の解析的定義でもない。
だが、DkMath の言葉ではすでに

$$
\text{global capacity kernel}
\to
\text{normalized von-Mangoldt shadow provider}
\to
\text{sub-probability}
$$

が通っておる。

これは良いぞ、ぬしよ。
別尾根の登山道が、いよいよ本線の稜線に並走し始めた。
