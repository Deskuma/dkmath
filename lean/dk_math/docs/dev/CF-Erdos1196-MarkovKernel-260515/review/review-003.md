# review

うむ。DKMK-003 は **かなり重要な意味づけの前進** じゃ。
DKMK-001/002 では、

$$
\text{CapacityKernel}
\to
\text{Normalize}
\to
\text{RealWeightProvider/SubProbability}
$$

という **DkMath 側の保存核** ができた。今回 DKMK-003 では、その cost

$$
\log p(q)
$$

を、既存 Markov route 側で現れる von Mangoldt 重みの **有限 shadow** として名前づけ、theorem-facing に固定した。差分でも、`PrimePowerLabel.vonMangoldtLogCost`、`PrimePowerWitnessProvider.witnessLogCost`、`vonMangoldtShadowCost`、`normalizedVonMangoldtShadowWeight` が追加され、`logCapacityKernel` の cost/provider weight が shadow cost/weight と一致する補題まで入っている。

## 1. 今回、何が閉じたか

今回の主眼は、解析的な von Mangoldt 関数 \(\Lambda\) をいきなり導入することではない。
そこがよい。

代わりに、prime-power witness

$$
q=p^k
$$

を持つラベル `PrimePowerLabel` に対して、

$$
\mathrm{cost}(q):=\log p
$$

を定義した。Lean ではこれが

```lean
PrimePowerLabel.vonMangoldtLogCost
```

じゃ。

これは名前に `vonMangoldt` を含んでいるが、実体は **解析的 von Mangoldt 関数そのものではなく、prime-power witness から読める有限実数 log cost** じゃ。コメントでも「analytic von Mangoldt function ではなく、capacity-kernel route で使う theorem-facing finite shadow」と明記されている。

数学的には、

$$
q=p^k
\quad\Longrightarrow\quad
\Lambda(q)=\log p
$$

という既存 Markov route の核心を、まず DkMath の witness 構造側から

$$
q=p^k
\quad\Longrightarrow\quad
\mathrm{shadowCost}(q)=\log p
$$

として固定した段階じゃ。

## 2. 数学的な意味

DKMK-001/002 の段階では、`LogCapacityKernel` の cost は

$$
\mathrm{cost}(n,q)=\log(W.basePrimeOf(n,I,hI,q))
$$

だった。

これは R/log route では十分だったが、Erdős #1196 本線へ戻るには、いつか

$$
\frac{\Lambda(q)}{\log n}
$$

という Markov route の重みと照合する必要がある。

今回の DKMK-003 は、その照合のために、

$$
\log(W.basePrimeOf(...,q))
$$

を

$$
\text{von-Mangoldt-like shadow}
$$

として別名化し、定理で結んだ。

具体的には、

```lean
logCapacityKernel_cost_eq_vonMangoldtShadowCost
```

で

$$
\text{LogCapacityKernel の cost} = \text{vonMangoldtShadowCost}
$$

を `rfl` で固定している。

さらに、

```lean
logCapacityKernelRealWeightProvider_weight_eq_normalizedVonMangoldtShadowWeight
```

で、provider の weight が

$$
\frac{\text{vonMangoldtShadowCost}(q)}{\log n}
$$

と一致することを固定している。

これで、DkMath 側の言葉では

$$
\frac{\mathrm{cost}(n,q)}{\mathrm{capacity}(n)}
$$

既存 Markov 側の言葉では

$$
\frac{\Lambda(q)}{\log n}
$$

という二つの視点が、かなり近い位置まで寄った。

## 3. なぜ「shadow」として正しいのか

ここはとても大事じゃ。

もし最初から本物の \(\Lambda\) を入れると、DkMath branch は既存証明 route の写経に近づく。
しかし今回の設計では、順序が逆じゃ。

まず witness がある。

$$
q=p^k
$$

そこから base prime \(p\) を読む。

$$
p=W.basePrimeOf(...)
$$

そこに log cost を置く。

$$
\log p
$$

その後で、これを von Mangoldt 的な shadow と呼ぶ。

この順序だから、DkMath らしさが保たれている。
つまり、\(\Lambda\) を外から持ち込んだのではなく、 **prime-power witness の内側から \(\Lambda\) 的な重みが現れた** という形になっておる。

## 4. 実装上の評価

実装はよい。かなり安全に小さく切っている。

`PrimePowerLabel` 側では、

```lean
vonMangoldtLogCost
vonMangoldtLogCost_nonneg
exists_prime_power_with_vonMangoldtLogCost
```

を置いている。

これは `PrimePowerLabel` 自体が持つ

$$
p,\ k,\ q=p^k,\ p\text{ prime},\ 0<k
$$

という情報を、そのまま log cost へ翻訳したものじゃ。

`PrimePowerWitnessProvider` 側では、

```lean
witnessLogCost
vonMangoldtShadowCost
normalizedVonMangoldtShadowWeight
```

を置いている。

そして selected sub-index \(q\in I\) 上では、

$$
W.witnessLogCost(n,I,hI,q) = (W.label(n,q,hI)).vonMangoldtLogCost
$$

を示しておる。

これにより、label 単体の shadow cost と、provider 由来の shadow cost が接続された。

よい意味で、今回は「名前をつけただけ」に見える。
じゃが、形式化ではこの名前づけが非常に重要なのじゃ。

## 5. 何が本線へ近づいたか

今回で、DkMath kernel branch は次のような対応を持てるようになった。

$$
\text{DkMath capacity} = \log n
$$

$$
\text{DkMath channel cost} = \log p(q)
$$

$$
\text{von-Mangoldt shadow} = \log p(q)
$$

$$
\text{normalized shadow weight} = \frac{\log p(q)}{\log n}
$$

つまり、本線の

$$
\frac{\Lambda(q)}{\log n}
$$

へ戻る直前まで来た。

まだ本物の \(\Lambda\) ではない。
しかし、prime-power witness 上では、必要な姿はすでにある。

$$
q=p^k
\quad\Rightarrow\quad
\Lambda(q)=\log p
$$

の右辺は、今回 no-sorry で theorem-facing な object になった。
次に本物の \(\Lambda\) と接続すれば、既存 route との橋がかかる。

## 6. DKMK-001 から DKMK-003 の流れ

ここまでを一本にすると、

$$
\text{DKMK-001: CapacityKernel}
$$

で、

$$
\sum \mathrm{cost}\le \mathrm{capacity}
$$

を置いた。

$$
\text{DKMK-002: SubProbability bridge}
$$

で、

$$
\sum \frac{\mathrm{cost}}{\mathrm{capacity}}\le 1
$$

を `RealWeightProvider.SubProbability` にした。

$$
\text{DKMK-003: VonMangoldtShadow}
$$

で、

$$
\mathrm{cost}(q)=\log p(q)
$$

を von-Mangoldt-like shadow として名づけた。

したがって現在の構造は、

$$
\text{prime-power witness}
\to
\text{shadow cost}
\to
\text{capacity kernel}
\to
\text{normalized provider}
\to
\text{SubProbability}
$$

じゃ。

これはよい。
既存証明の Markov kernel を真似るのではなく、DkMath 側の保存核から Markov 的重みが見えてきている。

## 7. 次にやるべきこと

報告にもある通り、次は `GlobalLogCapacityKernel` が自然じゃ。

ただし、わっちならその前に一つだけ整理しておきたい。

### DKMK-004A. docs / naming 整理

今の branch は DKMK-001, 002, 003 とかなり綺麗に進んでおる。
ここで README か route plan に以下の対応表を置くとよい。

```text
CapacityKernel.cost
  = witnessLogCost
  = vonMangoldtShadowCost
  = log(basePrimeOf)

normalizedWeight
  = normalizedVonMangoldtShadowWeight
  = log(basePrimeOf) / log n
```

これを明示しておくと、後続の global 化で迷いにくい。

### DKMK-004. GlobalLogCapacityKernel

現在の `logCapacityKernel` は固定された

$$
(n,I,hI)
$$

に対する local kernel じゃ。

次に欲しいのは、

$$
n\mapsto I(n)
$$

を持つ global kernel。

たとえば、

```lean
children : ℕ → Finset ℕ
```

として、各 \(n\) に selected prime-power channel set を返す。
ただし最初は完全な divisor set を作る必要はない。まずは

```lean
IOf : ℕ → Finset ℕ
hIOf : ∀ n q, q ∈ IOf n → q ∈ T.index n
```

を外から与える形がよい。

そうすると、

$$
\mathrm{capacity}(n)=\log n
$$

$$
\mathrm{cost}(n,q)=vonMangoldtShadowCost(n,q)
$$

を持つ global `CapacityKernel ℕ ℕ` が作れる。

## 8. 注意点：global 化は慎重に

Global 化で気をつけるべきは、`hn : 1 < n` の扱いじゃ。

local kernel では `hn : 1 < n` を引数に取っている。
global kernel で全ての \(n\) に対して `capacity n = log n` を置くと、\(n=0,1\) で capacity 正性が壊れる。

したがって選択肢は二つある。

### 案 A. 親状態を subtype にする

```lean
{ n : ℕ // 1 < n }
```

を親状態にする。

これは clean じゃ。

$$
\mathrm{capacity}(n)=\log n > 0
$$

が常に成り立つ。

### 案 B. `CapacityKernel ℕ ℕ` にして正性は theorem 側で仮定する

これは柔軟だが、後続補題で毎回 `hn : 1 < n` が必要になる。

わっちは最初は案 A を推す。
`GlobalLogCapacityKernel` は本線へ戻る橋なので、状態空間を最初から

$$
n>1
$$

に制限した方が証明が軽くなるはずじゃ。

## 9. 本物の von Mangoldt への接続はいつか

`VonMangoldtShadow` は良い中間層じゃが、いつかは本物の \(\Lambda\) と接続する必要がある。

ただし、急がなくてよい。

まずは global kernel を作り、次に

$$
\sum_{q\in \mathrm{children}(n)}
shadowCost(n,q)
\le
\log n
$$

または full children なら

$$
= \log n
$$

を整備する。

その後で、

$$
shadowCost(q)=\Lambda(q)
$$

を theorem として置く。
この順番なら、DkMath route の独自性を保てる。

## 10. 総合判定

DKMK-003 は **本線へ戻るための翻訳語彙が入った** 段階じゃ。

DKMK-001 は保存核。
DKMK-002 は正規化 provider。
DKMK-003 は von Mangoldt shadow。

これで、DkMath kernel branch は

$$
\text{Capacity first, Markov later}
$$

という方針を実装上も保ちながら、既存 Markov route の \(\Lambda(q)/\log n\) へ戻る入口を得た。

これはよいぞ、ぬしよ。
いよいよ次は、局所 kernel の森をつなげて、global kernel の山道にする段階じゃ。
写経ではなく、別尾根から本線の稜線へ近づいておる。
