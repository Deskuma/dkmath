# Report

うむ、ここまでの登頂を総括しよう。
結論から言えば、 **Erdős #1196 に向かう DkMath 内の有限 R/log route は、一つの山として登頂した** 。ただし、 **Erdős #1196 全体の解析的山頂** 、つまり

$$
\sum_{\substack{a\in A\ a > x}}\frac{1}{a\log a}
\le
1+O!\left(\frac{1}{\log x}\right)
$$

まで Lean で閉じた、という意味ではまだない。今回閉じたのは、その手前にある **有限 prime-power witness から log 質量が 1 を超えないことを出す中核ルート** じゃ。

## 1. 最初の地図：DkMath の世界観

初期資料では、DkMath は単なる補題集ではなく、宇宙式・動的調和数論・スケーリング・単位核・指数対数変換を中心に据えた研究ライブラリとして整理されていた。AGENT では、指数対数 (e^k \leftrightarrow e_k)、相対多角数、単位核 (u^d)、宇宙式 ((P+u)^2=P^2+2Pu+u^2)、そして ((x+u)^n) 型の defect 構造までが開発対象に含まれると記されている。

また、リポジトリ全体の構成マップでは、DkMath は `CosmicFormula`、`NumberTheory`、`ABC`、`FLT`、`RH`、`KUS` など複数の柱を持つ構造として整理されていた。特に `DiffPow`、`BinomTail`、`GcdDiffPow`、`ZsigmondyCyclotomic` が、冪差・gcd・原始素因子を扱う数論幹線として位置づけられている。

この段階で、山の形はすでに見えていた。
DkMath は「個別問題を直接叩く」のではなく、

$$
\text{宇宙式分解}
\to
\text{Tail / GN}
\to
\text{valuation}
\to
\text{mass / flow}
\to
\text{bridge}
$$

という層構造で攻める設計だったわけじゃ。

## 2. 宇宙式側の土台：Big / Body / Gap と Tail

宇宙式側では、まず

$$
\mathrm{Big}=(x+u)^d,\qquad
\mathrm{Gap}=u^d,\qquad
\mathrm{Body}=(x+u)^d-u^d
$$

という Big / Body / Gap の分解が基礎として整理された。トロミノ資料では、2次元では

$$
(x+u)(y+v)-uv=xy+xv+uy
$$

となり、Body が 3 要素、Gap が 1 要素として現れることが確認されていた。これは「トロミノ 3 要素 + 余白 1 要素」という宇宙式の幾何的原型じゃ。

一方、高次 Tail 構造では、

$$
(x+u)^d-
\sum_{j=0}^{r-1}\binom{d}{j}x^j u^{d-j} =
x^r GN_d^{(r)}(x,u)
$$

という一般化 GN 多項式が定義され、(x^r) が境界因子、(GN_d^{(r)}) が内部 Tail として読めるようになった。特に (r=1) が標準 GN であり、

$$
(x+u)^d-u^d=x,GN_d(x,u)
$$

となる。

ここで大事なのは、後の valuation / mass route の語彙がすでに芽吹いていたことじゃ。

$$
\text{境界因子}
\quad+\quad
\text{内部質量}
\quad+\quad
\text{valuation}
$$

という見方は、この Tail 構造から自然に出ている。

## 3. Mass API の構想：保存則から劣保存則へ

次に、宇宙式の

$$
\mathrm{Big}=\mathrm{Body}+\mathrm{Gap},
\qquad
\mathrm{Body}=\mathrm{Core}+\mathrm{Beam}
$$

を、単なる代数恒等式ではなく質量保存則

$$
\mu(\mathrm{Big}) =
\mu(\mathrm{Body}) +
\mu(\mathrm{Gap})
$$

として読む設計が立った。さらに、分岐では

$$
\sum_{\text{child}}\mu(\text{child})
\le
\mu(\text{parent})
$$

という劣保存則を API 化する方針が示された。

この設計は、後の Erdős route に直接つながる。

なぜなら primitive set の議論では、割り切りの下降過程に沿って質量が分配され、その総量が親を超えないことを示す必要があるからじゃ。ここで宇宙式の「保存則」が、数論の「sub-probability」へ橋を架ける。

## 4. 中間登山：primitive hitting と path family

過去の中間まとめでは、Phase A から Phase S までで、primitive set に対する有限 skeleton が整備されていた。

最初に、primitive set は divisibility chain 上で高々一度しか hit しない、という有限 combinatorial core が作られた。そこから、single chain、finite chain family、forest へ拡張され、

$$
\mathrm{hitMass}\le \mathrm{sourceMass}
$$

型の評価が得られるようになった。

さらに、下降路として

$$
n\mapsto \frac{n}{p}
$$

を扱う prime descent path が整備され、`AdjacentPrimePath` や path family を通じて、実際の有限下降列から source-controlled chain family を作れるようになった。

その後、Mass API の `SubConservative` route と、整除単調性に基づく `DvdMonotoneMass` route が合流し、weighted path family まで拡張された。これにより、

$$
\sum_i w_i\cdot \mathrm{hitMass}_i
\le
\sum_i w_i\cdot \mathrm{sourceMass}_i
$$

という有限重み付き評価が整った。

この段階は、まさに **Markov / 解析重みへ入る直前の前衛キャンプ** じゃった。

## 5. R/log 登山の開始：finite log weight へ

その後、Erdős #1196 の重み

$$
\frac{1}{a\log a}
$$

へ直接行く前に、有限 log route として

$$
\frac{\log p}{\log n}
$$

型の重みを扱う方針に入った。

この発想は、prime-power divisor witness

$$
q=p^k
$$

を通じて、(n) の内部にある素因子チャネルを読み、base prime (p) に log weight を与えるものじゃ。

この route の基本目標は、

$$
\sum_{q\in I}
\frac{\log p(q)}{\log n}
\le 1
$$

を有限集合 (I) について示すことだった。

当初は重複なし route、つまり (p(q)) が pairwise distinct である場合に限って進めていた。しかし、それでは prime-power labels (p,p^2,p^3,\dots) を自然に扱えない。そこで R021 以降、重複あり route へ進んだ。

## 6. R021-R028：重複あり finite R/log route の登頂

ここが今回の主峰じゃ。

R021 では、同じ base prime が複数回現れる場合には、pairwise distinct ではなく valuation budget で管理すべきだと整理した。

R022 では、そのための語彙として

$$
\mathrm{NatBaseMultiplicityOn}
$$

$$
\mathrm{NatBaseMultiplicityBudgetOn}
$$

が導入された。これは

$$
\#{q\in I\mid p(q)=p}
\le
n.\mathrm{factorization}(p)
$$

を表すものじゃ。

R023 では、この multiplicity budget から

$$
\prod_{q\in I}p(q)\mid n
$$

を導いた。

R024 では、それを

$$
\prod_{q\in I}p(q)\le n
$$

へ変換し、さらに

$$
\sum_{q\in I}\frac{\log p(q)}{\log n}\le 1
$$

すなわち `SubProbability` へ接続した。

R025 では、抽象 (pOf) を `PrimePowerWitnessProvider.basePrimeOf` に特殊化し、witness provider 由来の route にした。

R026 では、base prime だけでなく exponent reader

$$
k(q):=W.\mathrm{baseExponentOf}(n,I,hI,q)
$$

を導入し、

$$
q=p(q)^{k(q)}
$$

$$
0<k(q)
$$

$$
k(q)\le n.\mathrm{factorization}(p(q))
$$

を固定した。

R027 では、同じ base prime (p) を持つ labels を exponent slot

$$
1,2,\dots,n.\mathrm{factorization}(p)
$$

へ単射で入れた。つまり、

$$
q\mapsto k(q)
$$

が同一 base-prime fiber 上で単射であることを使い、

$$
\#{q\in I\mid p(q)=p}
\le
n.\mathrm{factorization}(p)
$$

を自動生成した。

最後に R028 で、README や route plan が更新され、推奨入口が

```lean
PrimePowerWitnessProvider.basePrimeOf_logRatioSubProbability
```

として明示された。R028 の資料でも、この theorem は `I ⊆ T.index n` と `1 < n` だけから、(q\mapsto \log(W.basePrimeOf\ n\ I\ hI\ q)/\log n) が `SubProbability` であることを示す、と整理されている。

## 7. 登頂で見えた数学的風景

山頂から見えた世界はこうじゃ。

整数

$$
n=\prod_p p^{v_p(n)}
$$

を考える。各素数 (p) は、縦方向に

$$
1,2,\dots,v_p(n)
$$

という exponent slot を持っている。

prime-power witness label は

$$
q=p^k
$$

なので、同じ (p) を持つ label は、その (p)-塔の (k) 番目の棚に置かれる。

同じ (p) かつ同じ (k) なら、同じ (q) である。
だから同じ棚に二つの異なる label は入れない。

ゆえに、

$$
\#{q\in I\mid p(q)=p}\le v_p(n)
$$

となる。

これを全ての (p) で合わせると、

$$
\prod_{q\in I}p(q)\mid n
$$

が出て、

$$
\sum_{q\in I}\log p(q)\le\log n
$$

となり、最後に (1<n) なので (\log n>0) で割って、

$$
\sum_{q\in I}
\frac{\log p(q)}{\log n}
\le 1
$$

となる。

これは「同じ素数が重複すると困る」のではなく、 **同じ素数が重複するなら exponent slot に並べればよい** という発見じゃ。
この発想で、重複あり finite log route が自然に閉じた。

## 8. 宇宙式との接続も見え始めた

別資料では、Erdős route 側の prime-power label

$$
q=p^k
$$

を宇宙式側の

$$
\mathrm{Big}(d;x,u)=(x+u)^d
$$

と対応させるなら、

$$
p=x+u,\qquad k=d,\qquad q=(x+u)^d
$$

が自然だと整理されていた。つまり、(x+u) が素数なら、

$$
q=p^k=(x+u)^d=\mathrm{Big}(d;x,u)
$$

として読める。

これは今回の R/log route と相性がよい。

R/log route では (q=p^k) を prime-power witness として読み、base prime (p) に log weight を与える。
宇宙式側では ((x+u)^d) が Big であり、もし (x+u) が prime なら Big 全体が prime-power channel になる。

つまり、今回の登頂で見えたのは、

$$
\text{宇宙式 Big}
\quad\leftrightarrow\quad
\text{prime-power witness}
\quad\leftrightarrow\quad
\text{log mass channel}
$$

という稜線じゃ。

## 9. 何が完了し、何が未完か

今回、 **完了** と言えるのは次じゃ。

$$
I\subseteq T.\mathrm{index}(n),\quad 1<n
$$

から、

$$
\sum_{q\in I}
\frac{\log W.\mathrm{basePrimeOf}(n,I,hI,q)}
{\log n}
\le 1
$$

を no-sorry で出す finite repeated-base R/log route。

これは R028 で公開導線にも反映され、推奨入口も明確になった。

一方、まだ **未完** なのは、Erdős #1196 全体の解析層じゃ。

具体的には、

$$
\sum_{\substack{a\in A\ a > x}}\frac{1}{a\log a}
\le
1+O!\left(\frac{1}{\log x}\right)
$$

へ進むには、有限 log sub-probability を、

* primitive set の hitting mass
* Markov / sub-Markov kernel
* tail estimate
* (1/(a\log a)) 型の解析的重み
* (1+O(1/\log x)) の漸近評価

へ接続する必要がある。

過去の中間まとめでも、Markov kernel や解析的質量 (\mu(n)=1/(n\log n)) はまだ未実装であり、有限 skeleton が整った段階だと整理されていた。

## 10. 今回の登頂の価値

今回の価値は、単に「補題が増えた」ことではない。

価値は、DkMath 内に次の原理が Lean theorem として定着したことじゃ。

$$
\text{prime-power divisor witnesses}
\Longrightarrow
\text{finite log sub-probability}
$$

しかも重複ありで成立する。

これは、Erdős #1196 の核心思想である

$$
\text{割り切り構造}
\to
\text{下降過程}
\to
\text{質量が 1 を超えない}
$$

を、有限・形式化可能・再利用可能な形にしたものじゃ。

この山を登ったことで、次からは「同じ素数が複数回現れる問題」に悩まなくてよい。
それはすでに exponent slot の理論で処理済みじゃ。

## 11. 次の稜線

次に進むなら、わっちは次の順を勧める。

まず、R021-R028 の成果を `PrimitiveSet` の上位 API から使えるようにする。
つまり `basePrimeOf_logRatioSubProbability` を、finite/log route の標準入口にする。

次に、これを primitive hitting / weighted path family と合流させる。
既に weighted finite sum は準備されているので、そこへ real/log provider の `SubProbability` を接続するのが自然じゃ。

最後に、Markov kernel と解析的重みへ進む。
ここで初めて、

$$
\frac{1}{a\log a}
$$

の本丸へ近づく。

## 12. 総括

ここまでの道のりは、こう言える。

最初は、宇宙式の Big / Body / Gap、Tail / GN、Mass API、primitive hitting という複数の尾根が別々に見えていた。
それが、R/log route で

$$
q=p^k
$$

という一点に集まり、base prime (p)、exponent (k)、factorization budget、log mass が一本の鎖になった。

そして R027-R028 で、

$$
\text{外部 budget 仮定}
$$

が消え、

$$
I\subseteq T.\mathrm{index}(n),\quad 1<n
$$

だけで finite log `SubProbability` が出るところまで閉じた。

これは登頂じゃ。
ただし、連峰全体の最高峰ではなく、 **有限 R/log 稜線の主峰** じゃな。

山頂から見える次の世界は、Erdős #1196 の解析峰。
そこへ続く尾根はもう見えておる。

わっちは少し誇ってよいと思うぞ、ぬしよ。
ここまでの登りは、ただの実装ではない。 **数論の割り切り構造を、質量保存の言葉へ翻訳する登山** だったのじゃ。
