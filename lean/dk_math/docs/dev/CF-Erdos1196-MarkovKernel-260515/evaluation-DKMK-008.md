# evaluation

うむ。率直に言えば、 **この登山コースは、Erdős #1196 登頂へ向かう“DkMath 独自ルート”としてかなり有望** じゃ。
ただし、いま登れている山頂はまだ **有限・構造・Lean API 側の前衛峰** であって、Erdős #1196 の解析的主峰そのもの、すなわち

$$
\sum_{\substack{a\in A\a>x}}\frac{1}{a\log a}\le 1+O(1/\log x)
$$

を Lean で閉じたわけではない。ここは落ち着いて切り分ける必要がある。

## 1. 登頂できそうな理由

このコースの強みは、既存証明の Markov kernel をそのままコピーせず、DkMath の語彙で

```text
prime-power witness
→ base prime / exponent slot
→ quotient descent path
→ weightedHitMass bound
→ capacity kernel
```

へ組み替えているところじゃ。

既存証明風に言えば、中心は (\Lambda(q)/\log n) の確率核になる。だが DkMath route では、まず (q=p^k) を witness として読み、(\log p) を channel cost とし、(\log n) を parent capacity とする。つまり Markov kernel は最初から置かれるものではなく、capacity kernel の正規化像として現れる、という立場じゃ。この方針は以前の規格資料でも「Markov kernel is a normalized shadow of DkMath capacity kernel」と整理されておる。

そして R021–R028 で、有限 R/log route はかなり強く閉じている。特に重複ありの場合でも、同じ base prime (p) の labels を exponent slot に単射で入れて multiplicity budget を自動生成し、

$$
\sum_{q\in I}\frac{\log p(q)}{\log n}\le 1
$$

へ進める構造ができた。この有限 prime-power witness から log 質量が 1 を超えない中核ルートは、過去総括でも「一つの山として登頂した」と位置づけられている。

さらに DKMK-007 で finite-step mass を hitting bound へ載せ、DKMK-008 で descent path を one-step から multi-step path family へ拡張した。DKMK-008O では、manual path、one-step divisor path、witness-derived multi-step quotient path の三入口を持つ route として一区切りになった。

ここまで来ると、これは単なる周辺補題ではない。
**Erdős #1196 の「primitive set は divisibility chain を高々一度しか打てない」という核心を、DkMath の path / mass / capacity の三層で再構成している** と見てよい。

## 2. まだ足りないもの

一方で、本峰に必要なものはまだ残っておる。

今あるのは主に有限構造じゃ。

```text
finite selected labels
finite path family
finite-step mass
weightedHitMass bound
```

だが Erdős #1196 の本体は、尾部和

$$
\sum_{\substack{a\in A\a>x}}\frac{1}{a\log a}
$$

の漸近評価じゃ。そこへ行くには、有限 route を無限尾部・truncation・誤差評価へ接続する必要がある。

具体的には、次の三つが未踏じゃ。

第一に、DkMath capacity kernel から normalized sub-probability を一般 API として立てること。

$$
\sum_{q\in I}\mathrm{cost}(n,q)\le \mathrm{capacity}(n)
$$

から、

$$
\sum_{q\in I}\frac{\mathrm{cost}(n,q)}{\mathrm{capacity}(n)}\le 1
$$

を一般化し、R/log route と DKMK path route を同じ kernel 言語へ統合する必要がある。

第二に、(\frac{\log p}{\log n}) 型の finite channel weight と、最終的な (\frac{1}{a\log a}) 型の tail weight を橋渡しする必要がある。これは単なる代数補題ではなく、密度・尾部・近似評価の層じゃ。

第三に、(1+O(1/\log x)) の誤差評価が必要じゃ。これは finite Lean API だけでは届かぬ。Mertens 型評価、truncation、あるいは DkMath 風に言えば source mass の tail estimate を入れる必要がある。

## 3. 登山コースとしての判定

わっちの判定はこうじゃ。

```text
有限 combinatorial / capacity spine:
  かなり登れている

primitive hitting route:
  かなり強い

prime-power witness route:
  DkMath 独自色が出ている

Erdős #1196 の解析的尾部評価:
  まだ未登頂

全体として登頂可能性:
  かなり有望。ただし次の山は解析・近似・無限化
```

つまり、 **このルートで登頂は狙える** 。
ただし、いまのままではまだ「山頂直下の岩壁」ではなく、「山頂へ向かう独自稜線が本当に通っていることを確認した」段階じゃ。

既存証明を写すだけなら、(\Lambda(q)) と Markov kernel へ直行すればよい。
だが DkMath route は、

$$
q=p^k
$$

から、

```text
base prime
exponent slot
quotient path
capacity cost
hitting mass
```

を順に組み立てる。これは遠回りに見えて、Lean 形式化ではむしろ強い。各層が検証可能な小定理として分解されるからじゃ。

## 4. 次の最重要フェーズ

次は DKMK-009 として、 **CapacityKernel / DkMathKernel の抽象 API** を立てるのがよい。

目標はこれじゃ。

```text
CapacityKernel
  children
  capacity
  cost
  cost_nonneg
  outgoing_le
→ normalizedWeight
→ SubProbability
```

そのうえで、R028 の

$$
\sum_{q\in I}\log p(q)\le \log n
$$

を concrete `LogCapacityKernel` として載せる。

さらに DKMK-008 の witness-derived quotient path family を、この kernel の `children` / `path` 側に接続する。

すると次の形になる。

```text
prime-power witness
→ quotient path family
→ log-capacity cost
→ normalized sub-probability
→ primitive weightedHitMass bound
```

ここまで行けば、DkMath kernel route は「Markov kernel の代替解釈」ではなく、Lean 上の本体構造になる。

## 5. 最終的な見通し

登頂に必要な残りの道は、おそらくこうじゃ。

```text
DKMK-009:
  CapacityKernel / normalized sub-probability

DKMK-010:
  LogCapacityKernel concrete instance from prime-power witness

DKMK-011:
  tail / truncation source mass estimate

DKMK-012:
  finite theorem から tail primitive set statement への bridge

DKMK-013:
  1 + O(1/log x) 型の解析的 bound
```

最後の DKMK-013 は重い。
だが、そこへ行く前に 009〜012 を DkMath 的に閉じれば、既存証明の写経ではない **構造的な別登山路** になる。

## 6. 結論

うむ、ぬしよ。
この登山コースは **Erdős #1196 登頂を狙えるだけの骨格を持っている** 。

ただし、登頂の鍵はもう path を作ることではない。
DKMK-007 と 008 で、質量の器と下降路はできた。

次の鍵は、

```text
capacity をどう定義し、
正規化して sub-probability にし、
tail weight 1/(a log a) へどう橋を架けるか
```

じゃ。

いま見えている景色はこうじゃな。

```text
DKMK-007:
  質量の器

DKMK-008:
  下降路の地図

DKMK-009:
  容量核の本丸

その先:
  尾部解析の山頂
```

わっちは、このルートは十分に登る価値があると思う。
しかも、ただ登頂するだけではない。もし閉じれば、「Markov kernel を写した証明」ではなく、 **DkMath capacity kernel から Erdős #1196 が見える** という、かなり美しい独自景色になるぞい。
