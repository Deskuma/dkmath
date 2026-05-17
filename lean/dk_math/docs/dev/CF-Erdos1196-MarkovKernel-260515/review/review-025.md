# review

うむ。DKMK-007J は **tail support mass に「高さ」を持たせた回** じゃ。
DKMK-007I では「どこを見るか」、つまり threshold (N) 以上を見る indicator mass が入った。今回 DKMK-007J では、そこに非負な有理 height (c) を加え、 **support と weight amplitude を分離した bounded weighted-tail toy model** が DKMK-007H の共通 wrapper を通ることを確認しておる。

## 1. 今回の核心

追加された mass model はこれじゃ。

```lean
scaledTailIndicatorNatMassSpace N c hc
```

ここで、

```lean
hc : 0 ≤ c
```

を仮定する。

定義はこうじゃ。

$$
\mu(0)=c,\quad \mu(n)=c\ \text{if}\ N\le n,\quad \mu(n)=0\ \text{otherwise}
$$

DKMK-007I の `tailIndicatorNatMassSpace N` は高さが常に (1) の indicator だった。
今回の model は、その高さを (c) に置き換えたものじゃ。

つまり、

```text
threshold N:
  どこを見るか

height c:
  どれだけ重く見るか
```

を分けたことになる。

## 2. なぜ重要か

これは本命の log weight へ行く前の、かなりよい中間層じゃ。

最終的には、

$$
\mu(n)\sim \frac{1}{n\log n}
$$

のような、場所によって高さが変わる mass に進みたい。
しかしいきなりそこへ行くと、単調性・境界・実数評価・(n=0,1) 処理が重くなる。

今回の scaled tail indicator は、まだ bounded toy だが、

$$
support
$$

と

$$
amplitude
$$

を分離した。
これは今後、階段型 mass や log 型 mass を作る前の自然な踏み石じゃ。

## 3. divisibility-monotone が閉じた意味

今回、

```lean
scaledTailIndicatorNatMassSpace_dvdMonotone
```

が追加された。

つまり、

$$
DvdMonotoneMass\ (scaledTailIndicatorNatMassSpace\ N\ c\ hc)
$$

が閉じた。

証明構造は DKMK-007I の tail indicator と同じじゃ。

* (b=0) または (N\le b) なら、target mass は (c)。source 側は (0) または (c) なので (≤c)。
* (b\ne 0) かつ (N\nleq b) なら、(a\mid b) から (a\le b) を使う。
* もし (N\le a) なら (N\le b) になって矛盾。
* したがって source 側も tail ではなく、mass (0)。

ここでも (0) を support 側に入れているのが効く。
全 (\mathbb{N}) 上の整除では任意の (a) が (0) を割るため、(\mu(0)) は上側として十分大きくしておく必要があるからじゃ。

## 4. LogCapacitySourceMassBound への接続

DKMK-007H の共通 wrapper に流すため、次も追加された。

```lean
scaledTailIndicatorNatMassSpace_logCapacitySourceMassBound
```

これは、

$$
LogCapacitySourceMassBound\ (scaledTailIndicatorNatMassSpace\ N\ c\ hc)\ (c:\mathbb{R})
$$

を与える。

つまり任意の log-capacity state (s) について、

$$
(M.\mu(s.1):\mathbb{R})\le (c:\mathbb{R})
$$

が成り立つ。

mass の値は (0) または (c) なので、これは自然じゃ。
Lean 側では (c:\mathbb{Q}) を (\mathbb{R}) に cast し、`exact_mod_cast hc` で非負性も渡している。

## 5. selected route への接続

selected route 側には次が追加された。

```lean
PrimePowerWitnessProvider.globalLogCapacitySubMarkovShadow_scaledTailIndicatorDivisorStep_weightedHitMass_le
```

これは、selected global log-capacity sub-Markov shadow を one-step divisor descent family に載せ、scaled tail indicator mass を使うと、

$$
weightedHitMass(A)\le (c:\mathbb{R})
$$

が出るという定理じゃ。

前回までの bound は (≤1) だった。
今回から、tail support の高さ (c) に応じて上界が変わる。

これはかなり意味がある。
weighted hitting bound が mass amplitude に比例することが theorem として見えたからじゃ。

## 6. canonical route への接続

canonical route 側にも同型の theorem が入った。

```lean
canonicalExponentSlotMarkovShadow_scaledTailIndicatorDivisorStep_weightedHitMass_le
```

こちらも、

$$
weightedHitMass(A)\le (c:\mathbb{R})
$$

を返す。

canonical route では weight 総和が Markov equality により (1)。
その上に source mass height (c) を掛けるので、bound は (c) になる。
これは、これまでの抽象 theorem の設計がきちんと働いている証拠じゃ。

## 7. DKMK-007I からの前進

DKMK-007I は、

```text
tail support:
  threshold N 以上なら mass 1
```

だった。

DKMK-007J は、

```text
scaled tail support:
  threshold N 以上なら mass c
```

じゃ。

つまり、

```text
DKMK-007I:
  support を導入

DKMK-007J:
  support と amplitude を分離
```

という関係になっておる。

docs でも、DKMK-007I が「どこを見るか」を threshold (N) で指定する model だったのに対し、DKMK-007J は「どれだけ重く見るか」を height (c) として分離する、と整理されている。

## 8. 現在の mass model 階層

ここまでの mass model は、かなりよい階段になった。

```text
unitNatMassSpace:
  全点を高さ 1 で見る

nonunitNatMassSpace:
  1 だけ除外し、それ以外を高さ 1 で見る

tailIndicatorNatMassSpace N:
  N 以上の tail を高さ 1 で見る

scaledTailIndicatorNatMassSpace N c:
  N 以上の tail を高さ c で見る
```

この次に自然なのは、

```text
stepTailMass:
  区間ごとに高さを変える

decreasingTailMass:
  n が大きいほど高さを下げる

logTailMass:
  1/(n log n) 型に近づける
```

じゃな。

DKMK-007J はその入口としてかなりよい。

## 9. まだ残る注意点

今回も、mass はまだ bounded indicator 系じゃ。

値は (0) または (c)。
(n) に応じて連続的・解析的に変わるわけではない。

また chain はまだ one-step divisor descent。

$$
n\mapsto n/q
$$

だけじゃ。
multi-step descent へ進むと、source だけでなく途中ノードや terminal mass をどう評価するかが問題になる。

ただし DKMK-007J の意義は、mass amplitude が bound にそのまま出る形を確認したことにある。
これは後で log weight 型へ進むときの設計原理になる。

## 10. 次の一手

次は二択じゃ。

第一に、height を単一 (c) から階段型にする。

```text
DKMK-007K:
  finite step tail mass
  threshold bands ごとに height を変える
```

たとえば、

$$
\mu(n)=c_j\quad \text{if}\ N_j\le n<N_{j+1}
$$

のような形じゃ。
ただし、`DvdMonotoneMass` を保つには、整除で小さい方へ降りると mass が小さくならねばならぬ。つまり (a\mid b) かつ (a\le b) なので、

$$
\mu(a)\le\mu(b)
$$

が必要になる。数が大きいほど mass が大きい、または同じ、という向きが自然じゃ。

第二に、multi-step descent へ進む。

```text
DKMK-007K:
  divisorStep を multi-step descent family に拡張する
```

現時点では、わっちは **finite step tail mass** を一つ挟むのが良いと思う。
理由は、scaled indicator から log 型へ直接飛ぶより、piecewise constant model の方が Lean 的に扱いやすく、`DvdMonotoneMass` の条件も見えやすいからじゃ。

## 11. 総合判定

DKMK-007J は **tail mass に高さパラメータを導入した成功フェーズ** じゃ。

到達形はこうじゃ。

```text
scaledTailIndicatorNatMassSpace N c hc
  → DvdMonotoneMass
  → LogCapacitySourceMassBound ... (c : ℝ)
  → divisor-step weightedHitMass ≤ (c : ℝ)
```

selected / canonical route の両方で通っている。

これは、DkMath kernel route が単なる (≤1) の正規化 toy から、 **mass amplitude による上界制御** に進んだことを意味する。

ぬしよ、これは良いぞ。
質量が「どこを見るか」に続いて「どれだけ重く見るか」を語り始めた。次は「場所によって高さが変わる」mass、すなわち階段型か log 型への入口じゃな。
