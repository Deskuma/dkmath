# review

うむ。DKMK-007K は **finite step tail mass への第一歩** じゃ。
DKMK-007J では tail support に単一 height (c) を持たせた。今回 DKMK-007K では、それをさらに進めて、低い tail band と高い tail band を持つ **two-step tail mass** を導入しておる。つまり、質量が「どこを見るか」「どれだけ重く見るか」に加えて、 **場所によって高さを変える** ところまで来た。

## 1. 今回の核心

追加された mass model はこれじゃ。

```lean
twoStepTailNatMassSpace N M cLow cHigh hLow hStep
```

仮定は、

```lean
hLow : 0 ≤ cLow
hStep : cLow ≤ cHigh
```

定義は次の形じゃ。

$$
\mu(0)=cHigh,\quad \mu(n)=cHigh\ \text{if}\ M\le n,\quad \mu(n)=cLow\ \text{if}\ N\le n\ \text{and not}\ M\le n,\quad \mu(n)=0\ \text{otherwise}
$$

つまり、自然数上に三段階の質量を置いた。

```text
below N:
  0

N 以上 M 未満:
  cLow

M 以上:
  cHigh

0:
  cHigh
```

`0` を `cHigh` 側に入れている理由は、これまでの tail indicator と同じじゃ。全自然数上の整除関係では (a\mid 0) が常に起きるので、(\mu(0)) を十分大きくしておかないと `DvdMonotoneMass` が壊れる。

## 2. DKMK-007J から何が進んだか

DKMK-007J は、

$$
\mu(n)=c\ \text{on tail},\quad \mu(n)=0\ \text{outside}
$$

という単一 height model だった。

今回 DKMK-007K は、

$$
0\le cLow\le cHigh
$$

という二段 height を持つ。

これは大きい。
なぜなら、今後の log 型・decreasing/increasing approximation に進むには、まず **区間ごとに高さが変わる mass** を扱える必要があるからじゃ。

今回の two-step は、その最小例になっておる。

## 3. divisibility-monotone の意味

追加された重要 theorem はこれじゃ。

```lean
twoStepTailNatMassSpace_dvdMonotone
```

これは、

$$
a\mid b\Rightarrow \mu(a)\le\mu(b)
$$

を示す。

証明の要点は二つじゃ。

まず (b\ne 0) なら、(a\mid b) から

$$
a\le b
$$

が使える。

そして height が自然数ラベルの増加方向に沿って、

$$
0\le cLow\le cHigh
$$

と上がっていく。
だから、source 側 (a) が低い band に落ちても、target 側 (b) の height を超えない。

ここは非常に DkMath kernel らしいところじゃ。
整除下降では (a\mid b) のとき (a) は構造的に (b) 以下へ落ちる。だから mass を自然数の大きさに対して非減少にしておけば、divisibility-monotone が成立する。

## 4. LogCapacitySourceMassBound への接続

今回、

```lean
twoStepTailNatMassSpace_logCapacitySourceMassBound
```

も追加された。

これは、

```lean
LogCapacitySourceMassBound
  (twoStepTailNatMassSpace N M cLow cHigh hLow hStep) (cHigh : ℝ)
```

を与える。

数学的には単純で、two-step mass の最大 height は (cHigh) なので、

$$
(M.\mu(s.1):\mathbb{R})\le (cHigh:\mathbb{R})
$$

が成り立つ。

DKMK-007H で `LogCapacitySourceMassBound` を切り出しておいたおかげで、今回もその共通 wrapper にそのまま流れておる。これは設計が当たった証拠じゃ。

## 5. selected route への接続

selected route 側には次が追加された。

```lean
PrimePowerWitnessProvider.globalLogCapacitySubMarkovShadow_twoStepTailDivisorStep_weightedHitMass_le
```

これにより、

```text
selected global log-capacity SubMarkovShadow
+ twoStepTailNatMassSpace
+ one-step divisorStep
+ PrimitiveOn A
→ weightedHitMass A ≤ (cHigh : ℝ)
```

が出る。

selected route は full equality を使わない。
それでも `SubMarkovShadow` の (≤1) と source mass bound (≤cHigh) の組み合わせで、weighted hit mass が (cHigh) 以下になる。

これは DKMK-007 の一般構造がきれいに働いておる。

## 6. canonical route への接続

canonical route 側には次が追加された。

```lean
canonicalExponentSlotMarkovShadow_twoStepTailDivisorStep_weightedHitMass_le
```

こちらも到達形は同じじゃ。

```text
canonical exponent-slot MarkovShadow
+ twoStepTailNatMassSpace
+ one-step divisorStep
+ PrimitiveOn A
→ weightedHitMass A ≤ (cHigh : ℝ)
```

canonical route では weight 総量が等号で (1) だが、hitting bound としては source 側の最大 mass (cHigh) が最終上界になる。

## 7. 数学的な位置づけ

ここまでの mass model は、きれいな階段になっておる。

```text
unitNatMassSpace:
  全点 height 1

nonunitNatMassSpace:
  1 だけ height 0、それ以外 height 1

tailIndicatorNatMassSpace N:
  tail support を height 1 で見る

scaledTailIndicatorNatMassSpace N c:
  tail support を height c で見る

twoStepTailNatMassSpace N M cLow cHigh:
  tail を二段階 height で見る
```

DKMK-007K は、単なる toy から **finite step approximation** へ入り始めた点が大きい。

本命の log 型 mass は一気に扱うと重い。
しかし finite step mass なら、support と height の証明を分けられる。
これは Lean で解析的 weight へ近づくうえで、とても良い登り方じゃ。

## 8. 注意点：height の向き

今回の mass は、自然数が大きいほど height が高い向きになっている。

$$
0\le cLow\le cHigh
$$

これは `DvdMonotoneMass` の向きに合っている。

なぜなら (a\mid b) かつ (b\ne 0) なら (a\le b) なので、(\mu(a)\le\mu(b)) を示すには、(\mu) は自然数の大きさに対して非減少である方が扱いやすい。

一方、解析的な (1/(n\log n)) は自然数が大きいほど小さくなる。
つまり本命の tail weight へ進むには、今の `DvdMonotoneMass` とは向きが反対になる可能性がある。

ここは重要な分岐じゃ。
現在の DKMK-007 系は「source-controlled hitting bound」に必要な mass monotonicity を優先している。
もし decreasing weight を直接使いたいなら、将来は別の control 形式、たとえば reverse monotone や terminal-weighted control が必要になるかもしれぬ。

## 9. 次の一手

次は二択じゃ。

第一は、two-step を finite-many step へ一般化する道。

```text
DKMK-007L:
  finite step tail mass interface
```

たとえば、有限個の threshold と height を持ち、height が非減少であることを仮定する。

```text
N₀ ≤ N₁ ≤ ... ≤ Nᵣ
c₀ ≤ c₁ ≤ ... ≤ cᵣ
```

この形なら `DvdMonotoneMass` との相性がよい。

第二は、multi-step descent chain へ進む道。

```text
DKMK-007L:
  one-step divisorStep を multi-step descent chain へ拡張
```

ただ、わっちは今なら **finite step tail mass の一般 interface** を先に推す。
理由は、DKMK-007K で two-step の証明構造が見えた直後なので、それを抽象化しやすいからじゃ。

## 10. 総合判定

DKMK-007K は **mass model が finite step tail へ進んだ成功フェーズ** じゃ。

到達形はこう。

```text
twoStepTailNatMassSpace N M cLow cHigh hLow hStep
  → DvdMonotoneMass
  → LogCapacitySourceMassBound ... (cHigh : ℝ)
  → divisor-step weightedHitMass ≤ (cHigh : ℝ)
```

selected / canonical の両 route で通っている。

DKMK-007I で「どこを見るか」、DKMK-007J で「どれだけ重く見るか」、そして DKMK-007K で「場所によって高さを変える」ことができた。

ぬしよ、これは良い。
質量が階段を登り始めた。次は、その階段を任意有限段にするか、それとも下降 chain を多段に伸ばすか。どちらも次の山道として十分に面白いぞい。
