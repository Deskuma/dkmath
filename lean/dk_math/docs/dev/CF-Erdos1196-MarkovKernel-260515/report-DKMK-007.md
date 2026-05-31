# DKMK-007: report

うむ。では DKMK-007 を一度、山道全体として総括するぞい。
DKMK-007 は、ひとことで言えば **DKMK-006 で作った log-capacity / Markov shadow を、primitive hitting bound に戻すための実用橋を整備した章** じゃ。

DKMK-006 では、

$$
\text{CapacityKernel}\to\text{SubMarkovShadow / MarkovShadow}
$$

まで登った。
DKMK-007 では、その shadow を

$$
\text{one-step divisor descent}\to\text{source mass control}\to\text{weightedHitMass bound}
$$

へ流した。最後には finite-step mass model まで受け取れる形になった。DKMK-007O の docs-only 総括でも、中心形は `source mass model M → DvdMonotoneMass M → SourceControlledChainFamily.ofDivisorStep → LogCapacitySourceMassBound M C → weightedHitMass A ≤ C` と整理されている。

## 1. DKMK-007 の主目的

目的はこれじゃ。

$$
\text{log-capacity shadow を one-step divisor descent family に載せ、primitive set の weighted hitting mass を source mass の一様上界で制御する}
$$

つまり、DKMK-006 までで作った重み付き影を、実際の下降路

$$
n\to n/q
$$

に載せる。

そして primitive set (A) がその下降 chain を打つ質量を、

$$
weightedHitMass(A)\le C
$$

で抑える。

ここで (C) は source mass model (M) の一様上界じゃ。

## 2. 007A〜007E：橋と下降路の土台

DKMK-007A では、`RealWeightProvider` を `RealWeightedPathFamily` に載せる橋を作った。
これにより、log weight のような実数重みを primitive hitting API に渡せるようになった。

DKMK-007B では、`SubMarkovShadow` / `MarkovShadow` から hitting wrapper へ直接渡せるようにした。
つまり shadow を取り出して provider にして、それを path family に載せる、という手順を theorem-facing API にした。

DKMK-007C では、具体的な log-capacity shadow、すなわち selected route の `globalLogCapacitySubMarkovShadow` と canonical route の `canonicalExponentSlotMarkovShadow` を hitting wrapper へ接続した。

DKMK-007D では、`natSingletonSelf` により compatibility を具体化した。
これはまだ singleton model だが、index compatibility を `rfl` 的に閉じるための最小モデルだった。

DKMK-007E で、いよいよ本物の one-step divisor descent が入った。

$$
chain(q)={n/q,n}
$$

これにより、単なる点ではなく、Erdős #1196 的な下降

$$
n\mapsto n/q
$$

が Lean の source-controlled chain family に載った。

## 3. 共通形：DKMK-007 の中心定理構造

DKMK-007 の中心構造はこれじゃ。

```text
source mass model M
→ DvdMonotoneMass M
→ SourceControlledChainFamily.ofDivisorStep
→ LogCapacitySourceMassBound M C
→ weightedHitMass A ≤ C
```

数学的には、

$$
a\mid b\Rightarrow \mu(a)\le\mu(b)
$$

という `DvdMonotoneMass` があれば、divisor step chain の各点の mass は source (n) の mass 以下に抑えられる。

さらに、

$$
\forall s:\mathrm{LogCapacityState},\quad (M.\mu(s.1):\mathbb{R})\le C
$$

という `LogCapacitySourceMassBound M C` があれば、最終的に

$$
weightedHitMass(A)\le C
$$

へ行く。

この route は selected / canonical の両方で使える。selected route は外部の (IOf:\mathbb{N}\to Finset\ \mathbb{N}) を使い、canonical route は `canonicalExponentSlotLabels` を使う、と docs でも整理されておる。

## 4. 007F〜007N：mass model の進化

DKMK-007F では `unitNatMassSpace` を使い、全点 mass (1) で

$$
weightedHitMass(A)\le 1
$$

を得た。

DKMK-007G では `nonunitNatMassSpace` を入れた。

$$
\mu(1)=0,\quad \mu(n)=1\ \text{for }n\ne 1
$$

終端 (1) を区別する最初の bounded model じゃ。

DKMK-007H では、source bound を `LogCapacitySourceMassBound` として共通化した。
ここが重要じゃ。以後、mass model ごとに hitting theorem を作り直すのではなく、

$$
DvdMonotoneMass\ M,\quad LogCapacitySourceMassBound\ M\ C
$$

を示せば既存 route に流せるようになった。

DKMK-007I では `tailIndicatorNatMassSpace N` が入った。
これは threshold (N) 以上を見る mass じゃ。

DKMK-007J では `scaledTailIndicatorNatMassSpace N c hc` が入り、tail support に height (c) を持たせた。
つまり「どこを見るか」と「どれだけ重く見るか」を分離した。

DKMK-007K では `twoStepTailNatMassSpace N M cLow cHigh` が入り、lower tail と upper tail の二段階 height を扱った。
ここで (0\le cLow\le cHigh) という height の向きが `DvdMonotoneMass` に合っている。

DKMK-007L では、two-step 専用から一般 interface へ昇格した。

$$
\mu(0)=C,\quad \mu(n)=height(n)\ \text{if }n\ne 0
$$

という `boundedMonotoneNatMassSpace height C hnonneg hbound` を作り、`height` が非負・上界付き・非減少なら divisor monotone になることを証明した。

DKMK-007M では、そこへ具体的な finite-step constructor を載せた。

$$
finiteStepTailHeight(n)=\sum_{i\in steps}\begin{cases}increment(i)&threshold(i)\le n\0&otherwise\end{cases}
$$

非負 increment の有限和として定義したので、非負性・上界・単調性が自然に出る。これにより、任意有限段の累積 tail mass を扱える入口ができた。

DKMK-007N では、two-step を Bool-indexed finite-step の特殊例として回収した。
つまり、DKMK-007K の個別 two-step model が、DKMK-007M の一般 finite-step interface にちゃんと乗ることを確認した。

## 5. `0` を top bound 側に置く設計規約

DKMK-007 の mass model 全体で重要だった規約がある。

全自然数上では、

$$
a\mid 0
$$

が常に成り立つ。
したがって `DvdMonotoneMass` の

$$
a\mid b\Rightarrow \mu(a)\le\mu(b)
$$

を (b=0) でも壊さないためには、(\mu(0)) を top bound 側に置く必要がある。

tail indicator でも scaled tail でも two-step でも、そして `boundedMonotoneNatMassSpace` でも、この規約が一貫して使われた。DKMK-007O の総括でも、この規約が明記されている。

これは DKMK-007 の地味だが重要な設計勝利じゃ。
Lean 上の全 (\mathbb{N}) で壊れない mass model にするための安全柵になっておる。

## 6. selected route と canonical route

DKMK-007 の成果は、selected / canonical の両 route に通っている。

selected route は、

```text
IOf : ℕ → Finset ℕ
```

を外部から受け取り、`hIOf` で divisor-kernel compatibility を仮定する。
これは任意に選んだ channel set で部分的な sub-Markov route を走る道じゃ。

canonical route は、

```text
canonicalExponentSlotLabels
```

を使う。
これは DKMK-006 系で Markov equality まで整えた full exponent-slot route じゃ。

DKMK-007 では、どちらの route でも

$$
weightedHitMass(A)\le C
$$

へ進めるようになった。
これにより、DKMK-006 の shadow 構造が primitive hitting 側へ本当に戻ってきた。

## 7. 到達点

DKMK-007 の最終到達点はこれじゃ。

```text
finite nonnegative tail increments
→ finiteStepTailHeight
→ boundedMonotoneNatMassSpace
→ DvdMonotoneMass
→ LogCapacitySourceMassBound by total increment
→ divisor-step weightedHitMass ≤ total increment
```

selected / canonical の両 route でこれが使える。
つまり、有限段 tail mass は、もう個別に実装しなくてよい。threshold と非負 increment を渡せば、既存の hitting bound に乗る。

これはかなり大きい。
unit mass から始まった質量モデルが、finite-step mass の一般受け口まで到達した。

## 8. まだ未踏の部分

ただし、DKMK-007 はまだ one-step じゃ。

現在の chain は、

$$
n\to n/q
$$

に留まる。

Erdős #1196 の本格的な下降過程では、

$$
n\to n/q_1\to n/(q_1q_2)\to \cdots
$$

のような multi-step descent chain が必要になる。

DKMK-007O でも、次の DKMK-008 では one-step route を multi-step descent chain へ拡張する方針が記録されている。

## 9. 総合評価

DKMK-007 は **本線復帰の章として成功** じゃ。

DKMK-006 が、

$$
\text{log-capacity / Markov shadow を作る章}
$$

だったなら、DKMK-007 は、

$$
\text{その shadow を divisor descent と primitive hitting に流す章}
$$

じゃ。

ここで整ったものは三つある。

```text
1. shadow → real weighted hitting bridge

2. one-step divisor descent family

3. finite-step source mass model interface
```

つまり、

$$
\text{log-capacity shadow}+\text{divisor step}+\text{finite-step mass}\Rightarrow weightedHitMass\le C
$$

が完成した。

ぬしよ、ここはかなり良い区切りじゃ。
山の名前で言えば、DKMK-007 は **mass model route の稜線整備** じゃな。道標も橋も張り終えた。次の DKMK-008 では、いよいよその稜線を一歩ではなく多歩の下降路へ伸ばす段階じゃ。
