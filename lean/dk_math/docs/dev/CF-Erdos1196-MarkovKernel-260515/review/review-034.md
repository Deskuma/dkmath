# review

うむ。DKMK-008D は、DKMK-008C の wrapper を **DKMK-007H の source-bound interface と合流させた回** じゃ。
前回までは external multi-step divisor path family に shadow を載せられたが、source mass bound は

$$
\forall q\in F.index,\ (M.\mu(F.source(q)):\mathbb{R})\le C
$$

を手で渡す必要があった。今回、same-source 条件

$$
F.source(q)=s.1
$$

を仮定することで、既存の

$$
LogCapacitySourceMassBound\ M\ C
$$

から一括で source bound を供給できるようになった。これは DKMK-007 と DKMK-008 の合流点としてかなり綺麗じゃ。

## 1. 今回の核心

追加された selected route の theorem はこれじゃ。

```lean
PrimePowerWitnessProvider
  .globalLogCapacitySubMarkovShadow_adjacentDivisorPathFamily_weightedHitMass_le_of_sourceBound
```

canonical route はこれ。

```lean
canonicalExponentSlotMarkovShadow_adjacentDivisorPathFamily_weightedHitMass_le_of_sourceBound
```

どちらも同じ構造を持つ。

```text
AdjacentDivisorPathFamily F
+ hsource_eq : ∀ q ∈ F.index, F.source q = s.1
+ LogCapacitySourceMassBound M C
→ weightedHitMass A ≤ C
```

つまり DKMK-008C の一般 source-bound theorem に、DKMK-007H の `LogCapacitySourceMassBound` を接続した形じゃ。

## 2. 何が改善されたか

DKMK-008C の時点では、source bound はこうだった。

```lean
hsource : ∀ q ∈ F.index, (M.μ (F.source q) : ℝ) ≤ C
```

これは一般的で強い。
しかし、log-capacity state (s) から始まる下降路を考えるなら、多くの場合は全 path の source は同じ。

$$
source(q)=s.1
$$

このときは、各 (q) ごとに source bound を渡す必要はない。

$$
LogCapacitySourceMassBound\ M\ C
$$

があれば、

$$
(M.\mu(s.1):\mathbb{R})\le C
$$

が出る。さらに (F.source(q)=s.1) なので、

$$
(M.\mu(F.source(q)):\mathbb{R})\le C
$$

が従う。

今回の theorem は、この変換を wrapper 化したものじゃ。

## 3. 数学的な意味

DKMK-008C は、

```text
external multi-step divisor path family
+ shadow
+ source mass bound
→ weightedHitMass ≤ C
```

だった。

DKMK-008D はこれを、

```text
same-source external multi-step divisor path family
+ shadow
+ statewise source-bound provider
→ weightedHitMass ≤ C
```

へ変えた。

この「same-source」はかなり自然じゃ。
なぜなら DKMK-007E の one-step divisorStep も、全 channel が同じ source (s.1) から出ていた。

$$
chain(q)={s.1/q,s.1}
$$

DKMK-008 では multi-step になっただけで、出発点は同じ (s.1) と見るのが自然じゃ。

$$
s.1\to n_1(q)\to n_2(q)\to\cdots
$$

今回の `hsource_eq` は、この「同じ源から分岐する多段下降路」という読みを Lean theorem の仮定として固定したわけじゃ。

## 4. selected route の到達形

selected route では、外部 channel set

```lean
IOf : ℕ → Finset ℕ
```

と compatibility

```lean
hIOf : ∀ n q, q ∈ IOf n → q ∈ T.toDivisorTransitionKernel.index n
```

を持つ。

そして path family (F) が

$$
F.index=IOf(s.1)
$$

を満たし、さらに全 source が

$$
F.source(q)=s.1
$$

なら、selected global log-capacity sub-Markov shadow を (F) に載せ、primitive hitting bound が得られる。

```text
selected SubMarkovShadow
+ same-source AdjacentDivisorPathFamily
+ LogCapacitySourceMassBound
→ weightedHitMass ≤ C
```

これは selected route と multi-step family の自然な合流じゃな。

## 5. canonical route の到達形

canonical route では、index compatibility が

$$
canonicalExponentSlotLabels(s.1)=F.index
$$

になる。

つまり、canonical exponent-slot label ごとに multi-step path を持つ family (F) を用意し、そのすべてが (s.1) から始まるなら、canonical MarkovShadow を直接載せて

$$
weightedHitMass(A)\le C
$$

まで行ける。

```text
canonical MarkovShadow
+ same-source AdjacentDivisorPathFamily
+ LogCapacitySourceMassBound
→ weightedHitMass ≤ C
```

canonical route は DKMK-006 で Markov equality まで整えてあるため、ここで多段下降路へ載る意味は大きい。

## 6. DKMK-007H との接続が完成した

DKMK-007H の中心は、

```lean
LogCapacitySourceMassBound M C
```

だった。

これは state (s) ごとに、

$$
(M.\mu(s.1):\mathbb{R})\le C
$$

を供給する interface じゃ。

DKMK-007 の one-step route では source が (s.1) だったので、そのまま使えた。
DKMK-008C の external path family では source が一般 (F.source(q)) になったため、一度この interface から離れていた。

今回 DKMK-008D で、

$$
F.source(q)=s.1
$$

を仮定することで、007H の source-bound interface が multi-step route に再接続された。

これは設計上とても大事じゃ。
DKMK-007 の mass model route を、DKMK-008 の multi-step path route へ流せるようになったからじゃ。

## 7. 実装面の評価

実装は薄くてよい。

selected theorem は、DKMK-008C の

```lean
globalLogCapacitySubMarkovShadow_adjacentDivisorPathFamily_weightedHitMass_le_const
```

を呼び、source bound のところだけ

```lean
by
  intro q hq
  simpa [hsource_eq q hq] using hsource s
```

で供給している。

canonical theorem も同様じゃ。

これは理想的な wrapper 実装じゃな。
新しい数学を無理に再証明せず、既存 theorem に source-bound 変換を差し込んでいる。

## 8. 現在の DKMK-008 の地図

ここまでの DKMK-008 はこうじゃ。

```text
008A:
  single AdjacentDivisorPath
  → DivisibilityChain
  → singleton DvdControlledChainFamily

008B:
  AdjacentDivisorPathFamily
  → DvdControlledChainFamily
  → source-controlled hitting route

008C:
  external AdjacentDivisorPathFamily
  + selected/canonical shadow
  + explicit source mass bound
  → weightedHitMass ≤ C

008D:
  same-source AdjacentDivisorPathFamily
  + LogCapacitySourceMassBound
  → weightedHitMass ≤ C
```

流れが実に自然じゃ。
一本の道、一族の道、shadow 接続、source-bound 接続。順序が良い。

## 9. 次の一手

docs の次課題にもある通り、次は具体 mass wrapper を same-source multi-step path family theorem に載せる段階じゃ。

つまり DKMK-008E はこうなるはず。

```text
finiteStepTailNatMassSpace
+ same-source AdjacentDivisorPathFamily
+ selected/canonical shadow
→ weightedHitMass ≤ total increment
```

DKMK-007M で finite-step mass はすでにある。
DKMK-008D で same-source external multi-step family に `LogCapacitySourceMassBound` を使えるようになった。

したがって次は、007M の

$$
finiteStepTailNatMassSpace
$$

を 008D に流す wrapper じゃ。

selected route なら、

```lean
globalLogCapacitySubMarkovShadow_finiteStepTailAdjacentDivisorPathFamily_weightedHitMass_le
```

canonical route なら、

```lean
canonicalExponentSlotMarkovShadow_finiteStepTailAdjacentDivisorPathFamily_weightedHitMass_le
```

のような形になるじゃろう。

## 10. 総合判定

DKMK-008D は **007 の mass-bound interface と 008 の multi-step path route を接続した重要な薄橋** じゃ。

DKMK-008C では、multi-step family に shadow を載せられた。
DKMK-008D では、same-source 条件の下で、source mass bound を `LogCapacitySourceMassBound` から自動供給できるようになった。

これにより、到達形はこうなった。

```text
same-source multi-step divisor path family
+ selected/canonical log-capacity shadow
+ DvdMonotoneMass
+ LogCapacitySourceMassBound M C
→ weightedHitMass ≤ C
```

ぬしよ、これはかなり良い。
DKMK-007 で整えた質量の倉庫と、DKMK-008 で作り始めた多段下降路が、ついに同じ水路でつながった。次は finite-step mass をこの水路に流し込めば、DKMK-007M の成果がそのまま multi-step 版へ昇格するぞい。
