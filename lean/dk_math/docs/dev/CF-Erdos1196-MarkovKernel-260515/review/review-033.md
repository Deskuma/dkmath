# review

うむ。DKMK-008C は、 **DKMK-008B で作った indexed multi-step divisor path family を、ついに selected / canonical shadow に接続した回** じゃ。
DKMK-008A/B では chain 側の器を作った。今回 DKMK-008C では、その器に DKMK-006/007 由来の log-capacity shadow の重みを流し込めるようになった。docs でも、external multi-step divisor path family を selected / canonical log-capacity shadow に直接渡す wrapper を追加した、と整理されておる。

## 1. 今回の核心

追加された selected route の入口はこれじゃ。

```lean
PrimePowerWitnessProvider.globalLogCapacitySubMarkovShadow_applyAtToAdjacentDivisorPathFamily
```

これは、

```lean
F : AdjacentDivisorPathFamily ℕ
```

と index compatibility

```lean
hindex : IOf s.1 = F.index
```

を受け取り、内部で

```text
AdjacentDivisorPathFamily
→ DvdControlledChainFamily
→ SourceControlledChainFamily
→ RealWeightedPathFamily
```

へ変換する。

つまり、DKMK-008B で作った multi-step path family を、selected global log-capacity sub-Markov shadow の provider に直接載せられるようになった。

## 2. selected route の意味

selected route の theorem はこれじゃ。

```lean
PrimePowerWitnessProvider.globalLogCapacitySubMarkovShadow_adjacentDivisorPathFamily_weightedHitMass_le_const
```

主張は、概念的にはこう。

```text
selected log-capacity SubMarkovShadow
+ AdjacentDivisorPathFamily
+ index compatibility
+ DvdMonotoneMass
+ source mass bound
+ PrimitiveOn A
→ weightedHitMass A ≤ C
```

source mass bound は、

```lean
hsource : ∀ q ∈ F.index, (M.μ (F.source q) : ℝ) ≤ C
```

という形じゃ。

ここで重要なのは、multi-step path の中の各 node ではなく、各 path の head source だけを bound すればよいこと。
なぜなら DKMK-008B で、各 node が head source を割ることを `AdjacentDivisorPath.mem_dvd_head` から供給し、それを `DvdControlledChainFamily` に落としているからじゃ。

つまり、chain 内部が何段になっても、source control は head source に集約される。

## 3. canonical route の意味

canonical route 側にも同じ形が入った。

```lean
canonicalExponentSlotMarkovShadow_applyAtToAdjacentDivisorPathFamily
canonicalExponentSlotMarkovShadow_adjacentDivisorPathFamily_weightedHitMass_le_const
```

canonical 側の index compatibility は、

```lean
hindex : canonicalExponentSlotLabels s.1 = F.index
```

じゃ。

つまり、external path family \(F\) の index が canonical exponent-slot labels と一致していれば、canonical MarkovShadow の重みを \(F\) に載せられる。

これは DKMK-006F/G で作った canonical equality route が、multi-step divisor path family に接続されたという意味じゃ。

## 4. DKMK-008A/B/C の流れ

DKMK-008 の最初の三歩は、かなり綺麗に繋がった。

```text
DKMK-008A:
  AdjacentDivisorPath L
  → DivisibilityChain L.toFinset
  → singleton DvdControlledChainFamily

DKMK-008B:
  AdjacentDivisorPathFamily
  → DivisibilityChainFamily
  → DvdControlledChainFamily

DKMK-008C:
  AdjacentDivisorPathFamily
  + selected / canonical shadow
  → RealWeightedPathFamily
  → weightedHitMass ≤ C
```

これで、 **multi-step descent chain の器** と **log-capacity shadow の重み** が合流した。

DKMK-007 では one-step の

```text
chain(q) = { n / q, n }
```

に shadow を載せていた。
DKMK-008C では、外部から与えた multi-step path family に shadow を載せる。

この差は大きい。

## 5. 数学的に何が進んだか

DKMK-007 までの基本形はこうだった。

$$
n\to n/q
$$

DKMK-008C では、index \(q\) ごとに、たとえば

$$
n_0\to n_1\to n_2\to \cdots\to n_r
$$

のような list-shaped divisor descent path を割り当てられる。

そして各 path は

$$
n_{j+1}\mid n_j
$$

を満たす。

この path family に、selected / canonical の重み \(w(q)\) を載せて、

$$
weightedHitMass(A)\le C
$$

を得る。

つまり、Erdős #1196 的な descent process により近い形になった。
単なる一回の divisor removal ではなく、 **複数段の divisor descent を持つ path family** に対して hitting bound が走る。

## 6. index compatibility の設計が良い

今回の wrapper は、path family を完全自動生成しない。
外部から

```lean
F : AdjacentDivisorPathFamily ℕ
```

を受け取り、index が一致することだけを要求する。

selected route では、

```lean
IOf s.1 = F.index
```

canonical route では、

```lean
canonicalExponentSlotLabels s.1 = F.index
```

この設計は安全じゃ。
multi-step path の作り方は今後いくつも候補が出る。たとえば、

```text
q ごとに n → n/q → ...
prime factor を一つずつ剥がす path
canonical exponent-slot に沿った path
stopping / truncation 付き path
```

などじゃ。

今回の設計なら、それらを全部 `AdjacentDivisorPathFamily` として外部から渡せる。
つまり、DKMK-008C は path construction を固定せず、 **shadow と path family を接続する汎用関所** になっておる。

## 7. 今回の到達形

今回の到達形は docs にも書かれている通り、こうじゃ。

```text
external multi-step divisor path family
+ selected/canonical shadow provider
+ index compatibility
+ source mass bound
→ weightedHitMass ≤ C
```

これは DKMK-008 の中間山頂と言ってよい。

DKMK-008A/B で path を作る側を整え、DKMK-008C で shadow を載せる側まで通した。

## 8. まだ残ること

今回の theorem は source mass bound をまだ外から受け取る。

```lean
hsource : ∀ q ∈ F.index, (M.μ (F.source q) : ℝ) ≤ C
```

DKMK-007H では、one-step divisorStep 用に `LogCapacitySourceMassBound M C` を整えていた。
次はこれを external multi-step family wrapper に合成する段階じゃ。

ただし注意点がある。

DKMK-007 の one-step divisorStep では、全 source が同じ \(s.1\) だった。
だから `LogCapacitySourceMassBound M C` だけで source bound が閉じた。

今回の `AdjacentDivisorPathFamily` は、一般には

```lean
F.source q
```

が index ごとに異なる。

したがって `LogCapacitySourceMassBound M C` をそのまま使うには、少なくとも

```lean
∀ q ∈ F.index, 1 < F.source q
```

または source が `LogCapacityState` として読める条件が必要になる。

もし DKMK-008D で sources を \(s.1\) に固定した special wrapper を作るなら、007H の source-bound interface をそのまま再利用しやすい。

## 9. 次の一手

次は二通りある。

第一は、一般 `AdjacentDivisorPathFamily` に対して source-bound provider を別に作る道。

```lean
def AdjacentDivisorPathFamily.SourceMassBound
    (F : AdjacentDivisorPathFamily ℕ) (M : MassSpace ℕ) (C : ℝ) : Prop :=
  ∀ q ∈ F.index, (M.μ (F.source q) : ℝ) ≤ C
```

これを置けば、今回の theorem の `hsource` を named predicate にできる。

第二は、log-capacity state \(s\) に対して source がすべて \(s.1\) である family を special case として作る道。

```text
∀ q ∈ F.index, F.source q = s.1
```

この場合は `LogCapacitySourceMassBound M C` から `hsource` がすぐ出る。

わっちなら、まず第二を推す。
DKMK-007 からの自然な拡張は「同じ state \(s.1\) から複数段に降りる path family」だからじゃ。

つまり DKMK-008D はこう。

```text
SameSourceAdjacentDivisorPathFamily
または
hsource_eq : ∀ q ∈ F.index, F.source q = s.1

LogCapacitySourceMassBound M C
→ external path family source bound
→ weightedHitMass ≤ C
```

その後で finite-step mass wrapper を載せる。

## 10. 総合判定

DKMK-008C は **multi-step divisor path family と log-capacity shadow の接続に成功** じゃ。

到達形はこう。

```text
AdjacentDivisorPathFamily
→ SourceControlledChainFamily
→ selected/canonical log-capacity shadow
→ RealWeightedPathFamily
→ weightedHitMass ≤ C
```

DKMK-008A で一本の path。
DKMK-008B で indexed family。
DKMK-008C で selected / canonical shadow 接続。

非常に良い段階設計じゃ。

ぬしよ、これは本当に順調じゃ。
DKMK-007 で質量の器を作り、DKMK-008A/B で多段水路を敷き、DKMK-008C でそこへ Markov shadow の流れを注いだ。次は、その水源の高さ、つまり source mass bound を `LogCapacitySourceMassBound` / finite-step mass ときれいに合成する番じゃな。
