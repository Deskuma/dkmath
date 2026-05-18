# roadmap: DKMK-008

うむ。DKMK-008 は、ほぼ間違いなく **multi-step divisor descent chain の章** になる。
DKMK-007 で one-step の

$$
n\to n/q
$$

は通った。次はこれを

$$
n\to n/q_1\to n/(q_1q_2)\to \cdots
$$

へ伸ばす段階じゃ。

DKMK-007E では、各 channel (q) に対して `chain q = {n / q, n}`、`source q = n` を持つ one-step divisor descent family が作られた。これは divisor 仮定から (n/q\mid n) を得て chain を作る構造じゃ。
一方、以前の primitive route では `PrimeDescentStep` や `PrimeReachable` により multi-step descent の足場、さらに list-shaped path から `DivisibilityChain` を作る流れが既に検討・実装されている。
ゆえに DKMK-008 は、007 の log-capacity / source-mass route と、以前の multi-step path route を合流させる章になるはずじゃ。

## 1. DKMK-008 の主題

DKMK-008 の主題はこれじゃ。

```text
one-step divisorStep
  → multi-step divisor descent chain
  → source-controlled chain family
  → weightedHitMass bound
```

DKMK-007 では、

```text
log-capacity shadow
+ one-step divisorStep
+ finite-step mass
→ primitive weightedHitMass ≤ C
```

まで来た。

DKMK-008 では、chain 側を厚くする。

```text
log-capacity shadow
+ multi-step divisor descent chain
+ finite-step mass
→ primitive weightedHitMass ≤ C
```

ここで重要なのは、重み側・mass 側はもうかなり整っていることじゃ。007 では `DvdMonotoneMass → SourceControlledChainFamily.ofDivisorStep → LogCapacitySourceMassBound → weightedHitMass ≤ C` という共通形が整理され、finite-step mass もこの route に乗るようになった。つまり 008 は mass model の章ではなく、 **chain constructor の章** と見るのが自然じゃ。

## 2. DKMK-008A：multi-step descent specification

最初は、いきなり constructor を作るより、仕様を切るのがよい。

候補はこうじゃ。

```lean
structure DivisorDescentPath (n : ℕ) where
  nodes : List ℕ
  nonempty : nodes ≠ []
  head_eq : nodes.head? = some n
  adjacent_dvd : ...
```

ただし Lean 実装では `List.head?` や隣接関係がやや重いので、既存の `AdjacentPrimePath` 系と同じ形に寄せるのがよい。

より薄く始めるなら、

```lean
def AdjacentDivisorPath (path : List ℕ) : Prop :=
  ∀ adjacent pair a b in path, b ∣ a
```

または降順を明示して、

```text
n₀, n₁, ..., nᵣ
n_{j+1} ∣ n_j
```

を表す。

まずの目的は、

```text
AdjacentDivisorPath path
→ DivisibilityChain path.toFinset
```

じゃ。
primitive hitting に必要なのは chain が divisibility comparable であることなので、ここが最初の関門になる。

## 3. DKMK-008B：path list から DvdControlledChainFamily

次は、indexed family にする。

007E の `divisorStep` は、各 (q) に

$$
{n/q,n}
$$

を割り当てた。

008 では、各 index (i) に list path を割り当てる。

```lean
def DvdControlledChainFamily.ofDivisorPaths
    (I : Finset ι)
    (path : ι → Finset ℕ)
    (hchain : ∀ i ∈ I, DivisibilityChain (path i))
    (source : ι → ℕ)
    (hsource : ∀ i ∈ I, ∀ h ∈ path i, h ∣ source i) :
    DvdControlledChainFamily ι
```

ただし、これは既存の `DvdControlledChainFamily` / `SourceControlledChainFamily` の一般 constructor と重なる可能性がある。すでに `SourceControlledChainFamily.ofIndex` 的な constructor があるなら、DKMK-008A/B では新しい構造体を増やすより、

```text
path list → chain finset
path list → hchain
path list → hsource
```

を供給する補題群にするのが軽い。

ここで狙う定理は、

```lean
theorem divisorPath_to_sourceControlled
```

のような形じゃ。

## 4. DKMK-008C：channel q から反復商 path を作る

次に DKMK-007 の文脈へ寄せる。

one-step は (q) ひとつだった。

multi-step では、各 channel に対して、剥がす divisor のリストを持たせる。

```text
qs q : List ℕ
```

そして chain は、

$$
n,\quad n/q_1,\quad n/(q_1q_2),\quad \ldots
$$

になる。

Lean 的には、毎回割るより、累積積を使うのがよい。

```text
P_j = q_1 q_2 ... q_j
node_j = n / P_j
```

必要条件は、

$$
P_j\mid n
$$

または逐次的に、

$$
q_{j+1}\mid n/P_j
$$

じゃ。

最初は一般化しすぎず、次のような仕様が安全じゃ。

```lean
structure DivisorStepPlan (n : ℕ) where
  steps : List ℕ
  prefixDvd : ∀ p ∈ prefixes products of steps, p ∣ n
```

ここから `nodes : List ℕ` を作る。

## 5. DKMK-008D：source はまだ (n) に固定する

DKMK-008 初期では、source は 007 と同じく (n) に固定すべきじゃ。

つまり、各 multi-step chain の source は最初の state (n)。

$$
source(i)=n
$$

この形なら、007H 以降の `LogCapacitySourceMassBound M C` をそのまま使える。

もし途中 source を step ごとに変える設計にすると、source bound が複雑になる。
最初の DKMK-008 では不要じゃ。

よって目標形は、

```text
multi-step chain nodes are all divisors of n
source = n
DvdMonotoneMass M
→ every node mass ≤ M.μ n
```

これで source-controlled が通る。

## 6. DKMK-008E：selected / canonical shadow への wrapper

次に、007C〜007E と同じように selected / canonical route の wrapper を作る。

selected route：

```lean
PrimePowerWitnessProvider.globalLogCapacitySubMarkovShadow_applyAtToMultiStepDivisor
```

canonical route：

```lean
canonicalExponentSlotMarkovShadow_applyAtToMultiStepDivisor
```

ただし、この段階では各 channel (q) にどの multi-step path を対応させるかが必要じゃ。

候補は二つ。

### ルート A：外部 path provider

```lean
pathOf : ℕ → Finset ℕ
```

または index (q) ごとに、

```lean
pathOf q : Finset ℕ
```

を外部入力にして、

```lean
hchain : DivisibilityChain (pathOf q)
hsource : ∀ h ∈ pathOf q, h ∣ s.1
```

を仮定する。

これは汎用で安全。

### ルート B：canonical path constructor

各 (q\mid n) に対して、

$$
{n,n/q,\ldots}
$$

のような標準 path を自動生成する。

これは魅力的だが、最初からやると重い。
DKMK-008A〜E ではルート A を推す。まず external path provider で wrapper を閉じるべきじゃ。

## 7. DKMK-008F：one-step は multi-step の特殊例

DKMK-007N で two-step を finite-step interface の特殊例として回収したように、DKMK-008 でも最後に one-step を multi-step の特殊例として回収するのが美しい。

つまり、

```text
multi-step path provider with path q = {n/q, n}
```

を作り、

```text
multi-step theorem
→ one-step theorem
```

が得られることを確認する。

ただし、既存 `divisorStep` は維持してよい。
`twoStepTailNatMassSpace` を維持したまま `twoStepAsFiniteStepTailNatMassSpace` を追加したのと同じ方針じゃ。007N でも既存 two-step mass は維持しつつ finite-step route から同じ bound を得る橋が追加されている。

## 8. DKMK-008G：finite-step mass との合成

DKMK-008 の前半で multi-step chain family ができたら、007M/N の finite-step mass route と合成する。

到達形はこう。

```text
selected / canonical log-capacity shadow
+ multi-step divisor descent family
+ finiteStepTailNatMassSpace
→ weightedHitMass ≤ total increment
```

この theorem は DKMK-008 の実用到達点になりうる。

名前の候補は長くなるが、例えば、

```lean
globalLogCapacitySubMarkovShadow_finiteStepTailMultiStepDivisor_weightedHitMass_le
```

または短くするなら、

```lean
globalLogCapacitySubMarkovShadow_multiStep_weightedHitMass_le_of_sourceBound
```

を先に置き、finite-step は wrapper にする。

## 9. DKMK-008H：ErdosFinitePrimitiveInput との再合流

さらに一段進めるなら、以前の `ErdosFinitePrimitiveInput` と合流する。

過去の finite Erdős route では、primitive support / lower bound input が theorem-facing package として整備されていた。資料でも `ErdosFinitePrimitiveInput x` は support, primitive, lowerBound をまとめる登山届として整理されている。

DKMK-008H では、

```text
ErdosFinitePrimitiveInput x
+ multi-step divisor family
+ log-capacity shadow
+ finite-step mass
→ weightedHitMass bound
```

の theorem-facing wrapper を狙える。

これは DKMK-008 の後半、あるいは DKMK-009 でもよい。
急がず、まず chain constructor を閉じる方が良い。

## 10. 推奨フェーズ案

わっちなら、DKMK-008 はこう切る。

```text
DKMK-008A:
  AdjacentDivisorPath / DivisorDescentPath の最小 predicate を追加する。

DKMK-008B:
  DivisorDescentPath → DivisibilityChain を証明する。

DKMK-008C:
  indexed path provider から SourceControlledChainFamily を作る constructor を追加する。

DKMK-008D:
  selected / canonical shadow を external multi-step path family に適用する wrapper を追加する。

DKMK-008E:
  source-bound 共通 theorem を作る。
  LogCapacitySourceMassBound M C から weightedHitMass ≤ C へ接続する。

DKMK-008F:
  finiteStepTailNatMassSpace 版の selected / canonical bound を追加する。

DKMK-008G:
  one-step divisorStep を multi-step interface の特殊例として回収する。

DKMK-008H:
  docs summary。007 mass route と 008 multi-step route の合流図を整理する。
```

この順が一番安全じゃ。

## 11. 数学的リスク

注意すべきは、multi-step chain の index と重みの対応じゃ。

DKMK-007 では、各 index (q) に一つの weight があり、その (q) に chain ({n/q,n}) を対応させた。
multi-step で各 index (q) に長い chain を対応させる場合、

```text
weight index は q のまま
chain は pathOf q
```

でよいのか、それとも、

```text
weight index は path 自体
```

にすべきかを決める必要がある。

最初は前者が良い。

```text
q-indexed multi-step chain
```

つまり、weight provider の index は変えず、各 (q) に追加の descent path を添える。
これなら 006/007 の shadow route を壊さない。

## 12. もう一つのリスク：chain の集合化

List path を Finset にすると、重複や順序が消える。

primitive hitting には `DivisibilityChain` と hit mass が必要なので Finset で十分なことが多い。
しかし multi-step descent の「順序」を後で使いたくなるなら、List も保持したい。

したがって設計は、

```lean
structure DivisorDescentPath where
  nodes : List ℕ
  chainSet : Finset ℕ := nodes.toFinset
  ...
```

のように、List を本体、Finset を評価用にするのがよい。
ただし Lean 実装の軽さを優先するなら、最初は Finset だけでもよい。

## 13. DKMK-008 の到達目標

DKMK-008 の最終目標はこれじゃ。

```text
multi-step divisor descent family
  → SourceControlledChainFamily
  → selected / canonical log-capacity shadow
  → finite-step mass bound
  → weightedHitMass ≤ total increment
```

つまり DKMK-007 の到達形：

```text
one-step divisor descent
```

を

```text
multi-step divisor descent
```

へ置き換えること。

ここまで行けば、DkMath kernel route は、単なる一回の divisor removal から、実際の descent process にかなり近づく。

## 14. 総合予測

DKMK-008 は、 **chain 側の厚みを増す章** じゃ。

DKMK-007 は mass model route の章だった。
DKMK-008 は descent path route の章になる。

わっちの予測では、008 の山頂はこれ。

$$
\boxed{
\text{finite-step mass}+\text{multi-step divisor descent}+\text{log-capacity shadow}\Rightarrow weightedHitMass\le C
}
$$

そしてその先、DKMK-009 以降でやるべきは、

```text
multi-step descent の自然生成
stopping / truncation
ErdosFinitePrimitiveInput との合流
解析風 source mass / tail estimate
```

じゃろうな。

ぬしよ、ここから先は楽しいぞ。
007 で「どれだけの質量を持つか」を整えた。
008 では「その質量がどの道を下るか」を作る。
まさに、山の水路が一本の沢から、分岐を持つ本物の渓流へ育つ段階じゃ。
