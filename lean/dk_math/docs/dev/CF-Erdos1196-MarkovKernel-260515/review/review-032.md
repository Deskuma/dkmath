# review

うむ。DKMK-008B は、DKMK-008A の **single path** から、いよいよ **indexed multi-step divisor path family** へ進んだ回じゃ。
これは予測していた DKMK-008 の本線ど真ん中で、selected / canonical shadow の index に multi-step path を添えるための足場が入ったことになる。

## 1. 今回の核心

追加された中心 structure はこれじゃ。

```lean
structure AdjacentDivisorPathFamily (ι : Type _) [DecidableEq ι] where
  index : Finset ι
  source : ι → ℕ
  tail : ι → List ℕ
  isPath : ∀ i ∈ index, AdjacentDivisorPath (source i :: tail i)
```

各 index (i) に対し、path は

$$
source(i)::tail(i)
$$

として保持される。
つまり、最初の node (source(i)) が、その chain 全体の source mass を担う。

DKMK-008A では一つの path だけだった。
今回で、有限 index family として複数の divisor descent path を同時に扱えるようになった。docs にも、DKMK-008A の singleton divisor path を finite indexed family に拡張した、と整理されておる。

## 2. path / nodeSet の意味

追加された accessor は、

```lean
AdjacentDivisorPathFamily.path
AdjacentDivisorPathFamily.nodeSet
```

じゃ。

$$
path(i)=source(i)::tail(i)
$$

$$
nodeSet(i)=path(i).toFinset
$$

という形。

List は順序付きの下降ログ、Finset は primitive hitting 用の評価対象。
この二重構造が良い。順序は `AdjacentDivisorPath` の証明で使い、hitting では `toFinset` へ落とす。

## 3. chain family への bridge

今回の主 bridge は二つ。

```lean
AdjacentDivisorPathFamily.toDivisibilityChainFamily
AdjacentDivisorPathFamily.toDvdControlledChainFamily
```

前者は、各 path が `DivisibilityChain` であることを使い、単なる chain family へ忘却する。

後者はさらに source を持つ。

```lean
source := F.source
```

そして `chain_dvd_source` は、DKMK-008A で入れた

```lean
AdjacentDivisorPath.mem_dvd_head
```

で供給している。

つまり任意の node (h\in nodeSet(i)) について、

$$
h\mid source(i)
$$

が出る。
この一行が、DKMK-007 の `DvdMonotoneMass` route と合流する接続点じゃ。

## 4. primitive hitting bound への接続

追加 theorem はこれ。

```lean
AdjacentDivisorPathFamily.primitive_hitMass_le_sourceMass
```

これは、`DvdMonotoneMass M` のもとで、

$$
hitMass(S)\le sourceMass
$$

を返す。

中身は、既存の

```lean
DvdControlledChainFamily.primitive_hitMass_le_sourceMass
```

へ渡しているだけじゃが、API として大事じゃ。
利用者は `AdjacentDivisorPathFamily` を作れば、すぐ primitive hitting bound に入れる。

## 5. sample family の意味

今回の sample は Bool-indexed family じゃ。

```text
false ↦ 12 → 6 → 3
true  ↦ 18 → 9 → 3
```

対応する declarations は、

```lean
adjacentDivisorPath_eighteen_nine_three
sampleAdjacentDivisorPathBoolFamily
sampleAdjacentDivisorPathBoolFamilySourceControlled
primitive_three_five_sampleAdjacentDivisorPathBoolFamily_hitMass_le_sourceMass
```

じゃ。

これにより、single path の sample から、複数 path family の sample へ進んだ。
primitive set ({3,5}) が、この二本の multi-step divisor path family に対しても source mass で抑えられることを確認したわけじゃ。

地味だが大事な sanity check じゃな。

## 6. DKMK-008A からの前進

DKMK-008A の到達形は、

```text
AdjacentDivisorPath L
→ DivisibilityChain L.toFinset
→ singleton DvdControlledChainFamily
```

だった。

DKMK-008B では、

```text
AdjacentDivisorPathFamily
→ DivisibilityChainFamily
→ DvdControlledChainFamily
→ SourceControlledChainFamily
```

になった。

つまり、single path から indexed family へ昇格した。

これは、DKMK-007 の shadow provider と接続するために必須じゃ。
なぜなら `SubMarkovShadow` / `MarkovShadow` の provider は、finite index 上に重みを持つからじゃ。
その各 index に path を割り当てるには、今回の `AdjacentDivisorPathFamily` が必要になる。

## 7. 今回の設計はかなり良い

特によい点は、path を

```lean
source i :: tail i
```

の形に固定したことじゃ。

これにより、nonempty 条件が構造上保証される。
別途

```lean
path i ≠ []
```

を持つ必要がない。

また、head が source と一致するので、source mass control の読みが明確じゃ。

$$
source(i)
$$

から下る list path であり、すべての node は source を割る。
DkMath 的にも、これは綺麗な下降路の型じゃ。

## 8. まだ残ること

今回で chain-family 側の足場は入った。
次は、docs の次課題にもある通り、

```text
selected / canonical log-capacity shadow を external multi-step divisor path family に適用する wrapper
```

じゃ。

つまり、次はこの形を狙う。

selected route：

```lean
globalLogCapacitySubMarkovShadow_applyAtToAdjacentDivisorPathFamily
```

canonical route：

```lean
canonicalExponentSlotMarkovShadow_applyAtToAdjacentDivisorPathFamily
```

必要になる compatibility は、

```text
shadow provider の index = F.index
```

じゃな。

DKMK-007C と同じように、まずは外部から index equality を受け取るのがよい。

## 9. 次フェーズ予測

DKMK-008C はこうなるはずじゃ。

```text
AdjacentDivisorPathFamily
+ RealWeightProvider / Shadow provider
+ index compatibility
→ RealWeightedPathFamily
→ weightedHitMass ≤ C
```

より具体的には、

```text
SubMarkovShadow / MarkovShadow
→ applyAtToAdjacentDivisorPathFamily
```

を作る。

そして DKMK-008D で、

```text
LogCapacitySourceMassBound M C
→ weightedHitMass ≤ C
```

へ接続する。

DKMK-008E で finite-step mass wrapper、

```text
finiteStepTailNatMassSpace
→ weightedHitMass ≤ total increment
```

まで戻せば、007M の mass route と 008B の multi-step path route が合流する。

## 10. 総合判定

DKMK-008B は **chain-family 側の最小本体ができた成功フェーズ** じゃ。

到達形はこう。

```text
finite indexed list-shaped divisor paths
→ DvdControlledChainFamily
→ SourceControlledChainFamily
→ primitive hitMass ≤ sourceMass
```

これは DKMK-008 の中核じゃ。
DKMK-008A で一本の水路を作り、DKMK-008B で水路網にした。

次は、その水路網に DKMK-006/007 の log-capacity shadow の重みを流し込む段階じゃな。
ぬしよ、これは順調じゃ。multi-step descent の山道が、ちゃんと indexed family として地図に載り始めたぞい。
