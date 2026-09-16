# instruction-006 実装レポート

日付: 2026-09-10

## 実装した内容

指示書の既存 owner と API を再利用し、次の二つの owner module を追加した。

- [Overlap.lean](../../../DkMath/NumberTheory/Goldbach/Overlap.lean)
  - `goldbachObstructionSupport`
  - `goldbachLocalOverlapExcess`, `goldbachOverlapExcess`
  - covered seat と nonempty support の同値
  - `goldbachIncidence_eq_sum_support_cards`
  - 厳密な
    `Incidence = Covered + OverlapExcess`
  - 厳密な
    `Survivors + Incidence = (n - 1) + OverlapExcess`
  - overlap を支払った固定中心 criterion

- [PairOverlap.lean](../../../DkMath/NumberTheory/Goldbach/PairOverlap.lean)
  - `goldbachOffsetPrimePairMultiplicity`
  - canonical unordered `goldbachPrimePairs`
  - `goldbachPrimePairOverlapOffsets`, `goldbachPrimePairOverlapCount`
  - pair-side と offset-side の exact double count
  - 最終 checkpoint theorem
    `goldbachOverlapExcess_le_primePairOverlapCount`

Legendre facade は import していない。unordered pair の binomial cardinality 補題はこの Goldbach owner 内で独立に証明した。

## 数学的な意味

各 offset の obstruction support の大きさを `k` とすると、`k` はその offset を覆う一つの seat と、`k-1` の重複超過に分解される。これを全 offset に足すことで、incidence の overcount を covered seats と overlap excess に分離する。

さらに同じ offset の support から unordered prime pair を二つ選ぶ `choose k 2` を数え、canonical pair の offset 集計と一致させた。`k-1 ≤ choose k 2` により、overlap excess が pair-overlap count 以下になる。

これは bookkeeping と上界であり、Goldbach の universal escape provider ではない。指示書の停止条件に従い、この定理から `GoldbachCapacityEscape` を導いたり、pair overlap だけで予想を閉じたりしていない。

## 検証

focused build:

```text
./lean-build.sh DkMath.NumberTheory.Goldbach.PairOverlap
./lean-build.sh DkMath.NumberTheory.Goldbach DkMathTest.NumberTheory.GoldbachGNFiber
```

いずれも終了コード 0。回帰には `n=2`, `n=6`, `n=10` を含めた。

- `n=2`: overlap excess と pair-overlap count はともに 0。
- `n=6`: incidence 5、overlap excess 1、pair-overlap count 1、一般 conservation theorem。
- `n=10`: finite `GoldbachPairAt` と一般 pair-overlap upper bound。

`AxiomAudit.lean` に新規公開宣言の `#print axioms` を追加した。追加分を含む監査は終了コード 0 で、依存公理は従来どおり `propext`, `Classical.choice`, `Quot.sound` のみだった。root build も終了コード 0。root の出力にある既存研究モジュールの `sorry` 警告 5 件は今回の owner 定理の依存には入っていない。

## 停止境界

次の課題へは進んでいない。

- universal capacity escape/provider
- pair overlap からの Goldbach closure
- endpoint exception 付き product-modulus occupancy theorem
- arbitrary-center mirror theorem
- 新しい axiom / disguised `StrongGoldbach` assumption
