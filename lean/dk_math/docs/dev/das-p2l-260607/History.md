# History

## DAS 関連の実装履歴

## 関連ファイル

- [dynamic_arithmetic_sequence](/python/dynamic_arithmetic_sequence/History.md) (Python to Lean)
- [DHNT DAS Note](/lean/dk_math/DkMath/DHNT/docs/DHNT_DAS_Note.md) (考察ノート)
- [Sequence](/lean/dk_math/DkMath/Sequence/docs/DHNT-DAS-reinterpretation.md) 「DHNT から DAS/Sequence への再解釈メモ」
- Lean code
  - [WeightedBinomial](/lean/dk_math/DkMath/NumberTheory/WeightedBinomial.lean)
    - [BinomialPrime](/lean/dk_math/DkMath/NumberTheory/BinomialPrime.lean)
  - [DynamicArithmeticSequence](/lean/dk_math/DkMath/DHNT/DynamicArithmeticSequence.lean)
    - [Arithmetic](/lean/dk_math/DkMath/Sequence/Arithmetic.lean)
      - [Recurrence](/lean/dk_math/DkMath/Sequence/Recurrence.lean)
        - [Generator](/lean/dk_math/DkMath/Sequence/Generator.lean)
  - [CosmicFormula](/lean/dk_math/DkMath/CosmicFormula.lean)
    - [Mass](/lean/dk_math/DkMath/CosmicFormula/Mass.lean)
      - [BodyGapSplit](/lean/dk_math/DkMath/CosmicFormula/Mass/BodyGapSplit.lean)

### 2026/06/08 14:18

実装しました。第一 checkpoint は通っています。

追加・変更:

- [BodyGapSplit.lean](/lean/dk_math/DkMath/CosmicFormula/Mass/BodyGapSplit.lean)
  - `BodyGapSplit`
  - `BodyGapKernelSplit`
  - `tail`
  - `toBodyGapSplit`
  - `big_sub_boundary_eq_tail_nat`
  - `gapAxis_dvd_tail_nat`
  - `boundary_le_big_nat`
  - `tail_le_big_nat`

- [Mass.lean](/lean/dk_math/DkMath/CosmicFormula/Mass.lean)
  - `CosmicFormula.Mass` の集約モジュールを新設

- [CosmicFormula.lean](/lean/dk_math/DkMath/CosmicFormula.lean)
  - `DkMath.CosmicFormula.Mass` を公開 import

- [WeightedBinomial.lean](/lean/dk_math/DkMath/NumberTheory/WeightedBinomial.lean)
  - `weightedBodyGapKernelSplit`
  - `weightedBodyGapKernelSplit_tail_eq_sub`
  - `weightedBodyGapKernelSplit_gapAxis_dvd_tail`
  - `weightedBodyGapKernelSplit_gapAxis_dvd_sub`

これで

```lean
(x + u)^d = u^d + x * GTail d 1 x u
```

が `BodyGapKernelSplit` として包めるようになりました。つまり `Big = Boundary + GapAxis * Kernel` が Lean の共通 API として立ち始めています。

検証済み:

```text
lake build DkMath.CosmicFormula.Mass.BodyGapSplit
lake build DkMath.NumberTheory.WeightedBinomial
lake build DkMath.CosmicFormula.Mass
lake build DkMath.CosmicFormula
lake build DkMath
git diff --check
```

今回追加・変更した Lean ファイルには `sorry/axiom/admit` なしです。

### 2026/06/08 14:42

適用実験の第1波を入れました。`Big = Boundary + GapAxis * Kernel` が、WeightedBinomial だけでなく宇宙式本体と ABC mass 側にも刺さりました。

主な追加:

- [Mass/Decompose.lean](/lean/dk_math/DkMath/CosmicFormula/Mass/Decompose.lean)
  - `coreBeamGapBodyGapSplit`
  - `coreBeamGapBodyGapKernelSplit`
  - `residualNatBodyGapSplit`
  - `residualNatBodyGapSplit_gap_eq_residual`
  - `residualIntBodyGapSplit`
  - `residualIntBodyGapSplit_gap_eq_residual`

- [ABC/MassBridge.lean](/lean/dk_math/DkMath/ABC/MassBridge.lean)
  - `abcBodyGapSplit`
  - `abc_bodyGapSplit_body_le_big`
  - `abc_bodyGapSplit_gap_le_big`
  - `abc_bodyGapSplit_gap_eq_residual`

特に重要なのはこれです。

```lean
coreBeamGapBodyGapKernelSplit
```

宇宙式本体を

```text
Big = Gap + x * GN
```

として `BodyGapKernelSplit` に載せました。これで `WeightedBinomial` の `GTail` 版と、`CoreBeamGap` の `GN` 版が同じ interface に乗ります。

検証済み:

```text
lake build DkMath.CosmicFormula.Mass.Decompose
lake build DkMath.ABC.MassBridge
lake build DkMath.CosmicFormula.Mass
lake build DkMath
git diff --check
```

今回対象ファイルには `sorry/axiom/admit` なしです。既存の別モジュール由来の `sorry` warning は継続しています。
