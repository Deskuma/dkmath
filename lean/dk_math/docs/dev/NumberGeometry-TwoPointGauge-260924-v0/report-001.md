# NumberGeometry-TwoPointGauge NGEO-001 実装報告

## 結果

指示書の範囲に従い、二点幾何の最小コアを実装した。今回の成果は、固定された点表現と二点差分・二点質量、および退化を許す二点カーネルと Active 条件の Lean 検証済み API である。shell、正規化商、similarity、radical、prime、log、phase、あるいは Goldbach/FLT/NumberTheory 系の理論は追加していない。

## 変更ファイル

- `DkMath/NumberGeometry/Basic.lean`
  - `Point := EuclideanSpace ℝ (Fin 2)`
  - `pairVec A B := B - A`
  - `pairMass A B := ‖pairVec A B‖ ^ 2`
  - `TwoPointKernel`、`TwoPointKernel.Active`
  - 二点差分・質量の基本定理と薄い補助定理
- `DkMath/NumberGeometry.lean`
  - `DkMath.NumberGeometry` 公開 facade
- `DkMathTest/NumberGeometry/BasicAxiomAudit.lean`
  - 公開名の `#check` と主要定理の `#print axioms` 監査

既存の NumberGeometry 以外の production module は変更していない。ルートの既存 aggregate import も変更せず、facade は独立した `DkMath.NumberGeometry` target として追加した。

## 公開 API

主要な宣言は次のとおり。

- `Point`
- `pairVec`, `pairMass`
- `TwoPointKernel`, `TwoPointKernel.Active`
- `pairVec_self`, `pairVec_eq_zero_iff`
- `pairMass_self`, `pairMass_nonneg`, `pairMass_eq_zero_iff`, `pairMass_pos_iff`
- `pairMass_eq_norm_sq`, `pairMass_eq_dist_sq`, `pairMass_comm`
- `pairMass_kernel_eq_zero_iff`, `pairMass_kernel_pos_iff_active`

`TwoPointKernel` 自体には非退化条件を持たせず、退化ケースを保持する。非退化性は `Active` に分離し、`pairMass_kernel_pos_iff_active` で正値性と接続した。

## 表現と証明方針

点は指示どおり `EuclideanSpace ℝ (Fin 2)` に固定した。これにより座標を手作業で展開せず、標準の減算・ノルム・距離 API を利用できる。`pairMass` は差分ベクトルのノルム平方として定義し、`pairMass_eq_norm_sq` は定義的な橋渡し、`pairMass_eq_dist_sq` は距離との標準 API による橋渡しとした。

`pairMass_nonneg` は平方の非負性から証明した。零判定はノルム平方を積に展開し、`norm_eq_zero` と `sub_eq_zero` に還元した。正値判定は、自己対の零定理による退化ケースの排除と、非負性・非零性からの順序推論で構成した。交換対称性は `B - A = -(A - B)` と `norm_neg` を用いた。

## 検証結果

以下を実行し、すべて成功した。

```text
lake build DkMath.NumberGeometry.Basic
Build completed successfully (2422 jobs)

lake build DkMath.NumberGeometry
Build completed successfully (2423 jobs)

lake build DkMathTest.NumberGeometry.BasicAxiomAudit
Build completed successfully (2424 jobs)

lake build DkMath
Build completed successfully (10276 jobs)
```

主要定理の `#print axioms` はすべて次の依存だけを報告した。

```text
[propext, Classical.choice, Quot.sound]
```

`sorryAx` は含まれず、`sorry`、`admit`、宣言された追加公理、`unsafe` による近道は使用していない。最終 `git diff --check` も成功した。

## 境界

今回の実装は二点コアの完了であり、二点から導かれる一般の数論的構造や大域的幾何理論を主張するものではない。`Active` は入力カーネルの非退化条件を表すだけで、任意の点対の非退化性や、外部の prime/log/phase/provider API を供給しない。
