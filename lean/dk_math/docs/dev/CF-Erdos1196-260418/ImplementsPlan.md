# 実装計画

以下の議論と設計に基づき、Erdos #1196 向けの実装計画をここに固定する。

[議論](./CosmicFormula-Erdos1196-discussion.md)
[設計](./CosmicFormula-Erdos1196-design.md)

## 1. 今回の実装目標

今回の第一目標は、論文全体の確率過程を一気に Lean へ移すことではない。

先に次を形式化する。

1. `Big = Body + Gap`, `Body = Core + Beam` を質量保存 API として再編成する。
2. primitive prime / `GN` / `padicValNat` を「下降 flow の痕跡」としてつなぐ。
3. ABC 側で再利用できる bridge を薄く追加する。

つまり、初手では

- exact な Markov / sub-Markov 過程
- `Λ(q) / log n` の実数確率
- `1 + O(1 / log x)` の漸近評価

までは入れず、まずはその手前の代数的・構造的 spine を作る。

## 2. ワークスペース調査結果

今回の計画は、新規理論をゼロから起こすより、既存資産の上に整理層を足す方が筋が良い。

### 2.1. 既存の直接利用候補

- `DkMath/CosmicFormula/CoreBeamGap.lean`
  - `big_eq_body_add_gap`
  - `body_eq_core_add_beam`
  - `big_eq_core_beam_gap`
- `DkMath/CosmicFormula/ResidualNat.lean`
  - `big_eq_body_add_gap`
  - `big_eq_core_add_beam_add_gap`
  - `residual_eq_gap`
- `DkMath/CosmicFormula/ResidualInt.lean`
  - `bigInt_eq_bodyInt_add_gapInt`
  - `bigInt_eq_coreInt_add_beamInt_add_gapInt`
  - `residualInt_eq_gapInt`
- `DkMath/NumberTheory/PrimitiveBeam.lean`
  - primitive prime existence / `GN` divisibility / `padicValNat` bridge
- `DkMath/NumberTheory/ZsigmondyCyclotomicSquarefree.lean`
  - squarefree 仮定からの honest な valuation 上界
- `DkMath/ABC/PadicValNat.lean`
  - `padicValNat_pow`
  - `padicValNat_one_le_of_prime_dvd`
- `DkMath/ABC/Rad.lean`
  - `rad`
  - `rad_dvd_nonzero`

### 2.2. 設計上の判断

- `CosmicFormula` 側には既に分解定理があるため、最初の実装は「新理論の証明」より「API の整理」に寄せる。
- `PrimitiveBeam` 側には #1196 的な primitive / valuation の入口が既にあるため、新規 flow API はこれを包む形にする。
- `ABC` 側は本体定理の置き場にせず、翻訳層だけ追加する。

## 3. 実装方針

### 3.1. 過度な抽象化を避ける

いきなり一般 `Measure` や `MarkovKernel` に寄せず、まずは

- 非負量
- 分解
- 子和が親を超えない
- primitive により chain が衝突しない

の 4 点を補題として切り出す。

### 3.2. `Nat` 減算は bridge 扱い

- 保存則の中心は `ℤ` / `ℚ` 寄りの読みで固定する。
- `Nat` 版は既存 `ResidualNat` を利用し、必要仮定つきの補題として接続する。

### 3.3. 新規ファイルは薄く始める

設計書の大構成は維持するが、初回は最低限の spine だけ作る。

想定ファイル:

- `DkMath/CosmicFormula/Mass/Core.lean`
- `DkMath/CosmicFormula/Mass/Decompose.lean`
- `DkMath/CosmicFormula/Mass/Branch.lean`
- `DkMath/NumberTheory/ValuationFlow/Basic.lean`
- `DkMath/NumberTheory/ValuationFlow/Primitive.lean`
- `DkMath/ABC/MassBridge.lean`
- `DkMath/ABC/ValuationFlowBridge.lean`

ただし `Tromino2D.lean` と `Harmonic.lean` は今回は保留とする。

## 4. Phase 分割

## Phase A. Cosmic Mass API の固定

目的:

- 既存 `CoreBeamGap` / `ResidualNat` / `ResidualInt` の分解補題を、#1196 文脈で再利用しやすい名前に整理する。

実装:

- `CosmicPart` の列挙
- 必要最小限の `MassSpace`
- `CosmicMassAPI`
- 既存定理への wrapper / alias

最低限通す定理:

- `mass_big_eq_mass_body_add_mass_gap`
- `mass_body_eq_mass_core_add_mass_beam`
- `mass_big_eq_mass_core_add_mass_beam_add_mass_gap`
- `mass_residual_eq_mass_gap`

依存元:

- `DkMath.CosmicFormula.CoreBeamGap`
- `DkMath.CosmicFormula.ResidualNat`
- `DkMath.CosmicFormula.ResidualInt`

完了条件:

- `Big / Body / Gap / Core / Beam` の保存則を、新しい API 名で参照できる。
- `Nat` 版と `Int` 版のどちらを使うべきかがコメントで明示されている。

## Phase B. Branch / SubConservative API

目的:

- 「子の総質量は親を超えない」を抽象 API として固定する。

実装:

- `Branching`
- `outgoingMass`
- `SubConservative`
- `branch_sum_le_parent`
- `outgoingMass_le_mass`

方針:

- この段階では具体的な `von Mangoldt` 重みは入れない。
- `Finset` ベースの有限 branch に留める。

完了条件:

- 将来の hitting-mass 評価が「branch の一般補題」として参照できる状態になる。

## Phase C. Primitive / GN / valuation の接続

目的:

- #1196 的な primitive 条件を、既存 `PrimitiveBeam` と squarefree valuation 補題へつなぐ。

実装:

- `ValuationFlow.Basic` に、valuation profile や flow one-step の最小定義を置く。
- `ValuationFlow.Primitive` で既存 primitive prime 補題を再束ねる。
- `PrimitiveBeam` 依存を「flow 的な命名」で再公開する。

最低限通す定理:

- primitive prime が boundary を割らない
- primitive prime が `GN` を割る
- primitive prime の valuation が `GN` 側へ移る
- squarefree `GN` なら valuation は高々 `1`

依存元:

- `DkMath.NumberTheory.PrimitiveBeam`
- `DkMath.NumberTheory.ZsigmondyCyclotomicSquarefree`
- `DkMath.ABC.PadicValNat`

完了条件:

- 「primitive condition -> Beam/GN 側へ質量が流れる -> valuation 上界」という spine が 1 本の import で読める。

## Phase D. ABC bridge

目的:

- `rad` / `squarefree` / `padicValNat` を Mass / ValuationFlow 側へ橋渡しする。

実装:

- `ABC/MassBridge.lean`
- `ABC/ValuationFlowBridge.lean`

内容:

- `rad` を support mass 的に読む補題の追加
- `padicValNat` を local mass / local load 的に読む薄い wrapper
- squarefree / squarefull を「局所質量の上界 / 下界」へ言い換える補題名整理

注意:

- ここでは ABC 本体の大定理には踏み込まない。
- bridge は翻訳レイヤに徹する。

完了条件:

- ABC 側から、新設 API を直接 import できる。
- 既存 `PadicValNat` / `Rad` の補題を再利用するだけで閉じる。

## Phase E. 例と build 整備

目的:

- 新設 API が空抽象に終わっていないことを、既存 concrete 例で確認する。

候補:

- `CoreBeamGap` の既存 concrete 例
- `PrimitiveBeamExamples`
- 必要なら `DkMathTest` に #print axioms を追加

完了条件:

- 各 phase ごとに少なくとも 1 つ、既存 concrete 対象へ適用した例がある。

## 5. 今回の実装順序

今回の着手順は次で固定する。

1. `CosmicFormula/Mass/Core.lean`
2. `CosmicFormula/Mass/Decompose.lean`
3. `CosmicFormula/Mass/Branch.lean`
4. `NumberTheory/ValuationFlow/Basic.lean`
5. `NumberTheory/ValuationFlow/Primitive.lean`
6. `ABC/MassBridge.lean`
7. `ABC/ValuationFlowBridge.lean`

理由:

- 既存実装の厚みは `CosmicFormula` と `PrimitiveBeam` にあり、ここを先に整えると後段が薄く済む。
- 逆に ABC から入ると、未固定の概念を橋側へ漏らしやすい。

## 6. 各段階の build 方針

`__AGENT.md` に従い、単体 build で進める。

想定 build 対象:

- `./lean-build.sh DkMath.CosmicFormula.Mass.Core`
- `./lean-build.sh DkMath.CosmicFormula.Mass.Decompose`
- `./lean-build.sh DkMath.CosmicFormula.Mass.Branch`
- `./lean-build.sh DkMath.NumberTheory.ValuationFlow.Basic`
- `./lean-build.sh DkMath.NumberTheory.ValuationFlow.Primitive`
- `./lean-build.sh DkMath.ABC.MassBridge`
- `./lean-build.sh DkMath.ABC.ValuationFlowBridge`

必要に応じて:

- `./lean-build.sh DkMath.NumberTheory.PrimitiveBeam`
- `./lean-build.sh DkMath.ABC.PadicValNat`

## 7. 今回やらないこと

初回実装では次は保留する。

- `Λ(q) / log n` を使う実数確率 kernel の定義
- Mertens 型評価
- `1 + O(1 / log x)` の解析的評価
- infinite set 上の hitting probability の完成形
- `Tromino2D` / `Harmonic` の本格展開

これらは、Phase A-D が閉じてから次段階として扱う。

## 8. 実装上の注意

- 既存証明を壊さないため、まずは wrapper / alias / bridge を優先する。
- `Nat` と `Int` の両方に同名概念を作る場合、コメントで役割差を明記する。
- `research` 依存が残る箇所と honest 補題で閉じる箇所を分離する。
- `PrimitiveBeam` の既存定理名は温存し、新 API では再公開名を追加する形にする。

## 9. 現時点の最終判断

この案件の最善手は、設計書にある大構想をそのまま全面実装することではなく、
既存の `CosmicFormula` / `PrimitiveBeam` / `PadicValNat` を spine にして
「質量保存」と「valuation flow」の 2 層を先に閉じることにある。

よって次の実装では、Phase A から順に着手する。
