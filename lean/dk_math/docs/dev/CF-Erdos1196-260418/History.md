# History

cid: 69e0651d-a220-83e8-a107-0029563409dc

- 時刻の打刻は `date` コマンドを使用して時間(時分秒)まで正確に行うこと。
- 新規履歴は **ファイル末尾** に追加すること。

## History Log

Archive

過去ログは、以下にアーカイブしてあります。

- [001](History-001.md)

## Note

タイムスタンプの打刻は `date` コマンドを使用して、実際の日時を正確に記録してください。例: `date "+%Y/%m/%d %H:%M JST"` など。

※コミット時間がより正確であり、異なる場合は、コミット時間を優先とする。

## Template

### 日時: `タイムスタンプ date コマンドを使用して年月日時分まで` JST (作業概要の見出し)

1. 目的:
   - （内容）
2. 実施:
   - （内容）
3. 結論:
   - （内容）
4. 検証:
   - （内容）
5. 失敗事例:
   - （内容）
6. 次の課題:
   - （内容）

### 日時: 2026/04/18 16:50 JST (Erdos #1196 実装計画の固定)

1. 目的:
   - `CosmicFormula-Erdos1196-*` 文書を読み、既存ワークスペースを踏まえた実装順序を確定する。
2. 実施:
   - `docs/__AGENT.md` を確認し、`History.md` の継続更新と単体 build 方針を再確認した。
   - `CosmicFormula-Erdos1196-design.md` と `CosmicFormula-Erdos1196-discussion.md` を読んだ。
   - 既存コードとして `CoreBeamGap`, `ResidualNat`, `ResidualInt`, `PrimitiveBeam`, `ZsigmondyCyclotomicSquarefree`, `ABC/PadicValNat`, `ABC/Rad` を調査した。
   - `ImplementsPlan.md` を更新し、Phase A-D の実装順序と build 対象を具体化した。
3. 結論:
   - 初手は確率 kernel の完全形式化ではなく、`CosmicFormula` の保存則 API と primitive/valuation flow の骨格を先に実装する方針で固定した。
   - 既存資産が十分あるため、新設は wrapper / bridge 中心で進める。
4. 検証:
   - ドキュメントと関連 Lean ファイルの対応関係を確認した。
   - `git status --short` は空で、作業木に未整理変更が無いことを確認した。
5. 失敗事例:
   - なし。
6. 次の課題:
   - `ImplementsPlan.md` の Phase A に従い、`CosmicFormula/Mass/Core.lean` と `Decompose.lean` から実装を開始する。

### 日時: 2026/04/18 17:03 JST (Phase A-B 実装 + ValuationFlow 入口追加)

1. 目的:
   - `ImplementsPlan.md` の Phase A-B を実装し、続けて Phase C の入口となる valuation-flow 名の wrapper を追加する。
2. 実施:
   - 新規追加:
     - `DkMath/CosmicFormula/Mass/Core.lean`
     - `DkMath/CosmicFormula/Mass/Decompose.lean`
     - `DkMath/CosmicFormula/Mass/Branch.lean`
     - `DkMath/NumberTheory/ValuationFlow/Basic.lean`
     - `DkMath/NumberTheory/ValuationFlow/Primitive.lean`
   - 更新:
     - `DkMath/CosmicFormula/Basic.lean` に新設 Mass API の import を追加した。
   - `Mass.Core` では `MassSpace`, `CosmicPart`, `CosmicMassAPI`, `CosmicResidualMassAPI` と、
     `CoreBeamGap` / `ResidualNat` / `ResidualInt` からの concrete API を定義した。
   - `Mass.Decompose` では、既存 `CoreBeamGap` / `ResidualNat` / `ResidualInt` の分解定理を
     `mass_*` 名の wrapper として再公開した。
   - `Mass.Branch` では `Branching`, `outgoingMass`, `SubConservative`,
     `outgoingMass_nonneg`, `outgoingMass_le_mass`, `branch_sum_le_parent` を追加した。
   - `ValuationFlow.Basic` では `diffMass`, `boundaryMass`, `beamMass` と
     `profileOfPrime` を定義した。
   - `ValuationFlow.Primitive` では `PrimitiveBeam` の既存補題を
     valuation-flow 命名で再公開した。
3. 結論:
   - #1196 向けの最初の骨格として、`CosmicFormula` 側の保存則 API と、
     primitive prime から beam / valuation へ流す spine が Lean 上で独立モジュール化できた。
   - これにより次段階は `ABC bridge` を薄く足すか、`ValuationFlow` の抽象層を厚くするかの二択になった。
4. 検証:
   - `cd lean/dk_math && ./lean-build.sh DkMath.CosmicFormula.Mass.Core`
   - `cd lean/dk_math && ./lean-build.sh DkMath.CosmicFormula.Mass.Decompose`
   - `cd lean/dk_math && ./lean-build.sh DkMath.CosmicFormula.Mass.Branch`
   - `cd lean/dk_math && ./lean-build.sh DkMath.CosmicFormula.Basic`
   - `cd lean/dk_math && ./lean-build.sh DkMath.NumberTheory.ValuationFlow.Basic`
   - `cd lean/dk_math && ./lean-build.sh DkMath.NumberTheory.ValuationFlow.Primitive`
   - `ValuationFlow.Primitive` の build では既存 `ZsigmondyCyclotomicResearch.lean` の `sorry` 警告が replay されたが、
     今回追加ファイル自体の build は成功した。
5. 失敗事例:
   - `Mass.Core` の初版では `CoreBeamGap.Core` / `Gap` の引数数が `CosmicMassAPI` と一致せず、
     unused 引数を受ける wrapper に修正した。
   - `Mass.Decompose` では `Nat` / `Int` 版の等式向きにズレがあり、`symm` を入れて整えた。
   - `Mass.Branch` では最初の `∑ ... in ...` 記法が落ちたため、`Finset.sum` へ書き換えた。
6. 次の課題:
   - `ABC/MassBridge.lean` と `ABC/ValuationFlowBridge.lean` を追加し、
     `rad` / `squarefree` / `padicValNat` を今回の API へ橋渡しする。
