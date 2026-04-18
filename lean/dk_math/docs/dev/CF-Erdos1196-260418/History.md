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

### 日時: 2026/04/18 17:24 JST (ABC bridge の追加)

1. 目的:
   - Phase D として `ABC/MassBridge.lean` および `ABC/ValuationFlowBridge.lean` を追加し、
     既存の Mass API / ValuationFlow API を ABC 側の語彙で読めるようにする。
2. 実施:
   - `docs/dev/CF-Erdos1196-260418/reviewer/review-001.md` を確認し、
     bridge 側の最初の補題候補をレビュー提案に合わせた。
   - 新規追加:
     - `DkMath/ABC/MassBridge.lean`
     - `DkMath/ABC/ValuationFlowBridge.lean`
   - `MassBridge` では
     - `supportMass := DkMath.ABC.Rad.rad`
     - `abc_big_eq_body_add_gap_mass`
     - `abc_gap_mass_le_big_mass`
     - `abc_residual_eq_gap_mass`
     - `abc_squarefree_support_lower_bound`
     - `abc_supportMass_dvd_self`
     を追加した。
   - `ValuationFlowBridge` では
     - `primitive_prime_gives_zero_boundary_load`
     - `primitive_prime_transfers_diff_load_to_beam`
     - `squarefree_beam_bounds_local_load`
     を追加した。
3. 結論:
   - 計画していた ABC bridge の最小核は入った。
   - これで「宇宙式の保存則 API」と「primitive valuation spine」を、ABC 側で直接参照できる薄い翻訳層が揃った。
4. 検証:
   - `cd lean/dk_math && ./lean-build.sh DkMath.ABC.MassBridge`
   - `cd lean/dk_math && ./lean-build.sh DkMath.ABC.ValuationFlowBridge`
   - `ValuationFlowBridge` build では既存 `ZsigmondyCyclotomicResearch.lean` の `sorry` 警告が replay されたが、
     追加した bridge ファイル自体の build は成功した。
5. 失敗事例:
   - なし。今回の bridge 追加では型修正は不要だった。
6. 次の課題:
   - Phase E として concrete example を追加するか、
     あるいは `ABC.Main` などへの公開 import 導線を整えて、利用側の import を簡略化する。

### 日時: 2026/04/18 17:36 JST (Phase E: bridge concrete example の追加)

1. 目的:
   - `review-002.md` の提案に従い、まず bridge の concrete example を追加して、
     今回の ABC bridge が空抽象ではなく既存 concrete 対象に使えることを確認する。
2. 実施:
   - `docs/dev/CF-Erdos1196-260418/reviewer/review-002.md` を確認し、
     public import 整備より先に concrete example を通す方針を採用した。
   - 新規追加:
     - `DkMath/ABC/MassBridgeExamples.lean`
     - `DkMath/ABC/ValuationFlowBridgeExamples.lean`
   - `MassBridgeExamples` では
     - `abc_big_eq_body_add_gap_mass`
     - `abc_gap_mass_le_big_mass`
     - `abc_residual_eq_gap_mass`
     - `abc_squarefree_support_lower_bound`
     - `abc_supportMass_dvd_self`
     の concrete example を追加した。
   - `ValuationFlowBridgeExamples` では、
     `31` が `2^5 - 1` の primitive prime である具体例を使って
     - `primitive_prime_gives_zero_boundary_load`
     - `primitive_prime_transfers_diff_load_to_beam`
     - `squarefree_beam_bounds_local_load`
     の concrete example を追加した。
3. 結論:
   - bridge は concrete 例に対して実際に使えることを確認できた。
   - これで「Mass API -> ABC bridge」「ValuationFlow primitive spine -> ABC bridge」の双方に、
     最低限の使用例が付いた。
4. 検証:
   - `cd lean/dk_math && ./lean-build.sh DkMath.ABC.MassBridgeExamples`
   - `cd lean/dk_math && ./lean-build.sh DkMath.ABC.ValuationFlowBridgeExamples`
   - `ValuationFlowBridgeExamples` の build では既存 `ZsigmondyCyclotomicResearch.lean` の `sorry` 警告が replay されたが、
     追加した example ファイル自体の build は成功した。
5. 失敗事例:
   - `MassBridgeExamples` の初版では `Squarefree 30` を `decide` / `native_decide` で閉じようとして不適切だったため、
     prime sample `31` に差し替えて `Prime.squarefree` で処理した。
   - `ValuationFlowBridgeExamples` の初版では `GN` を直接展開して squarefree を示そうとして式が広がりすぎたため、
     先に `GN 5 1 1 = 31` を固定してから `31` の squarefree を流す形へ修正した。
6. 次の課題:
   - `ABC.Main` などへの公開 import 導線を整えるか、
     あるいは `rad_lower_bound_of_disjoint_channels` に向けた最小補題設計へ進む。

### 日時: 2026/04/18 17:47 JST (`supportMass` と distinct prime channels の接続)

1. 目的:
   - `review-003.md` の提案に従い、公開 import 整備より先に
     `rad_lower_bound_of_disjoint_channels` に向けた最小補題を `MassBridge` 側へ追加する。
2. 実施:
   - `DkMath/ABC/MassBridge.lean` に次を追加した。
     - `supportMass_pos`
     - `supportMass_dvd_of_prime_channel`
     - `pairwise_distinct_channels_mul_dvd_supportMass`
     - `supportMass_ge_of_two_distinct_prime_channels`
   - ここで channel は当面「prime divisor witness」を意味するものとして固定した。
   - `DkMath/ABC/MassBridgeExamples.lean` に、
     `2` と `3` が `12` の distinct prime channels であることから
     `2 * 3 ≤ supportMass 12` を得る concrete example を追加した。
3. 結論:
   - `supportMass = rad` と prime channel counting を結ぶ最小の lower-bound spine が入った。
   - これで bridge 群は「保存則」「valuation flow」「support mass 下界」の 3 点で一段つながった。
4. 検証:
   - `cd lean/dk_math && ./lean-build.sh DkMath.ABC.MassBridge`
   - `cd lean/dk_math && ./lean-build.sh DkMath.ABC.MassBridgeExamples`
5. 失敗事例:
   - なし。今回の補題追加は既存 `mem_support_factorization_iff` と prime coprime 補題でそのまま閉じた。
6. 次の課題:
   - `ValuationFlow` 側で「異なる primitive witness は異なる prime channel を与える」
     という薄い補題設計へ進み、
     support mass 下界と primitive channel counting をさらに接続する。
