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

### 日時: 2026/04/18 18:46 JST (primitive witness から support mass 下界への接続)

1. 目的:
   - `review-004.md` の提案に従い、`ValuationFlow` 側で
     primitive witness から prime channel を取り出し、
     support mass 下界へ流す最小 spine を追加する。
2. 実施:
   - `DkMath/NumberTheory/ValuationFlow/Primitive.lean` に次を追加した。
     - `primitivePrimeFlow_prime`
     - `primitivePrimeFlow_dvd_diff`
   - `DkMath/ABC/ValuationFlowBridge.lean` に次を追加した。
     - `primitive_witness_gives_prime_channel_on_diff`
     - `distinct_primitive_witnesses_give_distinct_prime_channels`
     - `primitive_channels_force_supportMass_lower_bound`
   - `DkMath/ABC/ValuationFlowBridgeExamples.lean` に、
     `6^3 - 5^3 = 91 = 7 * 13` を使った 2 本 primitive channel 例を追加した。
     - `7` と `13` の primitive witness
     - distinct primitive witnesses から diff 側の 2 本 prime channel を得る例
     - `7 * 13 ≤ supportMass (6^3 - 5^3)` の例
3. 結論:
   - `primitive flow -> disjoint channels -> supportMass lower bound`
     の最小核が Lean 上で一本つながった。
   - これにより、prime divisor channel 版と primitive flow 版の lower-bound spine の対応が見えるようになった。
4. 検証:
   - `cd lean/dk_math && ./lean-build.sh DkMath.NumberTheory.ValuationFlow.Primitive`
   - `cd lean/dk_math && ./lean-build.sh DkMath.ABC.ValuationFlowBridge`
   - `cd lean/dk_math && ./lean-build.sh DkMath.ABC.ValuationFlowBridgeExamples`
   - 各 build では既存 `ZsigmondyCyclotomicResearch.lean` の `sorry` 警告が replay されたが、
     今回追加・更新したファイル自体の build は成功した。
5. 失敗事例:
   - なし。今回の追加は既存 primitive witness API と `supportMass` 下界補題の合成だけで閉じた。
6. 次の課題:
   - `ABC.Main` などへの公開 import 導線を整えるか、
     あるいは 2 本 channel 版を `Finset` / pairwise family 版へ一般化する設計へ進む。

### 日時: 2026/04/18 19:05 JST (`Finset` family 版 support-mass 下界の追加)

1. 目的:
   - `review-005.md` の提案に従い、2-channel 版で止まっていた
     `supportMass` 下界を `Finset` family 版へ一般化する。
   - あわせて、primitive witness family から同じ lower bound へ流す最小 adapter を追加する。
2. 実施:
   - `DkMath/ABC/MassBridge.lean` に次を追加した。
     - `prime_channel_family_prod_dvd_supportMass`
     - `pairwise_distinct_prime_channel_family_lower_bound`
     - `supportMass_ge_prod_of_prime_channel_family`
   - `Finset` を index に使うことで、distinctness は集合側に吸収し、
     各 member が `Nat.Prime p ∧ p ∣ n` を満たすだけの statement に整理した。
   - `DkMath/ABC/ValuationFlowBridge.lean` に次を追加した。
     - `primitive_witness_family_gives_prime_channel_family_on_diff`
     - `primitive_witness_family_force_supportMass_lower_bound`
   - `DkMath/ABC/MassBridgeExamples.lean` に
     `({2, 3} : Finset ℕ).prod id ≤ supportMass 12` を追加した。
   - `DkMath/ABC/ValuationFlowBridgeExamples.lean` に
     `({7, 13} : Finset ℕ).prod id ≤ supportMass (6 ^ 3 - 5 ^ 3)` を追加した。
3. 結論:
   - `supportMass = rad` 側の lower-bound spine が、
     2 本 channel 版から有限 family 版へ上がった。
   - 同時に `primitive witness family -> prime channel family -> supportMass lower bound`
     という有限集合レベルの導線も最小形で入った。
4. 検証:
   - `cd lean/dk_math && ./lean-build.sh DkMath.ABC.MassBridge`
   - `cd lean/dk_math && ./lean-build.sh DkMath.ABC.MassBridgeExamples`
   - `cd lean/dk_math && ./lean-build.sh DkMath.ABC.ValuationFlowBridge`
   - `cd lean/dk_math && ./lean-build.sh DkMath.ABC.ValuationFlowBridgeExamples`
   - `ValuationFlowBridge` 系の build では既存 `ZsigmondyCyclotomicResearch.lean` の `sorry` 警告が replay されたが、
     今回追加した bridge / example は成功した。
5. 失敗事例:
   - `ValuationFlowBridgeExamples` の初版では `({7, 13} : Finset ℕ)` の membership 展開順を取り違え、
     `primitiveWitnessFamily_6_5_3` の branch が逆になって build が落ちた。
   - branch 順を修正し、example は通るようにした。
6. 次の課題:
   - family 版を public import へどう露出するか整理する。
   - あるいは primitive witness family をより構造的に管理する API
     (`Finset` 上の witness packaging や後続の counting lemma) へ進む。

### 日時: 2026/04/18 19:13 JST (primitive witness family の package 化)

1. 目的:
   - `review-006.md` の提案に従い、public import 整備より先に
     primitive witness family を再利用しやすい小さな package にまとめる。
2. 実施:
   - `DkMath/ABC/ValuationFlowBridge.lean` に
     `PrimitiveWitnessFamily (a b d)` structure を追加した。
     - `support : Finset ℕ`
     - `witness : ∀ q ∈ support, PrimitivePrimeFlowWitness q a b d`
   - あわせて package 経由の薄い API として
     - `PrimitiveWitnessFamily.primeChannelFamily`
     - `PrimitiveWitnessFamily.supportMassLowerBound`
     を追加した。
   - `DkMath/ABC/ValuationFlowBridgeExamples.lean` に
     `{7, 13}` の既存 family を package 化した
     `primitiveWitnessFamilyPack_6_5_3`
     を追加し、
     package 経由で prime-channel family と support-mass lower bound が読める例を足した。
3. 結論:
   - `∀ q ∈ S, PrimitivePrimeFlowWitness ...` を毎回直接渡さなくても、
     family を一塊として扱う最小 API が入った。
   - これで public import を整える前の段階として、
     family bridge の重心が少し安定した。
4. 検証:
   - `cd lean/dk_math && ./lean-build.sh DkMath.ABC.ValuationFlowBridge`
   - `cd lean/dk_math && ./lean-build.sh DkMath.ABC.ValuationFlowBridgeExamples`
   - build では既存 `ZsigmondyCyclotomicResearch.lean` の `sorry` 警告が replay されたが、
     今回更新した bridge / example は成功した。
5. 失敗事例:
   - package example の初版では、
     `7 ∈ primitiveWitnessFamilyPack_6_5_3.support` の証明を
     `simp only` で閉じ切れず goal が残った。
   - ここは example 側だけ `simp [primitiveWitnessFamilyPack_6_5_3]` に変えて解消した。
6. 次の課題:
   - `ABC.Main` や公開 import 導線を整えて、新しい bridge API を表に出す。
   - あるいは package 化した witness family を使う counting / extraction 補題へ進む。

### 日時: 2026/04/18 19:21 JST (public import 導線の整備)

1. 目的:
   - `review-007.md` の提案に従い、package 化まで済ませた bridge API を
     短い import で利用できるよう公開導線を整える。
2. 実施:
   - `DkMath/ABC/Bridge.lean` を新設し、
     - `DkMath.ABC.MassBridge`
     - `DkMath.ABC.ValuationFlowBridge`
     を薄く集約する public-facing aggregator を追加した。
   - `DkMath/ABC/Main.lean` に `import DkMath.ABC.Bridge` を追加し、
     既存 top-level 導線 `DkMath.ABC -> DkMath.ABC.Main` から bridge API が見えるようにした。
   - `DkMath/ABC/BridgeExamples.lean` を新設し、
     `import DkMath.ABC.Bridge` だけで
     - `supportMass_ge_prod_of_prime_channel_family`
     - `PrimitiveWitnessFamily`
     - `PrimitiveWitnessFamily.primeChannelFamily`
     - `PrimitiveWitnessFamily.supportMassLowerBound`
     が使えることを確認する usage example を追加した。
   - primitive witness package の public example では、
     構成を最小化するため `8^1 - 1^1 = 7` の singleton sample を採用した。
3. 結論:
   - bridge API を implementation file 名に依存せず、
     `DkMath.ABC.Bridge` またはそれを含む `DkMath.ABC.Main` から読めるようになった。
   - これで外部利用側の import 導線が一段整理された。
4. 検証:
   - `cd lean/dk_math && ./lean-build.sh DkMath.ABC.Bridge`
   - `cd lean/dk_math && ./lean-build.sh DkMath.ABC.Main`
   - `cd lean/dk_math && ./lean-build.sh DkMath.ABC.BridgeExamples`
   - `Bridge` / `BridgeExamples` の build では既存 `ZsigmondyCyclotomicResearch.lean` の `sorry` 警告が replay された。
   - `Main` build では加えて既存 `ABC021.lean` の `sorry` 警告が replay されたが、今回の更新対象は成功した。
5. 失敗事例:
   - なし。public usage example も初回 build で通った。
6. 次の課題:
   - `DkMath.ABC` 直下でどこまで bridge API を canonical import とみなすか整理する。
   - あるいは `PrimitiveWitnessFamily` に対する counting / extraction 補題を追加して、
     public API の中身をもう一段厚くする。

### 日時: 2026/04/18 19:55 JST (public counting / extraction alias の追加)

1. 目的:
   - `review-008.md` の提案に従い、public surface を厚くしすぎずに
     `PrimitiveWitnessFamily` の最小 counting / extraction API を 1 段だけ追加する。
2. 実施:
   - `DkMath/ABC/ValuationFlowBridge.lean` の `PrimitiveWitnessFamily` namespace に
     - `channelProduct`
     - `channelProduct_eq_support_prod`
     - `channelProduct_le_supportMass`
     を追加した。
   - `channelProduct` は `support.prod id` の public-facing alias とし、
     `channelProduct_le_supportMass` は既存 `supportMassLowerBound` の
     channel-product 名による再公開に留めた。
   - `DkMath/ABC/BridgeExamples.lean` に
     - `primitiveWitnessFamilyPack_8_1_1.channelProduct = 7`
     - `primitiveWitnessFamilyPack_8_1_1.channelProduct ≤ supportMass (8 ^ 1 - 1 ^ 1)`
     の public usage example を追加した。
3. 結論:
   - public import から
     - support 集合
     - support の product
     - supportMass 下界
     の関係を method 名で読みやすくする最小 API が入った。
   - これで `PrimitiveWitnessFamily` の公開面は、
     structure / channel family / lower bound / channel product まで一通り揃った。
4. 検証:
   - `cd lean/dk_math && ./lean-build.sh DkMath.ABC.ValuationFlowBridge`
   - `cd lean/dk_math && ./lean-build.sh DkMath.ABC.BridgeExamples`
   - build では既存 `ZsigmondyCyclotomicResearch.lean` の `sorry` 警告が replay されたが、
     今回更新した bridge / example は成功した。
5. 失敗事例:
   - なし。今回の alias 追加は既存 lower-bound API の再包装だけで閉じた。
6. 次の課題:
   - `DkMath.ABC.Bridge` を推奨入口として文書側へ明示する。
   - あるいは `PrimitiveWitnessFamily` の次の counting / extraction 段
     （例えば support size や extracted channel family の読み出し）へ進む。

### 日時: 2026/04/18 20:10 JST (`channelCount` と member-wise extraction の追加)

1. 目的:
   - `review-009.md` の提案に従い、`channelProduct` の次の counting / extraction 段として
     `PrimitiveWitnessFamily` に card 語彙と member-wise extraction method を追加する。
2. 実施:
   - `DkMath/ABC/ValuationFlowBridge.lean` の `PrimitiveWitnessFamily` namespace に
     - `channelCount`
     - `channelCount_eq_support_card`
     - `mem_support_implies_prime_and_dvd_diff`
     - `mem_support_implies_prime_channel`
     - `mem_support_implies_dvd_diff`
     を追加した。
   - いずれも既存
     - `support.card`
     - `primeChannelFamily`
     の再包装に徹し、新しい heavy lemma は足していない。
   - `DkMath/ABC/BridgeExamples.lean` に public import 経由の usage example として
     - `primitiveWitnessFamilyPack_8_1_1.channelCount = 1`
     - support member `7` が prime diff channel である例
     - support member `7` が prime である例
     - support member `7` が diff を割る例
     を追加した。
3. 結論:
   - `PrimitiveWitnessFamily` の public surface に
     multiplicative size (`channelProduct`) に加えて
     cardinality (`channelCount`) と member-wise extraction が入った。
   - これで counting / extraction 段の最小セットはかなり揃った。
4. 検証:
   - `cd lean/dk_math && ./lean-build.sh DkMath.ABC.ValuationFlowBridge`
   - `cd lean/dk_math && ./lean-build.sh DkMath.ABC.BridgeExamples`
   - build では既存 `ZsigmondyCyclotomicResearch.lean` の `sorry` 警告が replay されたが、
     今回更新した bridge / example は成功した。
5. 失敗事例:
   - なし。今回の counting / extraction 追加は既存 API の method 名再包装で閉じた。
6. 次の課題:
   - `channelCount` と `channelProduct` を併用する counting 補題へ進む。
   - あるいは `DkMath.ABC.Bridge` を推奨入口として文書側に明示する。

### 日時: 2026/04/18 21:09 JST (`INDEX.md` 追記と `count -> product -> supportMass` の追加)

1. 目的:
   - ユーザー指示に従い、`DkMath.ABC.Bridge` を推奨入口として `INDEX.md` に明示する。
   - あわせて `review-010.md` の提案に従い、
     `channelCount` と `channelProduct` を結ぶ counting 補題を追加する。
2. 実施:
   - `INDEX.md` の `3.2 ABC まわり` 節に
     `DkMath.ABC.Bridge` を Erdos #1196 系 bridge API の推奨入口として追記した。
   - `DkMath/ABC/ValuationFlowBridge.lean` の `PrimitiveWitnessFamily` namespace に
     - `mem_support_implies_two_le`
     - `pow_channelCount_le_channelProduct`
     - `pow_channelCount_le_supportMass`
     を追加した。
   - `pow_channelCount_le_channelProduct` の証明には、
     support の各元が prime なので `2 ≤ q` を満たすことと、
     `Finset` の card/product に対する帰納法だけを使った。
   - `DkMath/ABC/BridgeExamples.lean` に public import 経由の usage example として
     - `2 ^ channelCount ≤ channelProduct`
     - `2 ^ channelCount ≤ supportMass (...)`
     を追加した。
3. 結論:
   - 文書側では `DkMath.ABC.Bridge` が bridge API の標準入口として明示された。
   - Lean 側では `channelCount -> channelProduct -> supportMass` の最小 counting spine が入った。
4. 検証:
   - `cd lean/dk_math && ./lean-build.sh DkMath.ABC.ValuationFlowBridge`
   - `cd lean/dk_math && ./lean-build.sh DkMath.ABC.BridgeExamples`
   - build では既存 `ZsigmondyCyclotomicResearch.lean` の `sorry` 警告が replay されたが、
     今回更新した bridge / example は成功した。
5. 失敗事例:
   - `pow_channelCount_le_channelProduct` の初版では、
     `Nat.pow_succ` による積の向きが `2 ^ s.card * 2` になり、
     `2 * 2 ^ s.card` への整形が不足して build が落ちた。
   - 等式を `Nat.mul_comm` で明示的に繋ぐ形へ修正して解消した。
6. 次の課題:
   - `channelCount` と `supportMass` の下界を concrete family 例で増やすか、
     あるいは `PrimitiveWitnessFamily` を既存 ABC 本体のどの命題へ差し込むか整理する。

### 日時: 2026/04/18 21:20 JST (2-channel concrete family の public sample 追加)

1. 目的:
   - `review-011.md` の提案に従い、singleton sample だけでなく
     2-channel concrete family でも counting spine が public import 経由で読めることを確認する。
2. 実施:
   - `DkMath/ABC/BridgeExamples.lean` に
     `primitiveWitnessFamilyPack_6_5_3 : PrimitiveWitnessFamily 6 5 3`
     を追加した。
   - support は `({7, 13} : Finset ℕ)` とし、
     `6^3 - 5^3 = 91 = 7 * 13` に対応する 2 本 primitive witness を
     `interval_cases` と `decide` で構成した。
   - 同ファイルに public import 経由の usage example として
     - `channelCount = 2`
     - `channelProduct = 7 * 13`
     - `2 ^ channelCount ≤ channelProduct`
     - `2 ^ channelCount ≤ supportMass (6 ^ 3 - 5 ^ 3)`
     を追加した。
3. 結論:
   - counting spine
     `channelCount -> channelProduct -> supportMass`
     が singleton だけでなく 2-channel concrete family でも public surface 上で読めるようになった。
   - これで counting API の効き方が具体例としてかなり見えやすくなった。
4. 検証:
   - `cd lean/dk_math && ./lean-build.sh DkMath.ABC.BridgeExamples`
   - build では既存 `ZsigmondyCyclotomicResearch.lean` の `sorry` 警告が replay されたが、
     今回更新した example は成功した。
5. 失敗事例:
   - 初版では 2 本 primitive witness の構成に `omega` を使ったが、
     divisibility を含む primitive 条件を処理できず build が落ちた。
   - ここは `interval_cases k <;> decide` に切り替えて解消した。
6. 次の課題:
   - `PrimitiveWitnessFamily` の counting spine を既存 ABC 本体のどの命題へ差し込むか整理する。
   - あるいは concrete family をさらに追加して、public API の利用例を厚くする。

### 日時: 2026/04/18 22:07 JST (`ABC.rad` 語彙への直接 alias 追加)

1. 目的:
   - `review-012.md` の流れに従い、bridge counting spine を
     `supportMass` だけでなく既存 ABC 本体が直接使う `ABC.rad` 語彙でも読めるようにする。
2. 実施:
   - `DkMath/ABC/ValuationFlowBridge.lean` の `PrimitiveWitnessFamily` namespace に
     - `channelProduct_le_abc_rad_diff`
     - `pow_channelCount_le_abc_rad_diff`
     を追加した。
   - いずれも既存
     - `channelProduct_le_supportMass`
     - `pow_channelCount_le_supportMass`
     と `supportMass_eq_abc_rad`
     の合成だけで閉じた alias である。
   - `DkMath/ABC/BridgeExamples.lean` に 2-channel sample `primitiveWitnessFamilyPack_6_5_3`
     を使った public usage example として
     - `channelProduct ≤ ABC.rad (6 ^ 3 - 5 ^ 3)`
     - `2 ^ channelCount ≤ ABC.rad (6 ^ 3 - 5 ^ 3)`
     を追加した。
3. 結論:
   - counting spine が bridge 専用語彙 `supportMass` だけでなく、
     ABC 本体で広く使われる `ABC.rad` へ直接着地する形になった。
   - これで既存 ABC コア命題へ差し込むための最小 alias が入った。
4. 検証:
   - `cd lean/dk_math && ./lean-build.sh DkMath.ABC.ValuationFlowBridge`
   - `cd lean/dk_math && ./lean-build.sh DkMath.ABC.BridgeExamples`
   - build では既存 `ZsigmondyCyclotomicResearch.lean` の `sorry` 警告が replay されたが、
     今回更新した bridge / example は成功した。
5. 失敗事例:
   - なし。今回の追加は既存 lower-bound spine と `supportMass_eq_abc_rad` の再包装だけで閉じた。
6. 次の課題:
   - `ABC016` / `ABC002` など既存 ABC コアの `rad`・quality 系命題で、
     この alias を差し込める箇所を具体化する。
   - あるいは `ABC.rad` 語彙での concrete family 例をさらに増やす。

### 日時: 2026/04/18 22:14 JST (ABC コア差し込み候補の整理)

1. 目的:
   - `review-013.md` の提案に従い、bridge spine を既存 ABC コアへ差し込む候補を 3 箇所まで抽出し、
     現 API で足りる点と不足補題を切り分ける。
2. 実施:
   - `ABC016.lean`, `ABC002.lean`, `ABC038.lean`, `RatioBound.lean` を点検し、
     `rad`・quality・count 系で bridge が刺さる位置を確認した。
   - 調査結果を
     [ABCCoreInsertionCandidates.md](ABCCoreInsertionCandidates.md)
     に整理した。
   - 候補は次の 3 件に絞った。
     - `ABC038.quality_le_of_not_bad_with_tail` / `quality_le_of_not_bad_with_log`
     - `ABC016.twoTail_le_rad_pow_of_log_bound`
     - `RatioBound.count_with_rad_eq_le_div`
   - 各候補について、
     - いまの bridge alias だけで足りるか
     - `rad(diff)` と `rad(a*b)` のズレ
     - family existence / packaging / count-class corollary のどれが不足か
     を明記した。
3. 結論:
   - 既存 ABC コアへの差し込み候補と、その手前に要る補題の種類が整理された。
   - 現時点で最も実装に近いのは `RatioBound.count_with_rad_eq_le_div` 周辺で、
     quality 本体 (`ABC038`, `ABC016`) はもう 1 本中間命題が必要だと分かった。
4. 検証:
   - 今回は調査・文書整理のみで、Lean コードの追加は行っていない。
5. 失敗事例:
   - なし。
6. 次の課題:
   - `RatioBound` 側に `rad lower bound -> count upper bound` の薄い corollary を足す。
   - あるいは `ABC038` へ進む前段として、`rad(diff)` を quality 入力へ送る中間命題を設計する。

### 日時: 2026/04/18 22:31 JST (`RatioBound` 候補への最小差し込み)

1. 目的:
   - `review-014.md` の提案に従い、候補 1 だった `RatioBound.count_with_rad_eq_le_div`
     周辺へ bridge spine を実際に差し込む。
2. 実施:
   - `DkMath/ABC/RatioBound.lean` に
     `count_with_rad_eq_le_div_of_lower_bound`
     を追加した。
     - これは `rad a = r` の exact class に対して、
       任意の正の lower bound `R ≤ r` から
       `X / R + 1` 型の count upper bound を出す薄い単調性版である。
   - `DkMath/ABC/ValuationFlowBridge.lean` には
     `PrimitiveWitnessFamily.count_class_with_same_rad_as_diff_le_of_channelCount`
     を追加した。
     - `pow_channelCount_le_abc_rad_diff`
       と上の `RatioBound` corollary を合成し、
       `diff` と同じ `ABC.rad` を持つ count class が
       `X / 2^channelCount + 1` 型で抑えられることを示す。
   - `DkMath/ABC/BridgeExamples.lean` に
     `primitiveWitnessFamilyPack_6_5_3` を使った public usage example として、
     `rad` class の個数が `100 / 2^channelCount + 1` 型で抑えられる例を追加した。
3. 結論:
   - 前回候補整理した `RatioBound` ルートに対して、
     bridge spine から実際の count upper bound へ流れる最小接続が入った。
   - これで `PrimitiveWitnessFamily` の counting spine は、
     `ABC.rad` 下界だけでなく count-class 上界へも到達するようになった。
4. 検証:
   - `cd lean/dk_math && ./lean-build.sh DkMath.ABC.RatioBound`
   - `cd lean/dk_math && ./lean-build.sh DkMath.ABC.ValuationFlowBridge`
   - `cd lean/dk_math && ./lean-build.sh DkMath.ABC.BridgeExamples`
   - `ValuationFlowBridge` / `BridgeExamples` の build では既存 `ZsigmondyCyclotomicResearch.lean` の
     `sorry` 警告が replay されたが、今回更新したファイルは成功した。
5. 失敗事例:
   - `RatioBound` 初版では `Nat.div_le_div_right` を使って
     `X / r ≤ X / R` を示そうとしたが、定理の向きが合わず build が落ちた。
   - ここは `Nat.le_div_iff_mul_le` と `Nat.div_mul_le_self` を使う直接証明へ切り替えて解消した。
   - `ValuationFlowBridge` 側では theorem 名解決で `ABC.` 修飾が必要だったため、明示して解消した。
6. 次の課題:
   - `ABC038` quality 系へ進む前段として、
     `rad(diff)` 下界を `rad(a*b)` 入力へ送る中間命題を設計する。
   - あるいは `RatioBound` 側で `rad ≥ R` class をさらにまとめて数える補題へ進む。

### 日時: 2026/04/18 22:41 JST (`ABC038` 前段の dependency chain 整理)

1. 目的:
   - `review-015.md` の提案に従い、`ABC038` quality 系へ進む前段として
     `rad(diff)` 下界を `rad(a*b)` 入力へ送る中間命題の dependency chain を theorem 名レベルで整理する。
2. 実施:
   - `ABC038.lean` の
     - `quality_le_of_not_bad_with_tail`
     - `quality_le_of_not_bad_with_log`
     を再読し、quality 側が実際に欲している入力が
     `ABC.rad (a * b)` であることを確認した。
   - `ValuationFlowBridge.lean` と前回の候補整理を踏まえ、
     bridge 側の `ABC.rad(diff)` 下界から quality 入力へ送るための
     中間命題候補を整理した。
   - 結果を
     [ABC038BridgeDependency.md](ABC038BridgeDependency.md)
     にまとめた。
   - とくに次の 3 層を明示した。
     - radical transport
     - witness family on triple / target
     - quality-input lower bound wrapper
3. 結論:
   - `ABC038` へ差し込む前に何が足りないかが、
     theorem 名と仮定の粒度で切り分けられた。
   - 次に実装すべき最小候補は
     - `primitive_witness_family_gives_abc_rad_target_lower_bound`
     - `primitive_channel_count_forces_quality_rad_input`
     の 2 本である。
4. 検証:
   - 今回は設計整理のみで、Lean コードの追加や build は行っていない。
5. 失敗事例:
   - なし。
6. 次の課題:
   - 上記 2 本の中間命題を Lean に実装する。
   - あるいは `ABC038` 側へ入る前に、`rad(diff) ≤ rad(a*b)` 型 transport hypothesis の自然な供給元を決める。

### 日時: 2026/04/18 23:04 JST (`ABC038` 向け TailBound wrapper の追加)

1. 目的:
   - `review-016.md` の流れを受けて、直前に追加した
     `primitive_witness_family_gives_abc_rad_target_lower_bound`
     / `primitive_channel_count_forces_quality_rad_input`
     を `ABC038` 側の既存 API に実際に接続する最小 wrapper を入れる。
2. 実施:
   - `DkMath/ABC/ValuationFlowBridge.lean` に
     `PrimitiveWitnessFamily.primitive_channel_count_forces_rad_input_lower_bound`
     を追加した。
     - これは既存の quality-input 版を、family 側の基底 `(a,b)` に固定せず、
       任意の radical input `(u,v)` に一般化した薄い transport 補題である。
   - 既存
     `PrimitiveWitnessFamily.primitive_channel_count_forces_quality_rad_input`
     は上の一般化補題の specialization として書き直した。
   - 新規追加:
     - `DkMath/ABC/ABC038Bridge.lean`
     - `DkMath/ABC/ABC038BridgeExamples.lean`
   - `ABC038Bridge` では次を追加した。
     - `tailBound_of_channelCount_tail_transport`
     - `quality_le_of_not_bad_with_channelCount_tail_transport`
   - これにより、`twoTail c ≤ (2 ^ channelCount)^γ` 型の budget と
     `rad c ≤ rad (u * v)` 型 transport から、
     既存 `ABC.TailBound γ u v c` と
     `ABC.Chernoff.quality_le_of_not_bad_with_tail`
     へ流せるようにした。
   - `ABC038BridgeExamples` には
     `6^3 - 5^3 = 91 = 7 * 13` の packaged witness family を再掲し、
     `TailBound 1 91 1 91` を bridge wrapper から読む concrete example を追加した。
3. 結論:
   - `PrimitiveWitnessFamily` の counting spine は、
     単なる `ABC.rad` 下界で止まらず、
     `ABC038` が読む `TailBound` 入力まで届くようになった。
   - これで quality 系との接続は theorem 名レベルでは一段前進した。
   - ただし concrete example は現時点では `TailBound` までに留めた。
     標準の `u + v = c` / `Nat.Coprime u v` を伴う quality sample では、
     `rad c ≤ rad (u * v)` の自然供給がまだ未解決である。
4. 検証:
   - `cd lean/dk_math && ./lean-build.sh DkMath.ABC.ValuationFlowBridge`
   - `cd lean/dk_math && ./lean-build.sh DkMath.ABC.ABC038Bridge`
   - `cd lean/dk_math && ./lean-build.sh DkMath.ABC.ABC038BridgeExamples`
   - `ABC038Bridge` / `ABC038BridgeExamples` の build では既存
     `ABC021.lean` と `ZsigmondyCyclotomicResearch.lean` の `sorry` 警告が replay されたが、
     今回追加・更新したファイル自体は成功した。
5. 失敗事例:
   - `ABC038Bridge` 初版では
     `quality_le_of_not_bad_with_tail` を `ABC.` 直下にあると誤認し、
     実際には `ABC.Chernoff` namespace 配下だったため build が落ちた。
   - `ABC038BridgeExamples` 初版では `native_decide` と
     `decide` による `twoTail 91 = 1` / `Squarefree 91` の直接計算に頼ったが、
     linter と reduction の両面で不安定だった。
   - ここは `twoTail_le_sqTail_real` と
     `sqTail_eq_one_of_squarefree`、さらに
     `Nat.squarefree_mul` を使う構成へ切り替えて解消した。
6. 次の課題:
   - `ABC038` quality sample を実際に閉じるには、
     `u + v = c` と両立する radical transport の自然な供給元を定理化する必要がある。
   - あるいは `TailBound` より手前で使う budget 語彙を `rad c` 側に寄せる中間補題を追加し、
     quality 側への接続条件を緩める。

### 日時: 2026/04/18 23:17 JST (divisibility ベース radical transport の追加)

1. 目的:
   - `review-017.md` の提案に従い、`rad c ≤ rad (u * v)` の自然供給元として
     divisibility ベースの transport route を bridge 層へ追加する。
2. 実施:
   - 既存 `ABC011.lean` に
     - `rad_dvd_of_dvd`
     - `rad_le_of_dvd`
     があることを確認し、これを `ABC038Bridge` 側で薄く再公開する方針を採用した。
   - `DkMath/ABC/ABC038Bridge.lean` に次を追加した。
     - `rad_input_transport_of_target_dvd_mul`
     - `tailBound_of_channelCount_tail_dvd`
     - `quality_le_of_not_bad_with_channelCount_tail_dvd`
   - `rad_input_transport_of_target_dvd_mul` では
     `c ∣ u * v` と `u * v ≠ 0` から
     `rad c ≤ rad (u * v)` を出す。
   - `tailBound_of_channelCount_tail_dvd` / `quality_le_of_not_bad_with_channelCount_tail_dvd`
     は、前回追加した generic transport wrapper を
     divisibility 仮定つきの便利版へ specialization した。
   - `DkMath/ABC/ABC038BridgeExamples.lean` には、
     `14^1 - 7^1 = 7` の one-channel family
     `primitiveWitnessFamilyPack_14_7_1` を追加し、
     `7 ∣ 14 * 7` から `TailBound 1 14 7 7` を読む
     divisibility-route sample を追加した。
3. 結論:
   - `ABC038` 向け radical transport について、
     generic 仮定 `rad c ≤ rad (u * v)` だけでなく、
     その自然供給元のひとつである
     `c ∣ u * v` ルートを theorem 名で固定できた。
   - これにより、transport route の候補は
     「任意 transport 仮定」から
     「divisibility ベースの自然仮定」へ一段具体化された。
4. 検証:
   - `cd lean/dk_math && ./lean-build.sh DkMath.ABC.ABC038Bridge`
   - `cd lean/dk_math && ./lean-build.sh DkMath.ABC.ABC038BridgeExamples`
   - build では既存 `ABC021.lean` と
     `ZsigmondyCyclotomicResearch.lean` の `sorry` 警告が replay されたが、
     今回更新したファイル自体は成功した。
5. 失敗事例:
   - `rad_input_transport_of_target_dvd_mul` 初版では
     `ABC.rad_le_of_dvd` をそのまま使い、
     実数版不等式を自然数版 goal に当てて型不一致で落ちた。
   - ここは `ABC.rad_dvd_of_dvd` と `Nat.le_of_dvd` を使う
     Nat 版の証明へ切り替えて解消した。
   - `ABC038BridgeExamples` では
     `primitiveWitnessFamilyPack_6_5_3` の second branch が
     `primitiveWitnessFamilyPack_14_7_1` 定義に紛れ込み、
     unsolved goal を出した。branch 配置を修正して解消した。
6. 次の課題:
   - divisibility ベース route が実際の `u + v = c` な quality sample に自然に現れるかを洗う。
   - もし現れにくければ、次は `TailBound` 側の入力語彙を `rad c` 基準に寄せる
     input-refactoring route の方が軽いかを比較検討する。

### 日時: 2026/04/19 00:24 JST (target-rad budget route の追加)

1. 目的:
   - `review-018.md` の示唆どおり、divisibility route をこれ以上厚くする前に、
     `TailBound` の入力語彙を `rad c` 基準へ一段寄せる
     input-refactoring route を bridge 層へ追加する。
2. 実施:
   - `DkMath/ABC/ABC038Bridge.lean` に次を追加した。
     - `targetRadTailBound_of_channelCount_tail`
     - `tailBound_of_targetRadTail_transport`
     - `quality_le_of_not_bad_with_targetRadTail_transport`
   - `targetRadTailBound_of_channelCount_tail` では、
     `PrimitiveWitnessFamily` の counting spine と
     `primitive_witness_family_gives_abc_rad_target_lower_bound`
     を使って、
     `twoTail c ≤ (2 ^ channelCount)^γ`
     から
     `twoTail c ≤ (rad c)^γ`
     へ landing させた。
   - `tailBound_of_channelCount_tail_transport` は、
     直接 `2 ^ channelCount` から `rad (u * v)` へ飛ばす形をやめ、
     いったん `rad c` 側 budget に landing してから
     `TailBound` へ transport する構成へ整理した。
   - `DkMath/ABC/ABC038BridgeExamples.lean` には
     `6^3 - 5^3 = 91` の two-channel sample について、
     `twoTail 91 ≤ (rad 91)^1`
     を直接読む example を追加した。
   - さらに、その target-rad budget を
     `tailBound_of_targetRadTail_transport`
     で `TailBound 1 91 1 91` へ流す example に更新した。
3. 結論:
   - `ABC038` 接続は、
     `channelCount -> rad c -> rad(u*v) -> TailBound`
     という二段 transport として見えるようになった。
   - これにより、generic transport route と divisibility route に加えて、
     transport 前の自然な中間 landing point として
     `rad c` budget を theorem 名で固定できた。
4. 検証:
   - `cd lean/dk_math && ./lean-build.sh DkMath.ABC.ABC038Bridge`
   - `cd lean/dk_math && ./lean-build.sh DkMath.ABC.ABC038BridgeExamples`
   - build では既存 `ABC021.lean` と
     `ZsigmondyCyclotomicResearch.lean` の `sorry` 警告が replay されたが、
     今回更新したファイル自体は成功した。
5. 失敗事例:
   - なし。今回は theorem 追加後の build でそのまま通った。
6. 次の課題:
   - `rad c` budget が quality sample の自然入力としてどこまで使えるかを洗う。
   - 特に `u + v = c` の nontrivial triple で、
     `rad c ≤ rad(u*v)` をどう supply するか、
     あるいは `rad c` 側 budget のまま質的不等式へ入る route がないかを比較検討する。

### 日時: 2026/04/19 00:46 JST (`rad(abc)` analytic bridge への直結 route の追加)

1. 目的:
   - `review-019.md` の示唆に従い、`rad c` budget から
     `rad(u*v)` transport を経ずに、
     既存の `rad(a*b*c)` analytic bridge へ直接入る最小 route を追加する。
2. 実施:
   - `DkMath/ABC/ABC038Bridge.lean` に次を追加した。
     - `radAbcBound_of_pi_targetRadTail`
     - `quality_le_of_pi_targetRadTail_of_radAbc`
     - `quality_le_of_not_bad_with_targetRadTail_on_radAbc`
   - `radAbcBound_of_pi_targetRadTail` では
     - `piSqRad c ≤ rad(a*b)^δ`
     - `twoTail c ≤ (rad c)^γ`
     - `a*b*c ≠ 0`
     から
     `c ≤ rad(a*b*c)^(1 + δ + γ)`
     を導く中間補題を実装した。
   - `quality_le_of_pi_targetRadTail_of_radAbc` では、
     上の `rad(abc)` growth bound と
     `δ + γ ≤ ε` を合成して
     `quality_le_of_sqprod_pow_bound_analytic_axiom_to_lemma`
     へ渡す route を追加した。
   - `quality_le_of_not_bad_with_targetRadTail_on_radAbc` では、
     `piSqRad_le_of_not_bad` を使って `¬Bad` 版 wrapper に薄く包み直した。
3. 結論:
   - `ABC038` 接続には、
     `channelCount -> rad c -> rad(u*v) -> TailBound`
     という transport route だけでなく、
     `channelCount -> rad c -> rad(a*b*c) -> quality`
     という analytic 直結 route も theorem 名で現れた。
   - これにより、review-019 が求めていた
     「`rad c` budget のまま quality 側へどこまで入れるか」
     に対する最小の実装回答が入った。
4. 検証:
   - `cd lean/dk_math && ./lean-build.sh DkMath.ABC.ABC038Bridge`
   - `cd lean/dk_math && ./lean-build.sh DkMath.ABC.ABC038BridgeExamples`
   - build では既存 `ABC021.lean` と
     `ZsigmondyCyclotomicResearch.lean` の `sorry` 警告が replay されたが、
     今回更新したファイル自体は成功した。
5. 失敗事例:
   - `radAbcBound_of_pi_targetRadTail` 初版では
     `c = piSqRad * rad * twoTail` の項の並び替えと
     `hπ` の `rad(a*b*c)` への持ち上げが不足し、型が噛まなかった。
   - ここは
     - `hdec` を `calc` で並び替える
     - `hπ_abc : piSqRad c ≤ rad(a*b*c)^δ`
     を先に作る
     形へ分解して解消した。
   - 同 theorem 初版では `a*b*c ≠ 0` を暗に使っていたため、
     仮定として明示し、quality wrapper 側で
     `rad(a*b*c) > 1` から供給する形に整理した。
   - `quality_le_of_sqprod_pow_bound_analytic_axiom_to_lemma` 呼び出しでは、
     `hπ` の形が `rad(a*b)^δ` ではなく
     `(rad a * rad b)^δ` を要求していたため、
     `rad_mul_coprime' hcop` で整形した。
6. 次の課題:
   - 新しい `rad(abc)` 直結 route の concrete sample を追加する。
   - その上で、`ABC038` 本体の convenience theorem 群のうち、
     どこをこの route で置き換えるのが最も薄いかを見極める。

## 2026/04/19 03:57 JST

1. 実施内容:
   - `DkMath/ABC/ABC038BridgeExamples.lean` に
     `rad(abc)` analytic route の concrete sample を追加した。
   - file local に
     `set_option linter.style.nativeDecide false`
     を置き、`piSqRad_7_eq_one : ABC.piSqRad 7 = 1`
     を `native_decide` で固定した。
   - `targetRadTailBound_7` を追加し、
     `primitiveWitnessFamilyPack_14_7_1`
     から `twoTail 7 ≤ (rad 7)^1` を theorem 名で再利用できるようにした。
   - その上で
     `quality_le_of_pi_targetRadTail_of_radAbc`
     を使い、
     `ABC.quality (ABC.Triple.mk 6 1 7 ...) ≤ 2`
     という concrete quality sample を追加した。
2. 補足:
   - quality sample では
     `piSqRad 7 ≤ rad(6*1)^0`,
     `twoTail 7 ≤ rad 7`,
     `1 < rad(6*1*7)`
     を個別に与えて、
     新しい `rad(abc)` 直結 route が実例で閉じることを確認した。
3. 検証:
   - `cd lean/dk_math && ./lean-build.sh DkMath.ABC.ABC038BridgeExamples`
   - build は成功した。
   - 既存 `ABC021.lean` と
     `ZsigmondyCyclotomicResearch.lean`
     の `sorry` 警告のみ replay された。
4. 失敗事例:
   - sample 初版では
     `quality_le_of_pi_targetRadTail_of_radAbc`
     の結論が `≤ 1 + 1` で返り、
     目標 `≤ 2` と definitional に一致しなかった。
   - これは一度 `hq` に受けて `norm_num at hq` で右辺を正規化する形にして解消した。
5. 次の課題:
   - `rad(abc)` 直結 route を
     `ABC038` 本体の convenience theorem 群へどう差し込むかを具体化する。
   - 特に、既存 wrapper のうち
     `rad(a*b)` transport を省ける箇所を洗い出す。

## 2026/04/19 04:58 JST

1. 実施内容:
   - `DkMath/ABC/ABC016.lean` に一般補題
     `piSqRad_eq_one_of_squarefree`
     を追加した。
   - 証明は
     `sqTail_eq_one_of_squarefree`
     と
     `sqTail_eq_piSqRad_mul_twoTail`
     を組み合わせ、
     `piSqRad n ∣ 1`
     から `Nat.eq_one_of_dvd_one` で落とす形にした。
   - `DkMath/ABC/ABC038BridgeExamples.lean` では
     file-local の `native_decide` 設定と
     `piSqRad_7_eq_one`
     を削除し、
     `ABC.piSqRad_eq_one_of_squarefree`
     を直接使う形へ置き換えた。
2. 意味:
   - `review-021` が指摘していた
     「sample 層の closed computation は許容できるが、
     reusable な部品なら構造的証明へ寄せたい」
     という論点に対して、
     `piSqRad 7 = 1`
     を sample 専用計算ではなく
     squarefree 一般補題の special case として読めるようにした。
   - これで `rad(abc)` concrete sample は、
     sample file 内の `native_decide` に依存しなくなった。
3. 検証:
   - `cd lean/dk_math && ./lean-build.sh DkMath.ABC.ABC016`
   - `cd lean/dk_math && ./lean-build.sh DkMath.ABC.ABC038BridgeExamples`
   - いずれも build 成功。
   - `ABC038BridgeExamples` build では
     既存 `ABC021.lean` と
     `ZsigmondyCyclotomicResearch.lean`
     の `sorry` 警告のみ replay された。
4. 失敗事例:
   - 最初に `ABC016` と `ABC038BridgeExamples` を並列 build したところ、
     古い `lake build` プロセスが残って待ち状態になった。
   - これは旧 build を kill して、
     `ABC038BridgeExamples` を直列で再実行することで解消した。
5. 次の課題:
   - `ABC038` 本体の convenience theorem 群に対して、
     `rad(abc)` 直結 route を使う wrapper をどこへ差し込むか具体化する。
   - 特に、
     `quality_le_of_not_bad_with_tail`
     系の入口で `rad(a*b)` transport を省ける最小定理を見つける。
