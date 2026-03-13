# RH Implements History

## History Archive for RH Implementation

[RH_Implements_History-01.md](RH_Implements_History-01.md) から続く RH 実装の記録アーカイブ

## RH 実装の記録

RH: Riemann Hypothesis を説明するための補題群の実装に関する記録

## 記録内容テンプレート（例）

### 日時: 2026/03/12 21:49: 概要見出し

1. 目的: RH の実装履歴の記録と要約
2. 内容:
   - RH の実装の概要と目的
   - 主要なファイル構成とその役割
   - 実装の目的と今後の展開
3. 結論: RH の実装は数式の構造解析と数値実験の基盤を提供するものであり、今後の展開が期待される。
4. 失敗事例: 特に大きな失敗はないが、数値実験の精度向上や複雑な性質の証明にはさらなる工夫が必要である。
5. 備考: 追加の詳細や数値実験の結果は、関連するドキュメントやノートブックに記録されている。
6. 次の課題: より高度な性質の証明や数値実験の拡充を行うこと。

---

## 実装履歴

※ここに上記テンプレートに沿った実装履歴を記録していく。

### 日時: 2026/03/14 00:35 JST: OP-004 文書整理（README 一本化）

1. 目的:
   `docs/README.md` を廃止し、`DkMath/RH/README.md` を単一の表紙ドキュメントとして統合する。
2. 内容:
   - 変更ファイル:
     - `DkMath/RH/README.md`
     - `DkMath/RH/docs/HOPC-RH-OpenProblems.md`
     - `DkMath/RH/docs/HOPC-RH-Roadmap.md`
     - `DkMath/RH/docs/RH_Implements_History-02.md`
   - 実施内容:
     - `docs/README.md` の内容を `RH/README.md` に統合（ファイル移動）
     - 統合後 README の相対リンクを root 基準へ補正
       - `./docs/EulerZetaFunction-v0-1.pdf`
       - `./docs/DkMath_RH.md`
       - `docs/HOPC-RH-Roadmap.md` / `docs/HOPC-RH-Glossary.md` / `docs/HOPC-RH-OpenProblems.md`
       - `docs/RH-CFBRC-Discussion.md`
     - `HOPC-RH-OpenProblems.md` の運用チェックリストから
       `docs/README.md` 参照を削除し、履歴記録先を `History-02` へ更新
     - `HOPC-RH-Roadmap.md` の主ファイル一覧から `docs/README.md` を削除
3. 結論:
   - RH README は `DkMath/RH/README.md` の 1 本に統一された。
   - `docs/README.md` への依存は、現行運用文書では解消された。
4. 失敗事例:
   - なし。
5. 検証:
   - `rg -n "DkMath/RH/docs/README\\.md|docs/README\\.md" lean/dk_math/DkMath/RH --glob "*.md"`
     を実行し、残存が `RH_Implements_History-01.md`（旧履歴アーカイブ）内のみであることを確認。
6. 次の課題:
   - OP-004 の残作業（曲率条件運用の供給規約・命名規約整理）へ進む。

### 日時: 2026/03/14 01:08 JST: OP-004 RH-P1（phaseCurv provider 層の導入）

1. 目的:
   OP-004 の着手として、`phaseCurv ≠ 0` 供給を provider として切り出し、
   `stationaryAt` bridge から `nondegenerateStationaryAt` bridge へ接続する。
2. 内容:
   - 変更ファイル:
     - `DkMath/RH/CFBRCBridge.lean`
     - `DkMath/RH/README.md`
     - `DkMath/RH/docs/HOPC-RH-OpenProblems.md`
     - `DkMath/RH/docs/HOPC-RH-Roadmap.md`
     - `DkMath/RH/docs/RH_Implements_History-02.md`
   - 追加実装（`CFBRCBridge.lean`）:
     - `nondegenerateStationaryAt_insert_of_hopcPrimeContributionSum_eq_zero_and_phaseCurv_ne_zero`
     - `exists_nondegenerateStationaryAt_insert_of_cfbRc_primitive_prime_bridge_of_local_split_and_phaseCurv`
     - `exists_nondegenerateStationaryAt_insert_of_cfbRc_primitive_prime_boundary_bridge_of_local_split_and_phaseCurv`
     - `BoundaryInsertPhaseCurvProvider`
     - `boundaryInsertPhaseCurvProvider_of_split`
     - `exists_nondegenerateStationaryAt_insert_of_cfbRc_primitive_prime_boundary_bridge_of_provider_and_phaseCurvProvider`
   - 文書同期:
     - `README.md` の CFBRC bridge API 一覧へ OP-004 API を追記
     - `HOPC-RH-OpenProblems.md` の OP-004 に状態・到達済み・命名規約を追記
     - `HOPC-RH-Roadmap.md` の Next Sprint に RH-P1 到達済みを追記
3. 結論:
   - 曲率前提を `BoundaryInsertPhaseCurvProvider` として分離でき、
     停留供給 (`BoundaryInsertLocalLiftProvider`) と独立に合成可能になった。
   - OP-004 の命名規約を
     `..._of_local_split_and_phaseCurv` / `..._of_provider_and_phaseCurvProvider`
     として暫定確定した。
4. 失敗事例:
   - `side` 依存型（`match side with ...`）の不一致で初回 build が失敗。
   - `cases side` による分岐で型を正規化して解消。
5. 検証:
   - `lake build DkMath.RH.CFBRCBridge` 成功。
6. 次の課題:
   - `phaseCurv ≠ 0` の供給パターンを
     解析仮定版 / 計算補題版 / provider 版で文書化する。

### 日時: 2026/03/14 01:24 JST: OP-004 RH-P2（singleton nondegenerate と規約追補）

1. 目的:
   OP-004 の次段として、singleton でも非退化停留を直接返せる高位 wrapper を追加し、
   曲率供給規約の文書化を進める。
2. 内容:
   - 変更ファイル:
     - `DkMath/RH/CFBRCBridge.lean`
     - `DkMath/RH/README.md`
     - `DkMath/RH/docs/HOPC-RH-OpenProblems.md`
     - `DkMath/RH/docs/HOPC-RH-Roadmap.md`
     - `DkMath/RH/docs/HOPC-RH-Glossary.md`
     - `DkMath/RH/docs/RH_Implements_History-02.md`
   - 追加実装（`CFBRCBridge.lean`）:
     - `exists_nondegenerateStationaryAt_singleton_of_cfbRc_primitive_prime_boundary_bridge_of_local_and_phaseCurv`
       (`S := ∅` 還元で既存 insert nondegenerate bridge を再利用)
   - 文書更新:
     - README の主要 API に singleton nondegenerate wrapper を追加
     - OpenProblems OP-004 に供給パターン v1（解析仮定/計算補題/provider）を明記
     - Roadmap の OP-004 到達済みを RH-P1/P2 へ更新
     - Glossary に `BoundaryInsertPhaseCurvProvider` と nondegenerate bridge 群を追加
3. 結論:
   - OP-004 の高位 API は singleton / insert の両経路で
     `nondegenerateStationaryAt` へ接続できる状態になった。
   - 曲率供給運用の命名規約と層分け（v1）が文書で追跡可能になった。
4. 失敗事例:
   - 初回実装で `match side` 由来の依存型不一致と前方参照問題が発生。
   - `cases side` で左右分岐し、right 版 bridge へ還元して解消。
5. 検証:
   - `lake build DkMath.RH.CFBRCBridge` 成功。
   - `lake build DkMath.RH` 成功。
6. 次の課題:
   - `phaseCurv ≠ 0` の計算補題版（`boundaryCore` / `boundaryDiffPow` 直結）を
     高位 wrapper として追加する。

### 日時: 2026/03/14 01:45 JST: OP-004 RH-P3（計算補題直結 nondegenerate wrapper）

1. 目的:
   OP-004 の残タスクとして、
   `boundaryCore` / `boundaryDiffPow` 直結の計算補題入口から
   `nondegenerateStationaryAt` へ接続する高位 wrapper 群を追加する。
2. 内容:
   - 変更ファイル:
     - `DkMath/RH/CFBRCBridge.lean`
     - `DkMath/RH/README.md`
     - `DkMath/RH/docs/HOPC-RH-OpenProblems.md`
     - `DkMath/RH/docs/HOPC-RH-Roadmap.md`
     - `DkMath/RH/docs/HOPC-RH-Glossary.md`
     - `DkMath/RH/docs/RH_Implements_History-02.md`
   - 追加実装（`CFBRCBridge.lean`）:
     - `exists_nondegenerateStationaryAt_insert_of_cfbRc_primitive_prime_boundary_bridge_of_boundaryCore_factor0_and_phaseCurv`
     - `exists_nondegenerateStationaryAt_singleton_of_cfbRc_primitive_prime_boundary_bridge_of_boundaryCore_factor0_and_phaseCurv`
     - `exists_nondegenerateStationaryAt_insert_of_cfbRc_primitive_prime_boundary_bridge_of_boundaryCore_local0_and_phaseCurv`
     - `exists_nondegenerateStationaryAt_singleton_of_cfbRc_primitive_prime_boundary_bridge_of_boundaryCore_local0_and_phaseCurv`
     - `exists_nondegenerateStationaryAt_insert_of_cfbRc_primitive_prime_boundary_bridge_of_boundaryDiffPow_local0_and_phaseCurv`
     - `exists_nondegenerateStationaryAt_singleton_of_cfbRc_primitive_prime_boundary_bridge_of_boundaryDiffPow_local0_and_phaseCurv`
     - `exists_nondegenerateStationaryAt_insert_of_cfbRc_primitive_prime_boundary_bridge_of_boundaryDiffPow_factor0_and_phaseCurv`
     - `exists_nondegenerateStationaryAt_singleton_of_cfbRc_primitive_prime_boundary_bridge_of_boundaryDiffPow_factor0_and_phaseCurv`
   - 設計メモ:
     - `stationary` 側既存 wrapper の層（factor0 → local0 → provider）を再利用し、
       `phaseCurv ≠ 0` 供給のみを追加入力として合成。
     - 依存型の不一致回避のため、各 wrapper 証明は `cases side` で
       `.right/.left` に正規化した。
   - 文書更新:
     - README API 一覧に OP-004 RH-P3 の非退化 wrapper 群を追加
     - OpenProblems / Roadmap を RH-P3 到達済みへ更新
     - Glossary の OP-004 語彙に計算補題直結 wrapper 群を追記
3. 結論:
   - OP-004 の計算補題版（`boundaryCore` / `boundaryDiffPow` 直結）で、
     `stationaryAt` だけでなく `nondegenerateStationaryAt` まで
     高位 API で到達できる形が揃った。
   - 曲率供給運用は
     解析仮定 / 計算補題 / provider の 3 層で統一された。
4. 失敗事例:
   - 初回実装で `match side` 依存型の不一致が連鎖的に発生。
   - すべての高位 wrapper を左右分岐 (`cases side`) へ落として解消。
5. 検証:
   - `lake build DkMath.RH.CFBRCBridge` 成功。
   - `lake build DkMath.RH` 成功。
6. 次の課題:
   - OP-004 の次段として、`normalized` / `with_offdvd` 経路に
     nondegenerate 版（`..._and_phaseCurv`）を追加するかを評価する。

### 日時: 2026/03/14 02:10 JST: OP-004 RH-P4（normalized / with_offdvd 非退化拡張）

1. 目的:
   OP-004 の残件として、
   `boundaryDiffPow` の `of_dvd` / `normalized` / `with_offdvd` 経路でも
   `nondegenerateStationaryAt` へ直接接続できる wrapper を追加する。
2. 内容:
   - 変更ファイル:
     - `DkMath/RH/CFBRCBridge.lean`
     - `DkMath/RH/README.md`
     - `DkMath/RH/docs/HOPC-RH-Glossary.md`
     - `DkMath/RH/docs/HOPC-RH-OpenProblems.md`
     - `DkMath/RH/docs/HOPC-RH-Roadmap.md`
     - `DkMath/RH/docs/RH_Implements_History-02.md`
   - 追加実装（`CFBRCBridge.lean`）:
     - `exists_nondegenerateStationaryAt_insert_of_cfbRc_primitive_prime_boundary_bridge_of_boundaryDiffPow_factor0_of_dvd_and_phaseCurv`
     - `exists_nondegenerateStationaryAt_insert_of_cfbRc_primitive_prime_boundary_bridge_of_boundaryDiffPow_factor0_normalized_and_phaseCurv`
     - `exists_nondegenerateStationaryAt_insert_of_cfbRc_primitive_prime_boundary_bridge_of_boundaryDiffPow_factor0_with_offdvd_and_phaseCurv`
   - 実装方針:
     - 停留供給は既存 `BoundaryInsertLocalLiftProvider` 構成器（`of_dvd`/`with_offdvd`）を再利用
     - 曲率供給は `BoundaryInsertPhaseCurvProvider` へ分離して合成
     - `normalized` 版は `boundaryDiffPowDvdSet` を使い `of_dvd` 版へ委譲
3. 結論:
   - OP-004 で意図していた計算補題版 nondegenerate 経路が、
     `factor0` 系の主要導線（通常 / `of_dvd` / `normalized` / `with_offdvd`）で揃った。
   - 曲率供給規約は provider 合成で一貫運用できる形になった。
4. 失敗事例:
   - `normalized` 非退化 wrapper で `match side` 依存型不一致が発生。
   - `cases side` で左右を固定して型正規化し解消。
5. 検証:
   - `lake build DkMath.RH.CFBRCBridge` 成功。
   - `lake build DkMath.RH` 成功。
6. 次の課題:
   - OP-004 は完了扱いとし、以後は OP-001 系（witness / provider 分離）の研究タスクを継続する。

### 日時: 2026/03/14 03:00 JST: RH-CFBRC-HOPC 研究草稿（prime-local 形成機構）の新設

1. 目的:
   実装で明確化された
   「prime-local contribution が停留/非退化停留形成に与える構造寄与」を
   研究論文草稿（GitHub Markdown）として独立文書化する。
2. 内容:
   - 変更ファイル:
     - `DkMath/RH/docs/HOPC-RH-PrimeLocal-Formation.md`（新規）
     - `DkMath/RH/README.md`
     - `DkMath/RH/docs/RH_Implements_History-02.md`
   - 新規草稿の要点:
     - `hopcPrimeContributionSum = 0` と停留条件の同値を中心命題として整理
     - CFBRC primitive-prime witness から RH 観測器への bridge を数理的に説明
     - `stationary` / `nondegenerate` / provider / normalized 経路を層構造で整理
     - 「RH の最終証明は主張しない」立場を明記
   - README 同期:
     - 冒頭の参照導線に
       `docs/HOPC-RH-PrimeLocal-Formation.md` を追加
3. 結論:
   - 実装知見を「補題の列」から「研究主張の形」へ再構成する文書基盤を用意できた。
   - 今後の OP-001 系研究を、形成原理の明文化を保ったまま進められる。
4. 失敗事例:
   - なし。
5. 検証:
   - ドキュメント追加のみ（Lean build 影響なし）。
6. 次の課題:
   - 草稿に実装 API の具体名（代表補題）を段階的に追加し、
     将来的な preprint 形式へ拡張する。

### 日時: 2026/03/14 03:21 JST: RH-PF1（prime-local 形成条件の直接抽出補題）

1. 目的:
   論文草稿の説明構造に対応して、
   `stationaryAt`/`nondegenerate` へ落とす前段の形成条件
   `hopcPrimeContributionSum = 0 ∧ phaseCurv ≠ 0`
   を Lean 補題として直接抽出する。
2. 内容:
   - 変更ファイル:
     - `DkMath/RH/CFBRCBridge.lean`
     - `DkMath/RH/docs/HOPC-RH-PrimeLocal-Formation.md`
     - `DkMath/RH/docs/RH-CFBRC-HOPC.md`
     - `DkMath/RH/docs/RH_Implements_History-02.md`
   - 追加実装:
     - `exists_primeLocalFormation_insert_of_cfbRc_primitive_prime_boundary_bridge_of_local_split_and_phaseCurv`
   - 文書同期:
     - 草稿に RH-PF1 補題名と数理的意味（形成条件の直接返却）を追記
     - RH-CFBRC-HOPC 実装層説明に RH-PF1 の位置づけを追加
3. 結論:
   - 「prime-local 形成機構」を、存在定理の帰結ではなく
     独立した中間命題として参照できるようになった。
   - 論文本文と Lean 補題の対応関係が 1 段明確化された。
4. 失敗事例:
   - 初回証明で `match side` 依存型不一致が発生。
   - `cases side` で左右分岐して解消。
5. 検証:
   - `lake build DkMath.RH.CFBRCBridge` 成功。
   - `lake build DkMath.RH` 成功。
6. 次の課題:
   - RH-PF1 を起点に、有限形成条件から atTop 側へ持ち上げる
     intermediate theorem（eventually 版）を設計する。

### 日時: 2026/03/14 03:27 JST: RH-PF2（finite 形成条件の eventually 持ち上げ）

1. 目的:
   RH-PF1（`insert p S` での形成条件直接抽出）を
   `Filter.atTop` 上の eventually 形式へ持ち上げる中間補題を追加する。
2. 内容:
   - 変更ファイル:
     - `DkMath/RH/CFBRCBridge.lean`
     - `DkMath/RH/docs/HOPC-RH-PrimeLocal-Formation.md`
     - `DkMath/RH/docs/RH-CFBRC-HOPC.md`
     - `DkMath/RH/docs/RH_Implements_History-02.md`
   - 追加実装:
     - `eventually_exists_primeLocalFormation_insert_of_cfbRc_primitive_prime_boundary_bridge_of_local_split_and_phaseCurv`
   - 補題の意味:
     - `S` 一様の `hsum_lift` / `hcurv_lift` を仮定し、
       `∀ᶠ S in atTop, ∃ p, (hopcPrimeContributionSum = 0 ∧ phaseCurv ≠ 0)`
       を返す。
     - 証明は RH-PF1 を `Eventually.of_forall` で持ち上げる構造。
3. 結論:
   - 論文説明で必要だった
     「finite 形成条件 → eventually 形成条件」
     の接続が Lean 補題として明示化された。
4. 失敗事例:
   - 初回証明で `match side` 依存型不一致が発生。
   - `cases side` 分岐で型を固定して解消。
5. 検証:
   - `lake build DkMath.RH.CFBRCBridge` 成功。
   - `lake build DkMath.RH` 成功。
6. 次の課題:
   - RH-PF2 を入力として、eventually `stationaryAt` / `nondegenerateStationaryAt`
     への高位 bridge を設計する。

### 日時: 2026/03/14 03:49 JST: RH-PF2w / RH-PF3（witness 付き eventually 形成と高位停留 bridge）

1. 目的:
   RH-PF2 の次段として、eventually 形成条件を witness 付きで回収し、
   eventually `stationaryAt` / eventually `nondegenerateStationaryAt` を返す
   高位 bridge を実装する。
2. 内容:
   - 変更ファイル:
     - `DkMath/RH/CFBRCBridge.lean`
     - `DkMath/RH/docs/HOPC-RH-PrimeLocal-Formation.md`
     - `DkMath/RH/docs/RH-CFBRC-HOPC.md`
     - `DkMath/RH/docs/RH_Implements_History-02.md`
   - 追加実装:
     - `exists_primeLocalFormationWitness_insert_of_cfbRc_primitive_prime_boundary_bridge_of_local_split_and_phaseCurv`
     - `eventually_exists_primeLocalFormationWitness_insert_of_cfbRc_primitive_prime_boundary_bridge_of_local_split_and_phaseCurv`
     - `eventually_exists_stationaryAt_insert_of_cfbRc_primitive_prime_boundary_bridge_of_local_split`
     - `eventually_exists_nondegenerateStationaryAt_insert_of_cfbRc_primitive_prime_boundary_bridge_of_local_split_and_phaseCurv`
   - 補題の意味:
     - RH-PF2 の形成条件に `p ∣ boundaryDiffPow` と gap 条件を同梱し、
       witness 付き eventually 形成へ強化。
     - 形成条件を `stationaryAt` / `nondegenerateStationaryAt` 判定補題へ接続し、
       atTop 側の高位存在命題を直接返す API を整備。
3. 結論:
   - RH-PF1 → RH-PF2 → RH-PF2w → RH-PF3 の段階が揃い、
     prime-local 形成機構から高位停留命題への導線が完成した。
4. 失敗事例:
   - RH-PF3 実装時に `match side` 依存型不一致（`hsum_lift` 引数型）が発生。
   - `cases side` で右/左を固定し、呼び出し側の型を正規化して解消。
5. 検証:
   - `lake build DkMath.RH.CFBRCBridge` 成功。
   - `lake build DkMath.RH` 成功。
6. 次の課題:
   - RH-PF3 を呼ぶ既存 wrapper 群の段階移行（旧導線の統合整理）を進める。

### 日時: 2026/03/14 04:19 JST: RH-PF2w への段階移行（provider 高位 wrapper 内部導線の統一）

1. 目的:
   RH-PF 系の導線へ呼び出し側を段階移行するため、
   provider 高位 wrapper が旧 split bridge へ直接依存していた部分を整理する。
2. 内容:
   - 変更ファイル:
     - `DkMath/RH/CFBRCBridge.lean`
     - `DkMath/RH/docs/RH_Implements_History-02.md`
   - 実装変更:
     - `exists_stationaryAt_insert_of_cfbRc_primitive_prime_boundary_bridge_of_provider`
       を、`exists_boundaryPrime_dvd_gap_of_cfbRc_primitive_prime_boundaryDiffPow_of_coprime`
       による witness 抽出 + 判定補題適用の直接構成へ変更。
     - `exists_nondegenerateStationaryAt_insert_of_cfbRc_primitive_prime_boundary_bridge_of_provider_and_phaseCurvProvider`
       を、RH-PF2w
       (`exists_primeLocalFormationWitness_insert_of_cfbRc_primitive_prime_boundary_bridge_of_local_split_and_phaseCurv`)
       経由で構成する形へ変更。
   - 互換性:
     - 公開シグネチャは変更なし（内部証明導線のみ更新）。
3. 結論:
   - provider 入口での内部実装が RH-PF 系と整合し、
     旧 split bridge 直接依存を一段減らせた。
4. 失敗事例:
   - なし（`cases side` で依存型を固定した構成で通過）。
5. 検証:
   - `lake build DkMath.RH.CFBRCBridge` 成功。
   - `lake build DkMath.RH` 成功。
6. 次の課題:
   - 同様の内部移行を `eventually` 系高位 wrapper（導入予定）へ拡張する。

### 日時: 2026/03/14 04:23 JST: RH-PF3 拡張（eventually 側の最小前提化 + provider-family 高位 API）

1. 目的:
   RH-PF3 の eventually 導線を整理し、
   `stationaryAt` 側の前提最小化と provider-family 直接入力 API を整備する。
2. 内容:
   - 変更ファイル:
     - `DkMath/RH/CFBRCBridge.lean`
     - `DkMath/RH/docs/HOPC-RH-PrimeLocal-Formation.md`
     - `DkMath/RH/docs/RH-CFBRC-HOPC.md`
     - `DkMath/RH/docs/RH_Implements_History-02.md`
   - 実装変更:
     - `eventually_exists_stationaryAt_insert_of_cfbRc_primitive_prime_boundary_bridge_of_local_split`
       から不要だった曲率仮定を削除し、
       primitive-prime witness + `hS_lift` + `hsum_lift` だけで構成。
     - 新規追加:
       - `eventually_exists_stationaryAt_insert_of_cfbRc_primitive_prime_boundary_bridge_of_providerFamily`
       - `eventually_exists_nondegenerateStationaryAt_insert_of_cfbRc_primitive_prime_boundary_bridge_of_providerFamily_and_phaseCurvProviderFamily`
3. 結論:
   - eventually 側でも「必要な仮定だけ」で停留存在へ到達できる導線になった。
   - provider 設計（record）を `atTop` へ持ち上げる高位 API が揃った。
4. 失敗事例:
   - provider-family wrapper 実装時に `hp_gap` の依存型不一致（`match side, hpnd`）が発生。
   - `cases side` で左右を固定して解消。
5. 検証:
   - `lake build DkMath.RH.CFBRCBridge` 成功。
   - `lake build DkMath.RH` 成功。
6. 次の課題:
   - `eventually` provider-family wrapper を利用する呼び出し側（tendsto/tsum 接続）を段階移行する。

### 日時: 2026/03/14 05:35 JST: RH-PF3 呼び出し側移行（tendsto/tsum 接続）

1. 目的:
   RH-PF3 の provider-family 系補題を、
   `hopcPrimeContributionTsum` / `tendsto` 接続の呼び出し側で実際に利用する導線へ移行する。
2. 内容:
   - 変更ファイル:
     - `DkMath/RH/CFBRCBridge.lean`
     - `DkMath/RH/docs/HOPC-RH-PrimeLocal-Formation.md`
     - `DkMath/RH/docs/RH-CFBRC-HOPC.md`
     - `DkMath/RH/docs/RH_Implements_History-02.md`
   - 追加実装（中間補題）:
     - `eventually_stationaryAt_of_cfbRc_primitive_prime_boundary_bridge_of_providerFamily`
       - fixed witness `p` を取り、`p ∈ S` eventually により
         `insert p S = S` へ正規化して `eventually stationaryAt(S)` を回収。
   - 追加実装（無限側接続）:
     - `hopcPrimeContributionTsum_eq_zero_of_boundaryDiffPow_factor0_with_offdvd_provider_and_providerFamily_sigma_gt_one`
     - `tendsto_hopcPrimeContributionSum_atTop_of_boundaryDiffPow_factor0_with_offdvd_provider_and_providerFamily_sigma_gt_one`
     - `hopcPrimeContributionTsum_eq_zero_of_boundaryDiffPow_factor0_with_offdvdFactorZeroProvider_and_providerFamily_sigma_gt_one`
     - `tendsto_hopcPrimeContributionSum_atTop_of_boundaryDiffPow_factor0_with_offdvdFactorZeroProvider_and_providerFamily_sigma_gt_one`
3. 結論:
   - PF3 provider-family wrapper 群が、有限側補題で止まらず
     `tsum/tendsto`（無限側）へ直結する呼び出し経路を持った。
4. 失敗事例:
   - なし。
5. 検証:
   - `lake build DkMath.RH.CFBRCBridge` 成功。
   - `lake build DkMath.RH` 成功。
6. 次の課題:
   - 旧 `hEvStationary` 直入力 API と新 provider-family API の公開方針
     （段階的 deprecate するか併存するか）を整理する。
