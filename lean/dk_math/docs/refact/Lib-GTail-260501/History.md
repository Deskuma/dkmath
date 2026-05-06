# History

cid: 69f480dc-fd84-83e8-8f69-053e9d23fbb5

- 時刻の打刻は `date` コマンドを使用して時間(時分秒)まで正確に行うこと。
- 新規履歴は **ファイル末尾** に追加すること。

## History Log

Archive

過去ログは、以下にアーカイブしてあります。

- [000](History-000.md)

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

### 日時: 2026/05/01 20:34 JST (GTail 純代数コアの Lib 切り出し)

1. 目的:
   - `DkMath.CosmicFormula.GTail` に同居していた純代数 GTail コアを `DkMath.Lib.Cosmic.GTail` に切り出し、`ABC.PadicValNat` 依存を持たない基礎層として単体ビルド可能にする。
2. 実施:
   - 新規 `DkMath/Lib/Cosmic/GTail.lean` を作成し、`GTail`、分解定理、再帰定理、`r = 1` alias、zero-eval 系を移動した。
   - namespace は downstream 互換を優先して `DkMath.CosmicFormula` のまま維持した。
   - 旧 `DkMath/CosmicFormula/GTail.lean` は `DkMath.Lib.Cosmic.GTail` を import し、Nat / p-adic / congruence 系の上位定理だけを保持する形へ整理した。
3. 結論:
   - 計画書の序盤方針どおり、純代数コアと Nat/p-adic 層の分離が完了した。
   - `Lib.Basic` への import 追加は、軽量入口の性格判断が未確定のため今回は保留した。
4. 検証:
   - `./lean-build.sh DkMath.Lib.Cosmic.GTail` 成功。
   - `./lean-build.sh DkMath.CosmicFormula.GTail` 成功。
   - `./lean-build.sh DkMath.CosmicFormula.Defs` 成功。
   - `./lean-build.sh DkMath.CosmicFormula.CosmicFormulaBinom` 成功。
   - `./lean-build.sh DkMath.FLT.Core` 成功。
5. 失敗事例:
   - sandbox の `bwrap: loopback: Failed RTM_NEWADDR: Operation not permitted` により一部コマンドが失敗したため、必要な検索・ビルドは承認済み escalation で再実行した。
6. 次の課題:
   - 必要なら `DkMath.Lib.Basic` あるいは専用入口ファイルへの import 導線を追加する。
   - 次段階で Nat / congruence / p-adic 系を `GTailNat`、`GTailCongruence`、`GTailPadic` へ分けるか判断する。

### 日時: 2026/05/06 17:59 JST (Lib / DkMathlib 入口導線の追加)

1. 目的:
   - `import DkMath.Lib` で再利用可能な Lib 層を使えるようにする。
   - `import DkMath` からも Lib 層がプロジェクト全体入口として到達可能であることを保証する。
   - 将来の公式公開入口 `import DkMathlib` を `DkMath` とは切り離したルート入口として用意する。
2. 実施:
   - 新規 `DkMath/Lib.lean` を作成し、`DkMath.Lib.Basic` と `DkMath.Lib.Cosmic.GTail` を import する導線入口にした。
   - `DkMath.lean` に `import DkMath.Lib` を追加した。
   - 新規 `DkMathlib.lean` を作成し、`DkMathlib.Basic` のみを import する独立入口にした。
3. 結論:
   - 開発側入口は `import DkMath.Lib` および `import DkMath` で成立する。
   - 公開側入口は `import DkMathlib` で成立し、現時点では `DkMath` へ依存しない。
4. 検証:
   - `lake build DkMath.Lib` 成功。
   - `lake build DkMathlib` 成功。
   - `lake build DkMath` 成功。
5. 失敗事例:
   - ファイル構成確認時に sandbox の `bwrap: loopback: Failed RTM_NEWADDR: Operation not permitted` が出たため、必要な検索は承認済み escalation で再実行した。
6. 次の課題:
   - `DkMathlib` 側へ公開対象を移す段階で、`DkMathlib.Basic` 以下にどの Lib 成果を再配置または再 export するかを決める。

### 日時: 2026/05/06 18:10 JST (GTail 分割後構造設計書の追加)

1. 目的:
   - Nat / congruence / p-adic 系の分割対象が多いため、実装前に混線しない構造設計を固定する。
2. 実施:
   - 新規 `post-refactor-structure-DkMath_Lib_Cosmic_GTail.md` を作成した。
   - `GTail`、`GTailNat`、`GTailCongruence`、`GTailPadic` の役割、依存グラフ、配置対象 theorem、旧 `DkMath.CosmicFormula.GTail` の compatibility shell 方針を整理した。
   - `GTailPadic` は `GTailCongruence` に依存させず、`GTailNat` から兄弟層として分ける設計を採用した。
3. 結論:
   - 次の実装順は `GTailNat`、`GTailCongruence`、`GTailPadic`、入口更新の順とする。
4. 検証:
   - Markdown 設計書の追加のみで Lean コード変更はないため、ビルドは未実施。
5. 失敗事例:
   - 定理一覧検索時に sandbox の `bwrap: loopback: Failed RTM_NEWADDR: Operation not permitted` が出たため、既に読めたファイル内容から配置対象を確認した。
6. 次の課題:
   - 設計書に従って `DkMath.Lib.Cosmic.GTailNat` から実装分割を開始する。

### 日時: 2026/05/06 20:11 JST (Step 1: GTailNat の分離)

1. 目的:
   - `DkMath.CosmicFormula.GTail` から `ℕ` 上の可除性・head-unit 非可除性 API を `DkMath.Lib.Cosmic.GTailNat` へ分離する。
2. 実施:
   - 新規 `DkMath/Lib/Cosmic/GTailNat.lean` を作成した。
   - `pow_dvd_higher_tail`、`GTail_not_dvd_of_head_unit_of_prime_dvd_x`、`GN_not_dvd_of_head_unit_of_prime_dvd_x` を移動した。
   - 旧 `DkMath/CosmicFormula/GTail.lean` は `DkMath.Lib.Cosmic.GTailNat` を import し、該当ブロックを削除した。
3. 結論:
   - 設計書 Step 1 の GTailNat 分離が完了した。
   - p-adic 層はまだ旧 `DkMath.CosmicFormula.GTail` に残し、次段階で `GTailPadic` へ移す。
4. 検証:
   - `lake build DkMath.Lib.Cosmic.GTailNat` 成功。
   - `lake build DkMath.CosmicFormula.GTail` 成功。
   - `lake build DkMath.Lib.Cosmic.GTail` 成功。
5. 失敗事例:
   - なし。
6. 次の課題:
   - Step 2 として `DkMath.Lib.Cosmic.GTailCongruence` を作り、`Nat.ModEq` と mod `p^2` / mod `p^3` 系を移動する。

### 日時: 2026/05/07 00:15 JST (Step 2: GTailCongruence の分離)

1. 目的:
   - `DkMath.CosmicFormula.GTail` から `Nat.ModEq` と mod `p^2` / mod `p^3` 系の合同 API を `DkMath.Lib.Cosmic.GTailCongruence` へ分離する。
2. 実施:
   - 新規 `DkMath/Lib/Cosmic/GTailCongruence.lean` を作成した。
   - `sum_range_modEq`、`GTail_congr_of_modEq`、`GTail_modEq_eval_zero_of_dvd_x`、`GN_modEq_*`、`GN_mod_p2_head`、`GN_mod_p3_head`、具体等式化補題を移動した。
   - 旧 `DkMath/CosmicFormula/GTail.lean` は `DkMath.Lib.Cosmic.GTailCongruence` を import し、合同ブロックを削除した。
3. 結論:
   - 設計書 Step 2 の GTailCongruence 分離が完了した。
   - `GTailPadic` はまだ旧 `DkMath.CosmicFormula.GTail` に残っている。
4. 検証:
   - `lake build DkMath.Lib.Cosmic.GTailCongruence` 成功。
   - `lake build DkMath.CosmicFormula.GTail` 成功。
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicBranchA` 成功。
     - 既存 warning: `declaration uses sorry` は残存するが、今回の分割による失敗ではない。
5. 失敗事例:
   - 合同ブロック削除時に sandbox の `bwrap: loopback: Failed RTM_NEWADDR: Operation not permitted` が出たため、承認済み escalation で機械的削除を再実行した。
6. 次の課題:
   - Step 3 として `DkMath.Lib.Cosmic.GTailPadic` を作り、`padicValNat_*` 系を移動する。

### 日時: 2026/05/07 01:10 JST (Step 3: GTailPadic の分離)

1. 目的:
   - `DkMath.CosmicFormula.GTail` から `padicValNat_*` 系の p-adic 付値 API を `DkMath.Lib.Cosmic.GTailPadic` へ分離する。
2. 実施:
   - 新規 `DkMath/Lib/Cosmic/GTailPadic.lean` を作成した。
   - `padicValNat_GTail_eq_zero_of_head_unit_of_prime_dvd_x`、`padicValNat_GN_eq_zero_of_head_unit_of_prime_dvd_x`、`padicValNat_higher_tail_lower_bound`、`padicValNat_tail_exact_of_head_unit`、`padicValNat_GN_exact_of_head_unit` を移動した。
   - `GTailPadic` は設計書どおり `DkMath.Lib.Cosmic.GTailNat` と `DkMath.ABC.PadicValNat` だけに依存させ、`GTailCongruence` とは独立にした。
   - 旧 `DkMath/CosmicFormula/GTail.lean` は `DkMath.Lib.Cosmic.GTailCongruence` と `DkMath.Lib.Cosmic.GTailPadic` を import する compatibility shell にした。
3. 結論:
   - 設計書 Step 3 の GTailPadic 分離が完了した。
   - 旧 `DkMath.CosmicFormula.GTail` は theorem 本体を持たない互換入口になった。
4. 検証:
   - `lake build DkMath.Lib.Cosmic.GTailPadic` 成功。
   - `lake build DkMath.CosmicFormula.GTail` 成功。
   - `lake build DkMath.FLT.Core` 成功。
5. 失敗事例:
   - 旧ファイルの delete patch は失敗したため、import 差し替えと theorem ブロック削除で compatibility shell に更新した。
   - shell 更新時に sandbox の `bwrap: loopback: Failed RTM_NEWADDR: Operation not permitted` が出たため、承認済み escalation で機械的置換を再実行した。
6. 次の課題:
   - Step 4 として `DkMath/Lib.lean` の import 導線を更新する。

### 日時: 2026/05/07 05:02 JST (Step 4: DkMath.Lib 入口導線の更新)

1. 目的:
   - `import DkMath.Lib` で GTail 周辺の分割済み Lib 層を一括利用できるようにする。
2. 実施:
   - `DkMath/Lib.lean` に `DkMath.Lib.Cosmic.GTailNat`、`DkMath.Lib.Cosmic.GTailCongruence`、`DkMath.Lib.Cosmic.GTailPadic` の import を追加した。
   - 設計書では `GTailPadic` の入口投入は判断事項だったが、GTail 周辺 API を `DkMath.Lib` から一括利用する導線を優先して含めた。
3. 結論:
   - `import DkMath.Lib` で `GTail`、Nat 可除性、合同、p-adic 付値の各層へ到達できる。
4. 検証:
   - `lake build DkMath.Lib` 成功。
   - `lake build DkMath` 成功。
5. 失敗事例:
   - なし。
6. 次の課題:
   - 必要なら downstream の新規コードから `DkMath.CosmicFormula.GTail` ではなく `DkMath.Lib.Cosmic.*` または `DkMath.Lib` を import するように置き換えていく。
