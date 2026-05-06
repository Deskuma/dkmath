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
