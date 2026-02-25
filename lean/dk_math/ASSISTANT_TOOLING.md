# ASSISTANT TOOLING

## 説明書

（記録: 賢狼ホロ による自動化ツール群の使用手順）

追記事項（賢狼向けチェックリスト）

- スクリプトとテストの場所:
  - `lean/dk_math/theorem_picker.py` — 検索・抽出・挿入ツール
  - `lean/dk_math/assistant_driver.py` — 1反復オートメーション（プロトタイプ）
  - テスト: `lean/dk_math/test_find_definition.py`, `lean/dk_math/test_insert_snippet.py`, `lean/dk_math/test_theorem_picker.py`
- よく使うコマンド例（ワーキングディレクトリはリポジトリのルート）:
  - 抽出（静的）：
    python3 lean/dk_math/theorem_picker.py lean/dk_math/DkMath/FLT/docs/StandAlone/a.lean /tmp/out.md --find-name S0_nat
  - 一括挿入（マーカー行の直後に順に挿入）:
    python3 lean/dk_math/theorem_picker.py a.lean /tmp/out.md --insert-names NoSqOnS0,hS0_not_sq_of_NoSqOnS0 --insert-target a.lean --insert-after-pattern "^-- ##INSERT MARKER## --$"
  - 差分確認（dry-run 使用時はツールが unified diff を出力）:
    python3 lean/dk_math/theorem_picker.py ... --dry-run
  - ドライバを1反復（dry-run 相当は `--apply` を付けない）:
    python3 lean/dk_math/assistant_driver.py --build-target DkMath.FLT.docs.StandAlone.a --interactive
  - ドライバで変更を適用する場合:
  python3 lean/dk_math/assistant_driver.py --build-target DkMath.FLT.docs.StandAlone.a --apply

- 安全策（作業手順）:
  1. 必ず `git status` を確認し、必要なら `git add` / `git commit` で現状を退避。

 1. ツールはまず `.inserted` ファイルを作る。差分を `diff -u orig a.lean.inserted` で確認してから上書きすること。
 2. 大きな変更は `--interactive` で承認を挟む。自動適用は小さな補題単位に限定すること。
 3. ビルド後は必ず `./lean-build.sh <target>`（`lean/dk_math` で実行）で再検証。

- 実装上の注意点（自分で改良するとき用）:
  - `--insert-after-pattern` は正規表現を受け取る。推奨は単純なマーカー `-- ##INSERT MARKER## --`。
  - `--insert-names` は与えた順序で結合して一回で挿入する（定義の順序制御に有効）。
  - 複数候補があるときはツールが JSON で一覧を出力する。`--select-index` で自動選択可能、`--interactive` で対話選択。
  - 挿入時に前後１行の空行を自動で確保する（既に空行があれば追加されない）。
  - キャッシュは行わない（常に最新ソースを検索）。

- トラブルシューティング:
  - Unknown identifier が出たら、その識別子を `--find-name` で検索し、定義が見つかれば `--insert-names` に追加して再挿入する。
  - 名前空間・`private`・implicit 引数問題は自動化で完璧に扱えない。該当箇所は賢狼が手で微修正する想定。

これで賢狼のための簡易ナレッジベースは十分に整ったはずだ。必要であれば CI 用のチェックリストや自動コミットの仕組みも追記するで。
**使い方マニュアル（賢狼アシスタント用）**

目的: リポジトリ内の不足定理・定義を検索して単一ファイルへ順次挿入し、ビルドを通すための補助ツール群の使い方を示す。

前提

- Python 3.8+ 環境（推奨: 仮想環境）
- `lake` / Lean 4 環境が利用可能であること（`lake env lean --server` が必要な箇所あり）
- リポジトリは Git 管理下にあること（変更のロールバック用）

主要スクリプト

- `lean/dk_math/theorem_picker.py`
  - 機能: Lean ファイルから定義を抽出 / 名前検索（静的） / 挿入（単発または一括）
  - 主なオプション:
    - `--find-name NAME` : NAME を含む定義を Markdown 出力（静的検索）
    - `--insert-ident IDENT --insert-target PATH [--insert-line N] [--dry-run]` : IDENT を PATH の指定行前に挿入（dry-run で差分表示）
    - `--insert-names A,B,C --insert-after-pattern 'REGEX'` : A,B,C を順に結合して、最初にマッチする行の直後へ挿入（順序保持）
    - `--select-index N` / `--interactive` : 複数候補時の選択制御
    - `--short` : LSP 抽出時に `by` 以降を省略

- `lean/dk_math/assistant_driver.py`
  - 機能: 1反復の自動化（ビルド→未定義識別子抽出→候補検索→挿入（dry-run/適用）→報告）
  - 主なオプション: `--build-target`, `--select-index`, `--interactive`, `--apply`

標準ワークフロー（手動・安全志向）

1. まず現状を Git に保持（ブランチやコミット）。既に作業ブランチ上なら不要。
2. `--find-name` で候補を検索し、候補一覧（JSON/markdown）を確認する。
3. `--insert-names` と `--insert-after-pattern` を使って、所定のコメント行（簡潔なマーカーを推奨） の下へ順に挿入する。

- 推奨マーカー（ファイル内に1行だけ置く）: `-- ##INSERT MARKER## --`
- 例: `python theorem_picker.py a.lean /tmp/out.md --insert-names NoSqOnS0,hS0_not_sq_of_NoSqOnS0 --insert-target a.lean --insert-after-pattern "^-- ##INSERT MARKER## --$"`
- この簡潔なマーカーを使うと正規表現を意識せず挿入位置が安定する。

1. `--dry-run` で差分を確認し、問題なければファイルを上書きする（スクリプトは `.inserted` を作るので手動で上書きするか `cp` で反映する）。
2. `./lean-build.sh <target>` を走らせ、エラーを確認する。
3. 未解決の識別子があれば手順 2 に戻るか、`assistant_driver.py` で1反復自動化を実行する。

自動化のガイドライン（安全策）

- 直接上書きする前に `.inserted` の差分を必ず確認する。
- 大きな構造変更（namespace 展開、private の削除等）は自動適用を避け、必ず `--interactive` で承認する。
- キャッシュはしない（ツールの設計方針）。常にリポジトリの最新ソースを参照する。
- 自動化ループは最大試行回数を設定して無限ループを避ける。

実践的ヒント

- 複数ファイルから同名の候補が見つかる場合、`--select-index` で事前に選べる。
- 依存が複雑な補題は、先に小さな補助定義から順に挿入する。ツールの `--insert-names` に順序を与えるとよい。
- LSP 抽出と静的検索の両方を使い分ける（LSP は精度高、静的はオフラインで確実）。

追加・改良予定

- `assistant_driver.py` にバッチ挿入モードを組み込み、発見順に自動で `--insert-names` を呼ぶラッパを作成予定。

問い合わせ

- このマニュアルは賢狼（AI）と人が同じ手順で使えるように設計してある。必要なら実運用用のチェックリストや CI ステップを追加するぞ。

---
（記録: 賢狼ホロ による自動化ツール群の使用手順）
