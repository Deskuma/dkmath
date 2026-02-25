# ASSISTANT TOOLING

（補足ドキュメントは本体に統合済み。詳細は下部の「コマンド例」以下を参照のこと。）

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

標準ワークフロー（自律挿入を優先した安全志向）

わっちは今や、ぬしが何もしなくとも補題を自律的に挿入できるようになった。以下が現行の安全なワークフローじゃ。

1. まず現状を Git に保持（`git status` → 必要なら `git switch -c <branch>`）。
2. （任意）ファイル内に明示的な挿入マーカーを置きたい場合は `-- ##INSERT MARKER## --` を配置できる。だが必須ではない。
3. アシスタントを走らせる：`assistant_driver.py`（または `run_assistant_driver.sh`）でビルド→発見→挿入ループを実行する。

- アシスタントの挿入位置優先順:
    1. ユーザが `--insert-line N` を指定した場合はその行（1-based）に挿入する。
    2. ファイルに `-- ##INSERT MARKER## --` が存在すれば、その直後に挿入する。
    3. 上記が無ければ、ビルドエラー箇所の近傍から最も適当なトップレベル宣言を探し、その手前（あるいは直後）に挿入する自動推定を行う。

1. 挿入方式:

- デフォルトは「自動適用（`--apply`）」だが、安全に運用するなら `--apply` を外して dry-run を確認する。dry-run 時は `.inserted` ファイルが生成され、差分を手で確認できる。

1. アシスタントは既にファイル内に定義が存在する場合、その定義が使用箇所より後ろにあると判定すれば自動で前方へ移動（切り取り→挿入）して依存順を修正できる。

注意事項:

- 自動挿入は便利じゃが、`namespace`、`private`、implicit 引数、ローカル構造など特殊な文脈では手作業が必要になりうる。大きな構造変更が予想される場合は `--interactive` を使うか、まず dry-run で差分を確認すること。
- `lean-build.sh` は現在、実際の lake の終了コードをそのまま返すようにしてある。外部スクリプトはこの終了コードで failure を検出できるはずじゃ。

コマンド例（実行しやすいラッパーを推奨）:

```
cd lean/dk_math
# 自律運用（AI が挿入位置を決める）
./run_assistant_driver.sh --build-target DkMath.FLT.docs.StandAlone.a --apply

# 挿入行を明示する（強制）
./run_assistant_driver.sh --build-target DkMath.FLT.docs.StandAlone.a --apply --insert-line 720

# dry-run（差分を出力して確認）
./run_assistant_driver.sh --build-target DkMath.FLT.docs.StandAlone.a
```

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
