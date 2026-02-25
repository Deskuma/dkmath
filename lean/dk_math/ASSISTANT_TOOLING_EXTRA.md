# アシスタントツールの運用に関する追加説明

重要: 挿入マーカーはアシスタントAIが配置する（ユーザは不要）

- 設定変更: 本ツールは、ユーザが明示的にマーカーを置かなくともアシスタントAIが挿入位置を決めて補題を追加できるようになった。つまりユーザは基本的に何もしなくて良い。
- 動作概要: アシスタントは以下の優先順で挿入位置を決定する。

 1. ユーザが `--insert-line N` オプションで明示した行（1-based）があればそこを使う。
 2. 対象ファイルに `-- ##INSERT MARKER## --` が存在すれば、その直後に挿入する（ユーザがマーカーを置きたい場合はこれを使える）。
 3. 上記が無い場合は、ビルドエラーの発生箇所の近傍から最も適当なトップレベル宣言を探し、その手前または直後に挿入する（自動推定）。

- 理由: ユーザ負担を減らすため、アシスタントが自律的に挿入位置を決定する。とはいえ特殊な文脈（namespace、private、implicit 等）がある場合は手修正が必要となる可能性があるため、その場合は差分を確認してユーザ承認を得る運用を推奨する。

改訂運用手順（簡潔）

1. リポジトリの現在状態を保存（`git status` → 必要なら `git switch -c <branch>`）。
2. 挿入したいファイルにマーカー行を配置する（例: `-- ##INSERT MARKER## --`）。
3. `assistant_driver.py` を実行してビルドを行う。
4. ビルドで Unknown identifier が出たら、アシスタントは候補補題を検索し、上記のルールに従って挿入する。
5. 挿入後に再ビルド。エラーが残る場合は 3-5 を繰り返す。
6. 最終的にビルド成功したら差分確認の上コミットする。

起動スクリプト（推奨）

VSCode などから `python3 ... .py` を直接呼ぶより、短いシェルラッパーを使うと実行許可の付与やタスク設定が楽になる。`lean/dk_math` に次のラッパーを用意してある:

- `run_theorem_picker.sh` : `theorem_picker.py` のラッパー
- `run_assistant_driver.sh` : `assistant_driver.py` のラッパー

使い方例:

```
cd lean/dk_math
# 自律運用（AI が挿入位置を決める）
./run_assistant_driver.sh --build-target DkMath.FLT.docs.StandAlone.a --apply

# 挿入行を明示する（強制）
./run_assistant_driver.sh --build-target DkMath.FLT.docs.StandAlone.a --apply --insert-line 720

# dry-run（差分を出力して確認）
./run_assistant_driver.sh --build-target DkMath.FLT.docs.StandAlone.a
```

この追加ドキュメントは、既存の `ASSISTANT_TOOLING.md` に対する補足として運用手順を明確化するためのものじゃ。必要なら本体に統合しておくれ。
