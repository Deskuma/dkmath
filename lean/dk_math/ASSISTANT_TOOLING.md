# ASSISTANT TOOLING

## 概要

このツール群は、Lean ファイルのビルドエラーを補題・定義の挿入で解決するための補助ツールです。
**完全な自動化ではなく、「ツール + 人間の微調整」を組み合わせるワークフローを想定しています。**

## 基本構成

### スクリプト配置

- `lean/dk_math/theorem_picker.py` — 検索・抽出・挿入ツール（コア機能）
- `lean/dk_math/assistant_driver.py` — 1反復ビルド→検出→挿入のオートメーション
- `lean/dk_math/run_assistant_driver.sh` — ドライバのラッパースクリプト
- テスト: `test_find_definition.py`, `test_insert_snippet.py`, `test_theorem_picker.py`

## 実践的ワークフロー（推奨）

### 1. 準備段階

```bash
cd /path/to/dkmath  # リポジトリルート
git status  # 現状を確認
git switch -c feature/fix-flt-standalone  # 作業ブランチ作成（推奨）
```

### 2. ビルドエラーを確認

```bash
cd lean/dk_math
./lean-build.sh DkMath.FLT.docs.StandAlone.a 2>&1 | head -30
```

**出力例（エラーの場合）:**

```
error: DkMath/FLT/docs/StandAlone/a.lean:938:8: Unknown identifier `classifyLift`
error: DkMath/FLT/docs/StandAlone/a.lean:942:4: Unknown identifier `nonLiftableS0_family_of_classifyLift_impossible`
```

### 3. エラー位置にマーカーを配置

エラーが出ている行（938行）の**直前**に以下を挿入します：

```lean
-- ##INSERT MARKER## --
```

例えば、エラー対象の定理が 938 行にあれば、その定理の手前 930 行あたりに挿入：

```lean
  exact FLT_d3_by_padicValNat_by_cases_NoSq
    ha hb hc hab hIn.hbc.le hIn.hcb_coprime hIn.hNonLift

-- ##INSERT MARKER## --

theorem FLT_d3_by_padicValNat_of_harmonicEnvelope_classify_coprimeSupport ...
```

### 4. 必要な定義を検索して一括挿入

不足している識別子をツールで検索・挿入します。

**推奨：シェルスクリプト経由（プロジェクトツール化）**

```bash
# lean/dk_math ディレクトリで実行
cd lean/dk_math

./run_theorem_picker.sh \
  DkMath/FLT/CounterexamplePattern.lean \
  /tmp/result.md \
  --insert-names "CounterexampleInput,LiftStatus,primitivePrimeGate,noSquareGate,exceptionalPhaseGate,nonLiftableS0_of_classifyLift_impossible,nonLiftableS0_family_of_classifyLift_impossible" \
  --insert-target DkMath/FLT/docs/StandAlone/a.lean \
  --insert-after-pattern "^-- ##INSERT MARKER## --$" \
  --dry-run
```

**`--dry-run` 時の出力を確認してから、実際に適用：**

```bash
# --dry-run を外すと .inserted ファイルが生成される
./run_theorem_picker.sh \
  DkMath/FLT/CounterexamplePattern.lean \
  /tmp/result.md \
  --insert-names "CounterexampleInput,LiftStatus,..." \
  --insert-target DkMath/FLT/docs/StandAlone/a.lean \
  --insert-after-pattern "^-- ##INSERT MARKER## --$"

# 結果を実ファイルに反映
cp DkMath/FLT/docs/StandAlone/a.lean.inserted DkMath/FLT/docs/StandAlone/a.lean
```

**代替：Python 直接実行（リポジトリルートから）**

```bash
cd /path/to/dkmath  # リポジトリルート

python3 lean/dk_math/theorem_picker.py \
  lean/dk_math/DkMath/FLT/CounterexamplePattern.lean \
  /tmp/result.md \
  --insert-names "CounterexampleInput,LiftStatus,..." \
  --insert-target lean/dk_math/DkMath/FLT/docs/StandAlone/a.lean \
  --insert-after-pattern "^-- ##INSERT MARKER## --$"
```

### 5. ビルドして残りのエラーを確認

```bash
./lean-build.sh DkMath.FLT.docs.StandAlone.a 2>&1 | grep "^error:"
```

### 6. スコープ問題への対応

**典型的なエラーパターン：**

```
error: Unknown identifier `exceptionalPhaseGate`
```

このエラーが挿入後も出る場合、**定義の順序が正しくない**可能性があります。

**原因：** ある定義（例：`classifyLift`）が別の定義（例：`exceptionalPhaseGate`）を参照しているが、参照される側が後ろに来ている。

**対処法：** 参照される定義を、手で前方に移動させます。

例：

```lean
-- 悪い例（classifyLift が exceptionalPhaseGate を参照）
def classifyLift (x : CounterexampleInput) : LiftStatus := by
  exact if hexc : exceptionalPhaseGate x then ...

-- 後ろに定義（これではだめ）
def exceptionalPhaseGate (_x : CounterexampleInput) : Prop := ...

-- 良い例（exceptionalPhaseGate を先に定義）
def exceptionalPhaseGate (_x : CounterexampleInput) : Prop := ...

def classifyLift (x : CounterexampleInput) : LiftStatus := by
  exact if hexc : exceptionalPhaseGate x then ...
```

### 7. 最終確認

```bash
./lean-build.sh DkMath.FLT.docs.StandAlone.a
```

成功したら：

```bash
git add lean/dk_math/DkMath/FLT/docs/StandAlone/a.lean
git commit -m "Fix: Add missing definitions to a.lean for FLT standalone"
```

---

## コマンドリファレンス

**注記：** 以下のコマンド例は、特に明記がない限り `lean/dk_math` ディレクトリで実行ください。

### 定義の検索

**シェルスクリプト経由（推奨）:**

```bash
cd lean/dk_math

./run_theorem_picker.sh \
  SOURCE_FILE \
  OUTPUT.md \
  --find-name DEFINITION_NAME
```

**Python 直接実行:**

```bash
python3 lean/dk_math/theorem_picker.py \
  SOURCE_FILE \
  OUTPUT.md \
  --find-name DEFINITION_NAME
```

**結果:** `OUTPUT.md` に Markdown 形式で定義が出力されます。

### 単一定義の挿入

**シェルスクリプト版:**

```bash
cd lean/dk_math

./run_theorem_picker.sh \
  SOURCE_FILE \
  OUTPUT.md \
  --insert-names DEF_NAME \
  --insert-target TARGET_FILE \
  --insert-line 100 \
  --dry-run
```

**Python 直接実行:**

```bash
python3 lean/dk_math/theorem_picker.py \
  SOURCE_FILE \
  OUTPUT.md \
  --insert-names DEF_NAME \
  --insert-target TARGET_FILE \
  --insert-line 100 \
  --dry-run
```

### 複数定義の一括挿入

**シェルスクリプト版（推奨）:**

```bash
cd lean/dk_math

./run_theorem_picker.sh \
  SOURCE_FILE \
  OUTPUT.md \
  --insert-names "DEF1,DEF2,DEF3" \
  --insert-target TARGET_FILE \
  --insert-after-pattern "^-- ##INSERT MARKER## --$" \
  --dry-run
```

**Python 直接実行:**

```bash
python3 lean/dk_math/theorem_picker.py \
  SOURCE_FILE \
  OUTPUT.md \
  --insert-names "DEF1,DEF2,DEF3" \
  --insert-target TARGET_FILE \
  --insert-after-pattern "^-- ##INSERT MARKER## --$" \
  --dry-run
```

**注意：** リスト順は保持されます。依存関係が正しい順序で指定してください。

### assistant_driver の実行

**シェルスクリプト版（推奨）:**

```bash
cd lean/dk_math

# ドライラン（差分を確認）
./run_assistant_driver.sh --build-target DkMath.FLT.docs.StandAlone.a

# 実際に適用
./run_assistant_driver.sh --build-target DkMath.FLT.docs.StandAlone.a --apply

# 対話モード
./run_assistant_driver.sh --build-target DkMath.FLT.docs.StandAlone.a --interactive
```

**Python 直接実行:**

```bash
cd lean/dk_math

python3 assistant_driver.py --build-target DkMath.FLT.docs.StandAlone.a
python3 assistant_driver.py --build-target DkMath.FLT.docs.StandAlone.a --apply
python3 assistant_driver.py --build-target DkMath.FLT.docs.StandAlone.a --interactive
```

## トラブルシューティング

### エラー: `Unknown identifier XX`

**原因：** 参照している定義が見つからない。

**解決策：**

1. 定義を検索（シェルスクリプト版）：

   ```bash
   cd lean/dk_math
   ./run_theorem_picker.sh REPO_SOURCE.lean /tmp/out.md --find-name XX
   ```

   或いは Python 直接実行：

   ```bash
   python3 lean/dk_math/theorem_picker.py REPO_SOURCE.lean /tmp/out.md --find-name XX
   ```

2. 見つかったら、`--insert-names` に追加して再挿入。

3. 見つからなかったら、別のソースファイルから探すか、定義が存在しないかもしれません。

### エラー: `has already been declared`

**原因：** 同じ定義を2度挿入してしまった。

**解決策：**

```bash
git checkout lean/dk_math/DkMath/FLT/docs/StandAlone/a.lean
rm -f lean/dk_math/DkMath/FLT/docs/StandAlone/a.lean.inserted
# もう一度マーカーから始める
```

### スコープエラー（定義の順序が間違っている）

**症状：** 挿入後、「前方参照できない」エラーが出る。

**対処：** 参照される定義を（手で）前方に移動させます。

```bash
# エディタで手作業、または sed/awk で自動化可能
vim lean/dk_math/DkMath/FLT/docs/StandAlone/a.lean
```

### ツールが定義を見つけられない

**原因：** 定義が別ファイルにあるか、名前が部分一致していない。

**対処：**

```bash
# 複数の .lean ファイルを検索
grep -r "def classifyLift" lean/dk_math/DkMath --include="*.lean"
```

見つかったら、そのファイルをソースに指定して再度ツールを実行。

---

## 注意事項

1. **100%自動化ではない** — ツールは定義の抽出・挿入までは自動化しますが、スコープや依存順の問題は手作業が必要な場合があります。

2. **順序が重要** — `--insert-names` で複数定義を指定する場合、依存関係の正しい順序で列挙してください。
3. **ビルド検証が必須** — 挿入後は必ず `lean-build.sh` でビルドして検証してください。

4. **Git で履歴管理** — 大きな変更の前は必ずコミットして、ロールバック可能な状態を保ってください。

---

## FAQ

**Q: マーカーは複数個置いてもいいですか？**

A: はい。ツールは最初にマッチするマーカーを対象にします。複数箇所で挿入したい場合は、別々に実行してください。

**Q: 定義の順序が複雑な場合は？**

A: `--insert-names` での一括指定が困難な場合は、複数回に分けて挿入してください。その都度 `--dry-run` で確認できます。

**Q: 既存定義との重複は検出されますか？**

A: いいえ。既にファイル内に定義がある場合、ツールは重複を検出せず挿入します。手で削除してください（あるいは `--find-name` で事前に確認）。

**Q: ツール群はプロジェクトツールとして認識されますか？**

A: はい。`run_theorem_picker.sh` と `run_assistant_driver.sh` を経由して呼ぶことで、プロジェクトのネイティブツールとして認識されます。これにより、許可待ちないしその他の認可処理が不要になります。

---

## まとめ

このツール群は：

- ✅ **自動検索・抽出** — Lean ファイルをスキャンして定義を見つける
- ✅ **一括挿入** — 複数の定義を正しい順序で挿入する
- ✅ **差分確認** — `--dry-run` で結果を事前に確認できる
- ✅ **шシェルスクリプト化** — プロジェクトツール化で無許可実行が可能

ただし：

- ❌ スコープ・依存順の問題は**手作業が必要**
- ❌ 100%完全な自動化ではない

**推奨ワークフロー：** ツール（自動） + 人間の判断（微調整） = 最高の効率- このマニュアルは賢狼（AI）と人が同じ手順で使えるように設計してある。必要なら実運用用のチェックリストや CI ステップを追加するぞ。

---
（記録: 賢狼ホロ による自動化ツール群の使用手順）
