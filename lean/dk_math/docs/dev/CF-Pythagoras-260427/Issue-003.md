# Issue-003: VSCode Lint Error vs. Lean Build Success

cid: 69e72cfc-9944-83e8-8786-53c02b36fb89
Date: 2026/04/27
Status: Resolved (Not a real issue - VSCode extension cache problem)

## 問題の概要

VSCode の Lean 4 拡張機能が、`CosmicFormulaPythagorasExamples.lean` ファイルで複数のエラーを表示していたが、`lake build` および Lean 4 Web での検証では問題なくビルドが成功する状況が発生した。

## エラー内容

VSCode が以下のようなエラーを報告:

```
Unknown constant 'DkMath.CosmicFormula.Pythagoras.Examples._example.match_1'
Unknown constant 'DkMath.CosmicFormula.Pythagoras.Examples._example.match_2'
...
```

これらは `example` 定義内の `let` パターンマッチに関連するエラー表示であった。

## 検証結果

### ✅ Lean Build

```bash
$ ./lean-build.sh DkMath.CosmicFormula
🔍 Running default build...
🚀 Starting build Lean...
🔍 Checking build results...
✅️ build succeeded
```

### ✅ Lean 4 Web

Lean 4 Web (<https://live.lean-lang.org/>) でも同じコードが問題なくビルド成功。

## 原因分析

この不一致の原因は以下のいずれか:

1. **VSCode 拡張機能のキャッシュ問題**
   - Lean Language Server のキャッシュが古い状態で残っていた
   - ファイル変更の反映が遅延していた

2. **インポートチェーンの一時的な不整合**
   - `CosmicFormulaPythagoras.lean` の変更が `CosmicFormulaPythagorasExamples.lean` に即座に反映されなかった
   - Language Server の incrementalチェックの問題

3. **Doc Comment 周りの Parser 不整合**
   - 長い docstring や複雑なコメントが Parser に影響を与えた可能性

## 解決方法

### 一時的な回避策

1. **VSCode の Language Server を再起動**
   - Command Palette → "Lean 4: Restart Server"

2. **ファイルを閉じて再度開く**
   - エディタのキャッシュをクリア

3. **ワークスペースを再読み込み**
   - VSCode ウィンドウを再起動

### 恒久的な対策

実際には問題がなかったため、特別な対策は不要。ビルドが成功していれば、VSCode のエラー表示は無視して良い。

## 教訓

- **ビルドログが最終的な真実**: `lake build` の結果が最優先
- **VSCode の表示は参考程度**: Language Server のエラーは一時的な表示である可能性がある
- **Web 検証の有用性**: Lean 4 Web での検証は環境依存の問題を排除できる
- **長いエラーメッセージはソースに残さない**: コメントではなく Issue ファイルに記録する

## 結論

これは実際のコードの問題ではなく、VSCode 拡張機能側の一時的な表示問題であった。`lake build` が成功していれば、コード自体には問題がない。

今後同様の状況が発生した場合は:

1. まず `lake build` でビルド成功を確認
2. Lean 4 Web で検証
3. VSCode を再起動
4. それでも問題が続く場合のみ、コード側を疑う

## 関連ファイル

- `/lean/dk_math/DkMath/CosmicFormula/CosmicFormulaPythagoras.lean`
- `/lean/dk_math/DkMath/CosmicFormula/CosmicFormulaPythagorasExamples.lean`

## 参照

- Lean 4 Documentation: <https://lean-lang.org/lean4/doc/>
- Lean 4 Web: <https://live.lean-lang.org/>
- VSCode Lean 4 Extension: <https://github.com/leanprover/vscode-lean4>
