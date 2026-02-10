# Idea: Lean Server の複数実行防止策

## 背景

現在の `theorem_picker.py` と `test_theorem_picker.py` では、各 Lean ファイルの処理ごとに新しい Lean LSP サーバープロセスを起動しています。これにより、以下の問題が発生します：

- テスト実行時間が長くなる（特に複数ファイルを処理する場合）
- CI 環境での不安定性（サーバー起動のオーバーヘッド）
- リソース消費が大きい（並列実行時に複数サーバーが同時稼働）

## 現在の実装

- `theorem_picker.py` は1ファイルの処理ごとに `lake env lean --server` を起動
- テストで複数ファイルを処理する場合、ファイル数だけサーバーが起動される
- 各サーバーは処理完了後に終了

## 改善案

### 1. サーバーインスタンスの再利用

**アプローチ**: 1つの Lean LSP サーバーインスタンスを複数ファイルの処理で再利用

**メリット**:
- サーバー起動コストを1回に削減
- 処理速度の向上
- リソース消費の削減

**実装の課題**:
- ファイル間の状態クリーンアップ（`textDocument/didClose` の適切な送信）
- サーバーの状態管理（エラー発生時の復旧）
- プロジェクトルートが異なるファイルへの対応

**実装例**:
```python
class LeanLspClient:
    def process_file(self, file_path: Path) -> List[Symbol]:
        """既存サーバーでファイルを処理"""
        # textDocument/didOpen でファイルを開く
        symbols = self.get_document_symbols(file_path)
        # textDocument/didClose でファイルを閉じる（状態クリーンアップ）
        return symbols

# 使用例
with LeanLspClient.create() as client:
    for lean_file in lean_files:
        symbols = client.process_file(lean_file)
        # 処理...
```

### 2. バッチ処理モードの追加

**アプローチ**: `theorem_picker.py` に複数ファイルを一括処理するオプションを追加

**メリット**:
- CLI から複数ファイルを効率的に処理可能
- サーバー起動を1回に抑制
- テストでも利用可能

**実装例**:
```bash
# 複数ファイルを一括処理
python theorem_picker.py --batch file1.lean file2.lean file3.lean --output-dir ./output/

# ディレクトリ内の全ファイルを処理
python theorem_picker.py --batch-dir ./DkMath/CosmicFormula/ --output-dir ./output/
```

### 3. キャッシュ機構の導入

**アプローチ**: LSP サーバーの応答をキャッシュし、再処理時に再利用

**メリット**:
- 同一ファイルの再処理が高速化
- テストの実行時間短縮
- CI での安定性向上

**実装の課題**:
- キャッシュの無効化タイミング（ファイル変更検出）
- ディスク容量の管理
- キャッシュの保存形式

### 4. テスト戦略の見直し

**現在の改善（本PR）**:
- 専用のサンプルファイル `TestShort.lean` を使用
- 複数ファイルのイテレーションを避ける
- 決定的なテスト結果を保証

**今後の拡張案**:
- サーバー起動を1回だけ行うテストフィクスチャの導入（pytest fixture）
- モックサーバーの使用（完全な Lean 環境不要なテスト用）

## 推奨アプローチ

短期的（次の改善サイクル）:
1. **サーバーインスタンスの再利用**を実装
   - 既存の `LeanLspClient` クラスに `process_file` メソッドを追加
   - コンテキストマネージャーパターンで安全な管理
   
2. **テストでの適用**
   - pytest fixture でサーバーインスタンスを共有
   - セットアップ/ティアダウンを1回のみ実行

長期的:
- バッチ処理モードの追加
- キャッシュ機構の検討（必要に応じて）

## 参考実装

### pytest fixture でのサーバー共有例

```python
import pytest
from theorem_picker import LeanLspClient

@pytest.fixture(scope="module")
def lean_server():
    """テストモジュール全体で1つのサーバーインスタンスを共有"""
    client = LeanLspClient.create()
    yield client
    client.shutdown()

def test_multiple_files(lean_server):
    """共有サーバーで複数ファイルをテスト"""
    for lean_file in test_files:
        symbols = lean_server.process_file(lean_file)
        # アサーション...
```

## まとめ

Lean LSP サーバーの複数実行を防ぐことで、テストの高速化・安定化、CI での信頼性向上が期待できます。まずはサーバーインスタンスの再利用から始め、段階的に改善していくことを推奨します。

---

**作成日**: 2026-02-10  
**関連 PR**: #37（--short オプション追加）  
**次のステップ**: サーバーインスタンス再利用の実装検討
