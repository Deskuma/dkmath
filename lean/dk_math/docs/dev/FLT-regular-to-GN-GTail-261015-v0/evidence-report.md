# FLT3・FLT5・FLT7 / Kummer × GN・GTail — 検証要約

- 記録日: 2026-10-17 JST
- 対象: `research/FLT-regular-to-GN-GTail-261015-v0` → `develop`
- 環境: `lean/dk_math`、Lean / Mathlib v4.34.1
- 目的: `evidence/` に蓄積した123ファイルの検証記録から、**マージ後に必要な結論・再現手順・監査境界**を残す。
- 詳細な標準出力、smoke 用 Lean スクリプト、試行時点別ログなどは `evidence/` を tar に固めて保存する。本書はその代替ログではなく、要約索引である。

## 1. 到達点と証明範囲

| テーマ | 到達した結果 | 証明上の区別 |
| --- | --- | --- |
| Kummer × GN / GTail | GN の円分因子・ノルム・イデアル冪配分・分岐商・単元処理の補題群を構築 | 一般正則素数に対する FLT 全体の証明ではない |
| FLT3 再証明 | `DkMath.FLT.Kummer.fermatThree_no_positive_solution_via_GN` | 同じ Eisenstein 剥離商の三乗を GN・円分イデアル経由で供給し、既存の算術的な厳密降下を再利用。既存の完成 FLT3 終点を結論としては使用しない |
| FLT5 再証明 | `DkMath.FLT.Kummer.fermatFive_no_positive_solution_via_GN` | 黄金比整数への相対ノルム・具体的五次 Kummer 単元補題・同じ剥離商の五乗を接続。既存の Golden 零セクター厳密降下と一般単元分類は再利用 |
| **FLT7 無条件形式化** | **`DkMath.FLT.Kummer.SevenDescent.fermatLastTheoremFor_seven : _root_.FermatLastTheoremFor 7`** | 具体的七次円分整数環で正深度 `State m` の底と一段降下を実装。外部 FLT7 終点・追加の降下 provider を引数にしない |
| AKS / GN の周辺接続 | 幅1の GN から Fermat 型の合同を再構成する補題 | FLT 終点や一般の無限降下を主張しない |

FLT7 の反復状態は、非分岐条件と原始性を保持した
`x^7 + y^7 = ε * (λ^m * z)^7`（`λ = 1-ζ`、`λ ∤ y,z`、`IsCoprime x y`）。
七位相のうち一つだけ追加の `λ` を含むことから `no_state_one` を示し、互いに素な商イデアルの七乗配分・具体的 PID・単元比の七乗化から
`descent_step : Nonempty (State (m+1)) → Nonempty (State m)` を構成する。
正深度状態の不存在、原始反例からの初期化、Mathlib の gcd 正規化を経て標準 FLT7 型へ到達した。
**FLT7 の証明対象は指数7であり、任意の正則素数への一般化ではない。**

## 2. 主要な検証実績（すべて記録上 PASS）

| 対象 | 最終的な代表ビルド | 回帰・公理検査 | 再帰的依存監査 |
| --- | --- | --- | --- |
| GN/Kummer 基盤 | `DkMath` と指定 GN テスト: 10,480～10,502 jobs の各段階で exit 0 | 各段階の新宣言を標準3公理 whitelist で検査 | 段階別の出力を保存 |
| FLT3 GN | `DkMath` + 指定テスト: **10,512 jobs**, exit 0 | **26公開宣言**、**11回帰例** | 終点: **74,404 定数 / 71,748 本体** |
| FLT5 GN | `DkMath` + 指定テスト: **10,515 jobs**, exit 0 | **62公開宣言**、**16回帰例** | 同じ β の根: **74,704 / 72,020**、終点: **75,120 / 72,425** |
| FLT7 GN 降下 | `DkMath` + 指定テスト: **10,542 jobs**, exit 0 | **44公開宣言**（39定理・4定義・1構造体）、**4回帰例** | 最終終点: **76,323 / 73,608**、深度1の排除: **72,825 / 70,209** |
| AKS/GN 接続 | `DkMath` + 指定テスト: **10,486 jobs**, exit 0 | **8定理**、**9回帰例** | この段階の独立した終点監査は主張しない |

各数値は、対応する `evidence/validation-*.txt` に記録された**当時の指定ビルド**の数値。異なる実行の jobs を合算しない。特に「指定テストを含む root ビルド」を「全 `DkMathTest` の実行」と読み替えない。

## 3. 公理・依存監査・残存警告

- 新しい FLT3・FLT5・FLT7 各終点の `Lean.collectAxioms` と、コンパイル済みの型・証明本文（opaque 含む）・帰納型コンストラクタを辿る再帰的依存監査では、許可する公理葉は **`propext`、`Classical.choice`、`Quot.sound` のみ**。
- 監査では、必要な GN・イデアル・単元・環同型・降下の実 provider への到達を要求し、`sorryAx` や既存の完成済み FLT 終点への近道を禁じる。FLT7 では `FltRegular` / Anthropic `P2MW`、旧選択 common-prime、小ノルム・補正根パケット等への依存も禁止して確認した。
- **注意:** `DkMath` の大域 import / ビルドには、以下の既存 `sorry` 警告が5件残る。リポジトリ全体が `sorry` 不在という主張ではない。

| 既存警告の場所 | 行 |
| --- | ---: |
| `DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean` | 147 |
| `DkMath/CosmicFormula/TriominoFLT.lean` | 1919 |
| `DkMath/FLT/PrimeProvider/TriominoCosmicBranchA.lean` | 4187 |
| `DkMath/NumberTheory/GcdNextResearch.lean` | 850 |
| `DkMath/FLT/Kummer/CyclotomicPrincipalization.lean` | 5389 |

上記5件は**新しい監査対象の FLT3・FLT5・FLT7 終点の証明グラフに含まれない**との検証記録がある。ビルド成功だけでこれを推論したのではなく、公理および依存監査を区別して確認している。

## 4. 再現のためのコマンド

作業ディレクトリは `lean/dk_math`。環境・依存を固定した同じ checkout で実行する。

```bash
# 公開入口と FLT7 の回帰・証明依存監査（記録済みの最終指定ビルド）
LAKE_ARTIFACT_CACHE=false LAKE_NO_CACHE=true LEAN_NUM_THREADS=2 lake build \
  DkMath DkMath.FLT.Kummer \
  DkMathTest.FLT.Kummer.SevenGNDescent \
  DkMathTest.FLT.Kummer.SevenGNDescentDependencyAudit

# FLT3 / FLT5 の指定テスト・依存監査（必要に応じて再実行）
LEAN_NUM_THREADS=2 lake build \
  DkMathTest.FLT.Kummer.ThreeGNDescent \
  DkMathTest.FLT.Kummer.ThreeGNDependencyAudit \
  DkMathTest.FLT.Kummer.FiveGNDescent \
  DkMathTest.FLT.Kummer.FiveGNDependencyAudit DkMath

# 追加の smoke ソースは evidence アーカイブから復元して実行
# lake env lean docs/dev/FLT-regular-to-GN-GTail-261015-v0/evidence/SevenGNDescentSmoke.lean
```

最後の複合 FLT3/5 コマンドは、各対象の検査を集約した**再現用の提案**であり、そのままの引数列に対する実行ログを主張しない。個別の実行済みコマンドと結果はアーカイブ内の `validation-three-gn.txt`、`validation-five-gn.txt`、`validation-seven-gn-descent.txt` を正本とする。

別途、利用者が `./lb`（10,540 jobs）と `./lb -T`（11,427 jobs）を手動実行して両方成功したとの報告がある。これは本ディレクトリの個別検証ログとは区別する。PR の Lean CI GREEN も報告されているが、**ブランチ更新後の CI 状態は再確認を要する**。

## 5. 監査境界とアーカイブの扱い

- FLT7 の初期探索で作った六位相族・実三次ノルム・共通補正根・小ノルムパケットも Lean 検証済みの独立した研究成果だが、**新 FLT7 終点の必要な依存グラフには入らない**。詳細は同階層の各 `SEVEN-*.md` 章に残す。
- `FLT7-PROOF-ROUTE-AUDIT.md` の旧 scratch は、その時点で底と step が未解決だった履歴。現在の `SevenGNDescent.lean` と `SEVEN-GN-DESCENT-TEXTBOOK.md` が最終到達点。
- Anthropic / `flt-regular` は比較・設計参考資料であり、DkMath の新 FLT7 終点に外部の完成証明を import したことにはならない。
- 本書がまとめるのは **Lean 形式化と既存の検証記録**。独立した数学的査読を完了したという意味ではない。
- `evidence/` には出力ログ、smoke ソース、依存監査の出力、当時の入力照合資料が含まれる。これらは実験時点の履歴資料であり、清書後のコード正本を定義するものではない。ソースの状態は **Git のコミット SHA** で固定する。
- 既存の教科書にある `evidence/*.txt` / `evidence/*.lean` のリンクは**変更しない**。詳細な検証記録が必要なら、同階層に置いた tar アーカイブから `evidence/` ディレクトリを復元して閲覧する。tar 作成時は `tar -cf evidence.tar evidence/`、復元時は `tar -xf evidence.tar` が一例（アーカイブ名は実際の運用に合わせる）。アーカイブと対応するソースの基準コミット SHA を記録すればよく、個別ファイルのハッシュ再計算は要求しない。

## 6. 読むべき教科書（アーカイブ不要の恒久参照）

- [FLT7 無条件証明](SEVEN-GN-DESCENT-TEXTBOOK.md)
- [FLT7 証明経路の棚卸し](FLT7-PROOF-ROUTE-AUDIT.md)
- [FLT3 GN 再証明](THREE-GN-DESCENT.md)
- [FLT5 GN 再証明](FIVE-GN-DESCENT-AND-SEVEN.md)
- [研究全体の導入](README.md) / [基盤実装と履歴](IMPLEMENTATION.md)

**マージ判定用の要点:** FLT3・FLT5 の GN 経由終点と FLT7 の Mathlib 標準終点について、指定 Lean ビルド、公理 whitelist、再帰的依存監査が通過している。旧 `sorry` は repository に残るが、監査対象の新終点には入らない。独立数学レビューは別工程として扱う。
