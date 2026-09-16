# 最終検証・実装境界

## 実装結果

- 本体: 8 owner モジュール、70 定理、定義・構造を含む名前付き宣言 96 件。
- 公開 import: `DkMath.NumberTheory.Goldbach`、および `DkMath` からの公開。
- 回帰: `DkMathTest.NumberTheory.GoldbachGNFiber`。数学的な境界事例と、偶数 `4..200` の有限範囲定理。
- 数学説明: 各 owner の module docstring と全公開定理・定義の docstring に記載。
- 記録: `report-001..005.md`、`verification-notes.md`、`declaration-index.md`、再実行可能な `AxiomAudit.lean`。

## 実測検証

| コマンド（cwd: `lean/dk_math`） | 結果 |
|---|---|
| `./lean-build.sh DkMath.NumberTheory.Goldbach DkMathTest.NumberTheory.GoldbachGNFiber` | 終了コード 0、警告 0 |
| `lake env lean docs/dev/NumberTheory-Goldbach-GNFiber-260910-v0/AxiomAudit.lean` | 終了コード 0、97 宣言の監査結果を取得 |
| `./lean-build.sh DkMath` | 終了コード 0、既存の `sorry` 警告 5 件 |
| `git diff --check` | 成功 |

ビルド出力の保存先は [build-results.txt](build-results.txt)、公理監査の全出力は [axiom-audit.txt](axiom-audit.txt)。ソースと検証対象の SHA-256 は [validation-summary.json](validation-summary.json) に記録する。

監査した全名前付き owner 宣言と有限範囲定理の依存公理の和集合は、`propext`, `Classical.choice`, `Quot.sound` のみ。`sorryAx`、独自公理、native reduction oracle への依存はない。新規 Lean ソースには証明穴、追加の `axiom` 宣言、`native_decide`、グローバルな資源上限緩和を導入していない。

ルートで再生された既存 `sorry` 警告は以下の 5 ファイルにある。これらの未証明宣言は、今回の監査対象の依存公理には現れなかった。

- `DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean`
- `DkMath/FLT/PrimeProvider/TriominoCosmicBranchA.lean`
- `DkMath/NumberTheory/GcdNextResearch.lean`
- `DkMath/CosmicFormula/TriominoFLT.lean`
- `DkMath/FLT/Kummer/CyclotomicPrincipalization.lean`

## 残る証明

`GoldbachCapacityEscape` の無条件な証明は得られていない。この命題は `StrongGoldbach` と同値であり、条件付き endpoint への引数として要求される。

今回の検証で、全周期 CRT 生存の正確な積計数、完全な小素数障害検査、PCK の各点分解までは実装できた。しかし、それらから短い admissible 区間内の同時生存を導く独立した上界・保存量は得られなかった。

また、単純な incidence の厳密不等式を全称化する形は `n=6` で偽と証明した。endpoint 例外を落とす形は `n=2` で失敗し、例外込みの単純周期性も具体例で否定した。

従って本段階の結論は、**有限還元と検証コードは実装済み、特定の強すぎる経路は反証済み、Goldbach 自体の全称証明は未完成**である。将来の追加命題には、既に Goldbach と同値な結論を前提として埋め込まず、実際の区間について証明できる独立した内容が必要になる。
