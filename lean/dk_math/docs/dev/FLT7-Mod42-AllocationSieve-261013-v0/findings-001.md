# findings-001 — gate 001

## 開始時のソース監査

- 現在のブランチ: `research/FLT7-Mod42-AllocationSieve-261013-v0`。開始時 `git status --short --branch` に変更なし。
- README / ROADMAP / instruction-001 を読了。実行範囲は gate 001 の算術二定理のみ。
- theorem index 再構築: 1,802 Lean files / 29,253 declarations、終了コード 0。
- index と実ソースで `nestedAllocation_residue_sieve` を確認。既存結論は `Nat.ModEq 7 (M / r) 1`。
- `alternatingCyclotomicSeven` 関連 index 検索は14件。対象の mod 6 定理に相当する既存宣言は関連モジュール / Lib / 全 DkMath のテキスト検索で見つからない。
- SymmetricReconstruction / AllocationThreshold / AllocationResidueSieve / SixthPowerAllocationSieve の既存定義と証明を確認。
- 自然数交代因子は `(x^7+y^7)/(x+y)`。`alternatingCyclotomicSeven_intCast` が符号付き整数 cyclotomicSeven 多項式への正当な変換を与える。自然数減算で多項式を捏造しない。
- GN は canonical `DkMath.CosmicFormula.GN` の互換略記。`GN_seven_eq_gap_mul_add_seven_mul_y_pow_six` の既存展開を使う。
- GN receiver は `Nat.Coprime u (7*M)` を持つが `r ∣ M` を含まない。gate 002 の追加ガードを保持する必要がある。

## 証明方針

互いに素な自然数対は 2 と 3 を共有しない。mod 6 の36対のうち共有因子のある12対を排除し、残る24対について既存多項式をカーネル検証する。スクラッチと検証は DkMathTest 配下に置く。

## 最初の calibration（終了コード1）

`norm_num at hp ⊢` は排除ケースで「No goals to be solved」、残存ケースで ZMod の数値等式（例: `15625 = 1`）を残した。これは命題の反例ではなく戦術上の失敗。排除は `norm_num at hp`、閉じた ZMod 等式はカーネル還元の `decide` と分ける。失敗ログを `logs/calibration-first.txt` に保存。

## 校正成功と production 化

修正した `ModSixCalibration.lean` の `lake env lean` は終了コード0。重複する校正証明は production に移し、最終的な DkMathTest モジュールには API 適用・反例・公理監査を残す。

指示書の `lake build -j 1 ...` は現行 Lake 5.0.0 / Lean 4.34.1 で `unknown short option '-j'`（終了コード1）。互換コマンド `lake build DkMath.FLT.Seven.SevenRamifiedFusionModSixResidues` で単一ターゲットを検証する。全リポジトリ build にはしない。


## 最終結果

- Outcome A。production focused build 終了コード0（9011 jobs は import 依存鎖を含む）。
- 最終 DkMathTest module 終了コード0。一般適用、ゼロ端点、(2,3)、反例(2,2)、逆向きの反例(5,5)すべて検証済み。
- 二 exports の公理はともに `[propext, Classical.choice, Quot.sound]`。`sorryAx` なし。
- 禁止構文検索ヒットなし。`git diff --check` 終了コード0。
- 再実行用のコマンド、全文ログ、正確なファイル一覧は report-001 を参照。
- 未実装: allocation への divisor-aware mod 6 bridge と mod 42、除外 consumer。gate 002 に進まず終了。
