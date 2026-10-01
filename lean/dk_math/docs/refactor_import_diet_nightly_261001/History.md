# History of refactor/import-diet-nightly-261001

## Log

### 日時: 2026/10/01 JST

1. 目的:
   `nightly` HEAD から import の依存を見直す専用ブランチを作り、Mathlib umbrella import の削減を段階的に始める。
2. 実施:
   - 起点: `nightly` at `bbcf20bd1fcec87198e410b901de6b7e865a3be5`
   - `DkMath/Polyomino.lean`: `import Mathlib` を Finset union と有限和の直接 import に置き換えた。
   - `DkMath/Lib/Basic.lean`: 空の namespace だけを含むため、未使用の `import Mathlib` を削除した。
3. 結論:
   小さな下層モジュールから、必要 API を保ったまま依存を絞る方針で開始した。Polyomino の変更は、作業開始前に利用者の nightly 作業ツリーで単体ビルドが通った変更を再現したもの。
4. 検証:
   この作業環境にはリポジトリのローカル clone と Lean toolchain がなく、ここから単体ビルド・全体ビルドは実行していない。ブランチ上での再ビルドと full build が必要。ビルド I/O、時間、最大 RSS の前後比較も未計測。
5. 失敗事例:
   なし。
6. 備考:
   `nightly` への変更は行っていない。全体一括置換はせず、依存の深さと利用 API を確認してから段階的に扱う。
7. 次の課題:
   依存の深い `Basic` / `Defs` / `Core` / `Lib` を優先して import 使用箇所を監査し、狭い import への置換をローカル Lean build で検証する。特に `DkMath.Basic`, `DkMath.Collatz.Basic`, `DkMath.NumberTheory.PrimitiveSet.Basic`, `DkMath.NumberTheory.PowerSums.Basic` を確認する。
