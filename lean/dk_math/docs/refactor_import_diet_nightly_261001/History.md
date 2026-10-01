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

### 日時: 2026/10/01 JST — import diet 実装スライス

1. 方針:
   `Mathlib` の一括置換は行わず、各ファイルの実際の定義・定理・tactic 使用を確認して direct import に置き換えた。公開されていた名前は維持し、transitive import に依存していた利用側には direct import を追加した。
2. 実施:
   - `DkMath/Basic.lean`: `Mathlib.Data.Nat.Choose.Basic` に縮小。
   - `DkMath/Collatz/Basic.lean`: `Mathlib.Data.Nat.Basic` に縮小。
   - `DkMath/NumberTheory/PrimitiveSet/Basic.lean`: `Mathlib.Data.Finset.Basic` と `Mathlib.Tactic.NormNum` に縮小。
   - `DkMath/NumberTheory/PowerSums/Basic.lean`: 有限和、Fin ベクトル記法、`norm_num` の direct import に縮小。
   - `DkMath/CellDim.lean`, `DkMath/Algebra/BinomTail.lean`, `DkMath/Lib/Cosmic/GTail*.lean`, `DkMath/Lib/NumberTheory/PadicValNat.lean`: 下層 API と必要 tactic だけに縮小。
   - `DkMath/CosmicFormula/RealCore.lean` を追加し、`CosmicFormulaDim.GReal` を解析・体積モジュールから分離。`DkMath.FLT.Core` は `CosmicFormulaDim` 全体を取り込まなくなった。
   - `DkMath/CosmicFormula/Defs.lean` の未使用 `CellDim` import を削除し、`CosmicFormulaBinom` の import を real algebra kernel に変更。
   - import の縮小で露出した利用側 (`ABC.Rad`, `TraceOneQuadratic`, `PrimeProviderCore`, `EisensteinCoordinates`) に direct import を追加。
3. 検証:
   - `lake build DkMath.Basic DkMath.Collatz.Basic DkMath.NumberTheory.PrimitiveSet.Basic DkMath.NumberTheory.PowerSums.Basic` 成功（980 jobs）。
   - `lake build DkMath.FLT.Core` 成功（3625 jobs）。
   - `lake build DkMath.Lib.NumberTheory.EisensteinCoordinates DkMath.FLT.Core` 成功（3627 jobs）。
   - `git diff --check` 成功。
4. 依存規模:
   `DkMath.FLT.Core` の focused build は、変更前の 8939 jobs から 3625 jobs へ減少した。
5. 未完了:
   `lake build DkMath` は 10334 jobs 中 9532 jobs まで進んだが、`GNThreeOrientation`、`FLT.Seven.AxisDivisibility`、`Legendre.CenteredPacketDiamond` など既存の数学的未解決箇所に到達したため、このスライスでは全体成功に至っていない。全体 build の最終再実行は `EisensteinCoordinates` の direct import 修正後に未実施。
6. 備考:
   commit、push、nightly への変更は行っていない。残る `import Mathlib` は別サブシステムの段階的監査対象として扱う。

### 日時: 2026/10/01 JST — 全体ビルド修正完了

1. 追加修正:
   - import 縮小で自動解決されなくなった `Odd`、`Nat.Coprime`、有限算術の具体的証人を、対象の Legendre/Recharge 補題に明示した。
   - `ParitySafeRechargeDepthFiberExcess` では `Odd 11` の証人と具体的な seat/coprimality 計算を補った。
2. 検証:
   - `lake build DkMath.NumberTheory.Legendre.ParitySafeRechargeDepthFiberExcess` 成功（1432 jobs）。
   - `lake build` 全体成功。
   - `git diff --check` 成功。
3. 結論:
   import diet の今回の実装スライスについて、全体ビルドを通過する状態になった。commit、push、nightly への変更は行っていない。
