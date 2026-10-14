# findings-002 — divisor-aware mod-42 allocation filter

## 開始時の監査（2026-10-13）

- ブランチは `research/FLT7-Mod42-AllocationSieve-261013-v0`、開始時変更なし。
- instruction-002 / review-001 / README / ROADMAP / evidence policy を確認。対象は gate 002 の必要条件と exclusion consumer のみ。
- 既存 mod-6 の二定理、mod-7 `nestedAllocation_residue_sieve`、両 receiver の実際の型を確認。既存 production 定理の改変は不要。
- DkMath 全体で mod-6 / mod-42 の対象名と形を検索。新しい allocation 結論と power helper に相当する宣言は見つからない。
- Mathlib の `Nat.modEq_and_modEq_iff_modEq_mul` は coprime moduli の合同式を積の合同式へ合成する。既存 CRT を再利用する。
- GN receiver の `Nat.Coprime u (7*M)` は `r ∣ M` を含まない。`of_dvd_right`、冪、積の coprimality により missing provenance を補う。
- RHS は `Nat.coprime_sub_self_right huD.le` を再利用する。
- `s^49 ≡ s (mod 6)` は全自然数を含む必要があるため、unit-only Euler lemma では不十分。mod 6 の6剰余で kernel reduction する小さな helper を試す。

## 実装方針

production 公開 API は要求された三定理のみ。power reduction と `7*s^49` からの回収は private helper とする。DkMathTest に一般適用、CRT/power の具体例、unguarded coprimality transport の反例、必要条件の非十分性を記録する。

## Calibration 結果

実際の Nat.Coprime / ModEq API 型を `#check` で確認（終了コード0）。DkMathTest に配置した校正コードは初回で終了コード0。三定理は要求の型のまま通り、追加 positivity 仮定は不要だった。二つの private helper と三 exports を production に移し、校正の重複証明は除去する。

GN では `7 ∣ 7*M`、`r ∣ M ∣ 7*M` に `of_dvd_right` を適用。冪と積を取って `Nat.Coprime u (7^27*r^49)`、対称化して gate-001 に渡す。RHS は `u≤D` で自然数の `D-u` への coprimality を運ぶ。


## 最終検証

- production focused build 終了コード0、test module 終了コード0。追加 positivity 仮定不要、Outcome A。
- 三 exports の実公理出力はすべて `[propext, Classical.choice, Quot.sound]`。`sorryAx` なし。
- ガードなし coprimality transport の反例と、mod-42 の非十分性の具体例を Lean で確認。
- `M=8,r=1` を新 consumer で排除、`M=1,r=1` は合同式を通るが既存 bounds で receiver が成立しない。
- 失敗試行なし。コマンドと終了コードは report-002、小さい検証証拠は evidence/002-verification-summary.md。
- logs は Git-ignore 対象。README / ROADMAP は gate-002 実装完了・レビュー待ちのみ注記する。
- gate 003 の wrapper / reconstruction integration は未実装。

- 全7ファイルの staged whitespace audit（`git diff --cached --check`）終了コード0。ステージ対象に logs なし。通常の Git 書込みは read-only 制限に当たったが、許可された Git 実行で解消した。
