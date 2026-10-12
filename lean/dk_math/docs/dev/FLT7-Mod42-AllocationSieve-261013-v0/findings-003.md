# findings-003 — independent allocation prefilter

## Source audit (2026-10-13)

- 開始時ブランチ `research/FLT7-Mod42-AllocationSieve-261013-v0`、変更なし。instruction-003 / review-002 / evidence policy を確認。
- 今回は実装・検証・報告のみ。Git の add / commit / push や integration は行わない。
- gate-002 の mod-42 必要条件は `r ∣ M` を保持している。
- `SixthPowerSievedNestedCondition` は divisor membership、coprimality、coarse bound、mod 7、sixth-power sieve、exact receiver を含む。単なるこの predicate の再包装を避ける。
- 既存 `internalDepthFourReconstruction_iff_sixth_power_sieved` は追加仮定なしの thin consumer を可能にする。
- DepthFourReconstructionAudit は finite chart equivalence / conditional route を述べ、chart の存在を主張しない。
- production で cheap allocation / prefilter を検索。既存 branch selector はあるが、今回の endpoint-free arithmetic predicate に相当する定義は見つからない。

## Approach

指示書の endpoint-free な二定義を用い、sixth-power sieve は含めない。exact predicate からは既存 mod-42 transport と既存 threshold fields を取り出すのみ。

DkMathTest で 554 が旧 necessary-only guards と modulus-one sixth-power sieve を通り、新 filter に落ちることを検査する。589 は新 filter を通る候補として調べるが、endpoint witness とは解釈しない。

## Calibration and duplicate audit

- Source index 再構築は終了コード0、1,804 files / 29,261 declarations。`search --name CheapAllocation --limit 20` は0件。Mathlib の allocation-sieve / cheap-allocation 対象名検索もヒットなし。
- DkMathTest calibration は初回で終了コード0。二定義・二含意と 554 / 589 の実際の整数比較が Lean で通った。
- 校正では literal `1^343` の自動評価 threshold（256）に関する warning が出たが、証明は受理された。最終テストでは `exponentiation.threshold 400` を設定し、この literal の正規化 warning を解消する。未検証仮定は追加しない。
- 最終 production は二定義と二 theorem のみ。calibration の重複証明は production に移し、具体的比較と一般適用を最終 DkMathTest に残す。
- 554 の例は fixed divisor `r=1` での strict screening の証拠。`HasModFortyTwoCheapAllocation 554` 全体の否定や exact condition の存在を意味しない。


## Final results

- Outcome A: focused production build / final tests both exit 0. Final test output has no warning/error.
- Fixed-allocation decidability and general new-numeric-to-old-numeric implication are checked in Lean.
- Both new production theorem exports and three named candidate test theorems have only `[propext, Classical.choice, Quot.sound]`; no `sorryAx`.
- 554 rejects a candidate surviving former necessary-only guards; 589 passes. No receiver witness is inferred.
- Existing files unchanged. Compact evidence is provenance-labeled; raw logs remain ignored. No gate 004 / Git mutation.

- 付帯の文字列による定義監査は初回に import 名 `SevenRamifiedFusionSixthPowerAllocationSieve` まで含めて false positive を出した。検査対象を二つの定義本文に絞り修正し、終了コード0。Lean 証明の失敗や定義内の依存ではない。
- 最終 whitespace / source SHA-256 / 定義本文監査は終了コード0。禁止構文なし、staging なし、logs は ignored。
