# findings-006 — exact centered-image exclusion at 589

## Source and scope

instruction-006 / review-005 と実際の centered polynomial、strict monotonicity、adjacent bracket no-image、centered/exact iff、sixth-power sieved receiver fields を確認。開始時変更なし。今回の対象は M=589 のみ、literal sixth-power 仮定なし。

既存対象名 / numeral を DkMath / DkMathTest で検索し、対応する 589 exclusion の重複宣言は見つからない。新規 source-coupling audit は行わない。

## Two trust levels

1. Python arbitrary-precision precheck: strict integer comparisons の再計算。Lean proof ではない。
2. Lean: actual `centeredSevenSextic` の定義をカーネル還元し、両 strict inequalities と既存 adjacent-image theorem による no-image を検証する。

D=7^27、T=448*589^49、k=52382010648825907313680。全 divisor の sieve exclusion は membership / coarse bound で r=1 を導き、この exact exclusion に運ぶ。

## Precheck and first calibration

Python precheck exit 0: D matches、両 strict inequalities は true。正の差の十進桁数は下側117 / 上側116。これは Python arithmetic の結果であり Lean proof としない。

初回 Lean calibration exit 1: bracket と no-image は通ったが、receiver transport の `64*(7*s^49)` を `448*s^49` へ移す simp の結合方向が不足。`←mul_assoc` と `64*7=448` の kernel-checked constant equality を明示する。数学的 target の反例ではない。

## Calibration success

修正した calibration exit 0。五つの API がすべて追加仮定なしで通った。重複する校正コードは production に移し、最終 DkMathTest に両不等式・各 export の適用・cheap survival と exact exclusion の同時成立・公理監査を残す。

## Final verification

- Outcome A: focused build exit 0 (9093 jobs)、final test exit 0、warning/error なし。
- bracket、no-image、pointwise exact exclusion、full-sieve exclusion、conditional source consequence を確認。
- cheap survival と exact exclusion の同時成立を既存 589 test の再利用で確認。
- bracket の公理は propext のみ、他四定理は標準三公理。sorryAx なし。
- Python precheck / Lean acceptance を report / evidence で明確に区別。既存 files は変更なし、logs は ignored、staging empty。
