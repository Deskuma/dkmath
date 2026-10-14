# findings-010 — parametric mixed exclusion

instruction-010 と gate009 の実際の finite-divisor / full-sieve proof、mod42 divisor guard、same-r mod5 transport を確認。開始時変更なし。対象名 / progression の実ソース検索で重複結果なし。

s≡1 mod42 を2/3へ縮小し、oddness / nondivisibilityから3∤2s、4∤2sを得る。membership + coarse bound + strict upper boundで r<5、残るr1/r2を既存二consumerで排除する。追加source仮定やexact receiver emptinessを仮定しない。

## Calibration result

Initial calibration exit0。提案三仮定は十分、追加仮定不要。3∤2s は mod3 residue、4∤2s は oddness と 4倍の仮定から s=2k の矛盾。r<5 の導出では strict upper bound を保持する。production は新二定理のみ、既存排除consumerを再利用する。

## Final validation

Outcome A。focused build exit0 (9091jobs)、final test exit0、warning/errorなし。両exportsは標準三公理のみ、sorryAxなし。

指定size criterionは全kについてk≤63799と同値。63800distinct coresのcardinalityも既存Finset lemmaで確認。k22982はgate009の9653618に一致。k63800でcriterionが偽であることも確認したが、それをexact receiverの存在と解釈しない。

全kのcheap passageを主張せず、既存例一つだけ比較。Source assumptionなし。Existing files unchanged、logs ignored、Git mutationなし。Bound緩和と残るdivisor coverを次の一問として記録、未実装。
