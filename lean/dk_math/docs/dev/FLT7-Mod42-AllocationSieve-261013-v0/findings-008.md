# findings-008 — divisor-dependent mod-five image

instruction-008 と actual centered polynomial / exact centered equivalence / gate007 / cheap allocation / sixth-power / perfect-sixth obstruction を確認。開始時変更なし。

Target は全自然数 r,s に対し 5∤r、s≡r² mod5 の fixed-chosen-divisor no-image と exact receiver transport。divisor membership はこの scalar transport に不要だが、具体例の cheap condition では保持する。

Source search で対応する一般 gap / square-mod-five 宣言は見つからない。Python 表は候補データであり Lean proof ではない。actual definition を ZMod5 に cast し、hs で s を r² に書き換え、任意の r,q を剰余へ還元する。

## Calibration

初回 DkMathTest calibration exit0。hs を cast した後、r,q の5剰余へ還元し全25ケースを調べた。r=0 residue は hr5 で除外、残る20ケースの scalar equality が矛盾する。公表 API の hypotheses は要求通り、追加 positivity / divisor guard は不要。scalar equality は chosen r を含むまま保持している。

## Final checked table

| r mod5 | D mod5 | image | allowed s |
| --- | --- | --- | --- |
| 0 | 0 | {0,2,3} | {0,1,4} |
| 1 | 3 | {1,2,4} | {2,3,4} |
| 2 | 1 | {1,3,4} | {1,2,3} |
| 3 | 4 | {1,3,4} | {1,2,3} |
| 4 | 2 | {1,2,4} | {2,3,4} |

Image / allowed-s finite tables are Lean checked; allowed means modular matching, not exact natural image. General proof reduces arbitrary r,q to residues, with s eliminated by the given congruence.

## Final outcome

Outcome A。focused build exit0 (9088 jobs)、both test runs exit0、final output warning/errorなし。Two production exports and regression have standard three axioms only, no sorryAx.

r=2,t=13,M=9653618 passes cheap and SixthPowerAllocationSieve, but fails both exact receivers. The previous sufficient perfect-sixth size premise36≤13 is false; no converse inferred. Unit-premise deletion has a checked zero-gap countermodel.

No all-divisor or full-sieve exclusion inferred. Existing files unchanged, no Git mutation. Stale index was refreshed (1,809 files / 29,283 declarations). Next single question is remaining eligible divisors at this same core, not global FLT7 closure.
