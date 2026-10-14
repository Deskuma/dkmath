# findings-009 — complete allocation exclusion at 9653618

instruction-009 と actual full-sieve fields、mod42 exclusion の divisor guard、same-r mod5 consumer を確認。開始時変更なし。対象名の実ソース検索で既存同名結果なし。

membership と size から r<5 を導き、3/4 の divisibility failure を排除して r=1∨r=2 にする。full-sieve の同じ witness r を保持し、r1 は mod42、r2 は mod5 で両 branch を排除する。production に DkMathTest import を追加しない。

Index refresh exit0: 1,809 files / 29,283 declarations。初回 calibration exit1: norm_num を hypothesis と goal に同時適用し、3/4 の contradiction branch を閉じた後に「No goals to be solved」。hypothesis の正規化後、残る goals だけ simp に渡す最小修正を行った。数学的反例や仮定変更ではない。

## Final results

Outcome A: corrected production focused build exit0 (9093 jobs); final test exit0, no warning/error. All three exports have standard three axioms, no sorryAx.

Membership + size gives r=1∨r=2 without hidden conditions. The same selected r is excluded using mod42 at1 / mod5 at2. Full-sieve is false, while the cheap existential is true by the existing r2 regression. Conditional source corollary uses existing iff only.

Existing files unchanged. No production-to-test import. No gate010 or Git mutation. Compact evidence is Codex-reported.
