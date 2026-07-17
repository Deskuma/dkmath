# Canonical Absorption-Deficit Audit (cp-343)

Odd roots: `1..16383`. Block limit: `4096`.
This is finite computational evidence, not a Lean theorem.

## Summary

- roots audited: 8192
- roots reaching a state-one canonical endpoint: 8192
- roots with a positive observed queue maximum: 6709
- largest observed queue/deficit: 8
- every positive queue state passed its active-window deficit identity
- the CSV stores the final maximum witness for each root
- no uniform bound or eventual discharge follows from this table

## Maximum-Deficit Windows

| root | queue | terminal | start | blocks | length | holes | valuation | deficit |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| 4255 | 8 | 8 | 6 | 3 | 18 | 7 | 3 | 8 |
| 4591 | 8 | 6 | 0 | 7 | 27 | 12 | 7 | 8 |
| 5673 | 8 | 9 | 7 | 3 | 18 | 7 | 3 | 8 |
| 6121 | 8 | 7 | 1 | 7 | 27 | 12 | 7 | 8 |
| 6383 | 8 | 8 | 6 | 3 | 18 | 7 | 3 | 8 |
| 6471 | 8 | 4 | 2 | 3 | 18 | 7 | 3 | 8 |
| 6887 | 8 | 6 | 0 | 7 | 26 | 11 | 7 | 8 |
| 8161 | 8 | 8 | 2 | 7 | 27 | 12 | 7 | 8 |
| 8191 | 8 | 2 | 0 | 3 | 18 | 7 | 3 | 8 |
| 8511 | 8 | 8 | 6 | 3 | 18 | 7 | 3 | 8 |
| 9575 | 8 | 8 | 6 | 3 | 18 | 7 | 3 | 8 |
| 9663 | 8 | 3 | 0 | 4 | 23 | 10 | 5 | 8 |
| 9707 | 8 | 4 | 2 | 3 | 18 | 7 | 3 | 8 |
| 10881 | 8 | 9 | 3 | 7 | 27 | 12 | 7 | 8 |
| 10921 | 8 | 3 | 1 | 3 | 18 | 7 | 3 | 8 |
| 11347 | 8 | 9 | 7 | 3 | 18 | 7 | 3 | 8 |
| 12243 | 8 | 7 | 1 | 7 | 26 | 11 | 7 | 8 |
| 12591 | 8 | 14 | 12 | 3 | 18 | 7 | 3 | 8 |
| 12767 | 8 | 8 | 6 | 3 | 18 | 7 | 3 | 8 |
| 12943 | 8 | 3 | 1 | 3 | 18 | 7 | 3 | 8 |
