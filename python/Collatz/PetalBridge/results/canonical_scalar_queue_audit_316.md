# Canonical Scalar Queue Audit (cp-316)

Odd roots: `1..16383`. Block limit: `4096`.
This is finite computational evidence, not a Lean theorem.

## Summary

- roots audited: 8192
- roots reaching a state-one canonical endpoint: 8192
- roots with nonzero queue there: 0
- largest observed queue: 8
- no uniform bound or uniform repayment lag follows from this table

## Queue Records

| root | max queue | block | length | claims | capacity | drift | height | depths |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| 4255 | 8 | 8 | 4 | 2 | 1 | 1 | 2 | d1:1;d3:1 |
| 4591 | 8 | 6 | 5 | 2 | 1 | 1 | 2 | d2:1;d4:1 |
| 5673 | 8 | 9 | 4 | 2 | 1 | 1 | 2 | d1:1;d3:1 |
| 6121 | 8 | 7 | 5 | 2 | 1 | 1 | 2 | d2:1;d4:1 |
| 6383 | 8 | 8 | 4 | 2 | 1 | 1 | 2 | d1:1;d3:1 |
| 6471 | 8 | 4 | 4 | 2 | 1 | 1 | 2 | d1:1;d3:1 |
| 6887 | 8 | 6 | 5 | 2 | 1 | 1 | 2 | d2:1;d4:1 |
| 8161 | 8 | 8 | 5 | 2 | 1 | 1 | 2 | d2:1;d4:1 |
| 8191 | 8 | 2 | 4 | 2 | 1 | 1 | 2 | d1:1;d3:1 |
| 8511 | 8 | 8 | 4 | 2 | 1 | 1 | 2 | d1:1;d3:1 |
| 9575 | 8 | 8 | 4 | 2 | 1 | 1 | 2 | d1:1;d3:1 |
| 9663 | 8 | 3 | 7 | 4 | 2 | 2 | 3 | d2:1;d3:1;d5:1;d7:1 |
| 9707 | 8 | 4 | 4 | 2 | 1 | 1 | 2 | d1:1;d3:1 |
| 10881 | 8 | 9 | 5 | 2 | 1 | 1 | 2 | d2:1;d4:1 |
| 10921 | 8 | 3 | 4 | 2 | 1 | 1 | 2 | d1:1;d3:1 |
| 11347 | 8 | 9 | 4 | 2 | 1 | 1 | 2 | d1:1;d3:1 |
| 12243 | 8 | 7 | 5 | 2 | 1 | 1 | 2 | d2:1;d4:1 |
| 12591 | 8 | 14 | 4 | 2 | 1 | 1 | 2 | d1:1;d3:1 |
| 12767 | 8 | 8 | 4 | 2 | 1 | 1 | 2 | d1:1;d3:1 |
| 12943 | 8 | 3 | 4 | 2 | 1 | 1 | 2 | d1:1;d3:1 |

## Positive-Excursion Records

| root | longest positive blocks | first return block | max queue | queue at one |
| --- | --- | --- | --- | --- |
| 7527 | 20 | 20 | 5 | 0 |
| 15055 | 20 | 20 | 4 | 0 |
| 7963 | 19 | 19 | 4 | 0 |
| 10617 | 19 | 20 | 4 | 0 |
| 11291 | 19 | 20 | 4 | 0 |
| 12703 | 19 | 19 | 4 | 0 |
| 14695 | 18 | 18 | 5 | 0 |
| 703 | 17 | 17 | 6 | 0 |
| 937 | 17 | 18 | 6 | 0 |
| 1055 | 17 | 17 | 5 | 0 |
| 1249 | 17 | 19 | 6 | 0 |
| 1583 | 17 | 17 | 5 | 0 |
| 1665 | 17 | 20 | 6 | 0 |
| 1875 | 17 | 18 | 5 | 0 |
| 2463 | 17 | 2 | 6 | 0 |
| 2499 | 17 | 18 | 6 | 0 |
| 2631 | 17 | 1 | 6 | 0 |
| 2813 | 17 | 18 | 5 | 0 |
| 2919 | 17 | 3 | 6 | 0 |
| 3331 | 17 | 19 | 6 | 0 |
