# Collatz Orbit Pressure Remainder Scan

- rows: `500`
- rows with pressure witness: `237`
- rows with L5 remainder: `18`
- max pressure depth count: `6`
- max L5 remainder: `3`

## Top Pressure Samples

| n | sumS | pressure count | first depth | cont mass | ret mass | L1 | L2 | L3 | L4 | L5 |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 511 | 129 | 6 | 2 | 8 | 10 | 7 | 5 | 4 | 3 | 2 |
| 681 | 129 | 6 | 2 | 8 | 10 | 8 | 6 | 5 | 4 | 3 |
| 795 | 123 | 5 | 2 | 14 | 20 | 14 | 10 | 7 | 5 | 3 |
| 895 | 124 | 5 | 2 | 14 | 19 | 13 | 9 | 6 | 4 | 2 |
| 671 | 124 | 5 | 2 | 13 | 18 | 12 | 7 | 4 | 3 | 2 |
| 807 | 128 | 5 | 2 | 8 | 12 | 7 | 5 | 4 | 3 | 2 |
| 767 | 130 | 5 | 2 | 7 | 9 | 6 | 4 | 3 | 2 | 1 |
| 255 | 130 | 5 | 2 | 6 | 8 | 5 | 4 | 3 | 2 | 1 |
| 639 | 118 | 4 | 2 | 17 | 27 | 16 | 8 | 4 | 2 | 0 |
| 447 | 123 | 4 | 2 | 14 | 19 | 13 | 8 | 5 | 3 | 2 |
| 711 | 129 | 4 | 2 | 6 | 9 | 5 | 4 | 3 | 2 | 1 |
| 127 | 129 | 4 | 2 | 5 | 7 | 4 | 3 | 2 | 1 | 0 |

## Reading

`pressure_depth_count > 0` marks at least one local source continuation
pressure witness.  The Lean checkpoint 121 bridge turns the depth-two
one-range version into a positive mass plus delayed-budget pair.

The L1..L5 columns record the shifted-tail all-ones delayed remainders.
They should be read as possible retained mass, not as independent
budget entries.
