# Collatz Selected Depth Overlap Scan

- rows: `500`
- rows with at least two selected depths: `52`
- rows with a disjoint selected-depth pair: `0`
- rows where every selected-depth pair overlaps: `52`
- rows whose selected depths are a prefix from `r_start`: `500`
- nonempty prefix rows: `237` / `237`
- rows whose selected depths are consecutive: `500`
- nonempty consecutive rows: `237` / `237`
- max selected depth count: `6`
- max selected depth: `7`
- max pairwise overlap: `13`

## Top Multi-Witness Samples

| n | selected depths | prefix | consecutive | missing | pairs | disjoint pairs | max overlap | first pair | first overlap | masses |
|---:|---|---|---|---|---:|---:|---:|---|---:|---|
| 511 | 2;3;4;5;6;7 | True | True |  | 15 | 0 | 6 | 2:3 | 6 | 8:6 |
| 681 | 2;3;4;5;6;7 | True | True |  | 15 | 0 | 6 | 2:3 | 6 | 8:6 |
| 255 | 2;3;4;5;6 | True | True |  | 10 | 0 | 5 | 2:3 | 5 | 6:5 |
| 671 | 2;3;4;5;6 | True | True |  | 10 | 0 | 8 | 2:3 | 8 | 13:8 |
| 767 | 2;3;4;5;6 | True | True |  | 10 | 0 | 5 | 2:3 | 5 | 7:5 |
| 795 | 2;3;4;5;6 | True | True |  | 10 | 0 | 10 | 2:3 | 10 | 14:10 |
| 807 | 2;3;4;5;6 | True | True |  | 10 | 0 | 5 | 2:3 | 5 | 8:5 |
| 895 | 2;3;4;5;6 | True | True |  | 10 | 0 | 10 | 2:3 | 10 | 14:10 |
| 127 | 2;3;4;5 | True | True |  | 6 | 0 | 4 | 2:3 | 4 | 5:4 |
| 169 | 2;3;4;5 | True | True |  | 6 | 0 | 4 | 2:3 | 4 | 5:4 |
| 225 | 2;3;4;5 | True | True |  | 6 | 0 | 4 | 2:3 | 4 | 5:4 |
| 383 | 2;3;4;5 | True | True |  | 6 | 0 | 4 | 2:3 | 4 | 5:4 |

## Reading

A disjoint pair means two selected continuation index sets are disjoint
in this finite orbit window.  This is only experimental evidence.

If disjoint pairs are common, a future Lean predicate could target
`DisjointTowerTargets`.  If all selected pairs overlap, the right
formal condition may need to express nested selected-depth behavior.

The prefix/consecutive fields test the next hypothesis: selected
depths may form a visible initial tower segment.  A prefix row means
`r_start, r_start+1, ..., max_selected_depth` are all selected.
