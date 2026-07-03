# Collatz Pressure Sign Pattern Scan

- rows: `8192`
- rows with positive pressure depths: `4421`
- rows with local islands: `252`
- rows with sign-change-up positions: `404`
- positive block definition: `maximal consecutive positive-depth run, length >= 1`
- rows with positive blocks length >= 1: `4421`
- rows with positive blocks length >= 2: `1455`
- rows with positive blocks length >= 4: `623`
- max positive depth count: `11`
- max local island count: `1`
- max sign-change-up count: `1`
- largest margin jump: `12`
- largest retention drop: `20`
- largest continuation drop: `13`
- largest retention drop minus 2 continuation drop: `10`
- rows_with_margin_step_identity_failure: `0`
- rows_with_net_drop_positive: `8089`
- rows_with_margin_jump: `8089`
- rows_with_margin_jump_iff_net_drop_failure: `0`
- positive block length counts: `1:2966; 2:570; 3:262; 4:322; 5:143; 6:67; 7:26; 8:42; 9:3; 10:19; 11:1`
- all-ones depth first counts: `1:4097; 2:2047; 3:1025; 4:511; 5:257; 6:127; 7:65; 8:31; 9:17; 10:7; 11:5; 12:1; 13:2`
- all-ones depth mode counts: `1:8192`
- all-ones depth max counts: `1:147; 2:782; 3:1692; 4:1004; 5:580; 6:3099; 7:462; 8:275; 9:65; 10:25; 11:40; 12:2; 13:19`
- sign-change cause counts: `retention_drop_dominant:404`

## Top Positive-Depth Samples

| n | positive depths | blocks | max block | all-ones max | frontier | frontier margin | islands | sign-up | margins |
|---:|---|---|---:|---:|---:|---:|---|---|---|
| 16383 | 2;3;4;5;6;7;8;9;10;11;12 | 2-12 | 11 | 13 | 2 | 12 |  |  | 2:12;3:13;4:10;5:8;6:7;7:5;8:5;9:4;10:3;11:2;12:1;13:0 |
| 5673 | 2;3;4;5;6;7;8;9;10;11 | 2-11 | 10 | 13 | 2 | 18 |  |  | 2:18;3:14;4:8;5:5;6:6;7:4;8:4;9:3;10:2;11:1;12:0;13:-1 |
| 4255 | 2;3;4;5;6;7;8;9;10;11 | 2-11 | 10 | 13 | 2 | 17 |  |  | 2:17;3:14;4:8;5:5;6:6;7:4;8:4;9:3;10:2;11:1;12:0;13:-1 |
| 8511 | 2;3;4;5;6;7;8;9;10;11 | 2-11 | 10 | 13 | 2 | 17 |  |  | 2:17;3:14;4:8;5:7;6:5;7:4;8:4;9:3;10:2;11:1;12:0;13:-1 |
| 6383 | 2;3;4;5;6;7;8;9;10;11 | 2-11 | 10 | 13 | 2 | 16 |  |  | 2:16;3:13;4:7;5:6;6:6;7:4;8:4;9:3;10:2;11:1;12:0;13:-1 |
| 11347 | 2;3;4;5;6;7;8;9;10;11 | 2-11 | 10 | 13 | 2 | 16 |  |  | 2:16;3:13;4:7;5:6;6:6;7:4;8:4;9:3;10:2;11:1;12:0;13:-1 |
| 12767 | 2;3;4;5;6;7;8;9;10;11 | 2-11 | 10 | 13 | 2 | 16 |  |  | 2:16;3:13;4:7;5:6;6:6;7:4;8:4;9:3;10:2;11:1;12:0;13:-1 |
| 9575 | 2;3;4;5;6;7;8;9;10;11 | 2-11 | 10 | 13 | 2 | 15 |  |  | 2:15;3:12;4:8;5:6;6:6;7:4;8:4;9:3;10:2;11:1;12:0;13:-1 |
| 12591 | 2;3;4;5;6;7;8;9;10;11 | 2-11 | 10 | 13 | 2 | 15 |  |  | 2:15;3:10;4:5;5:4;6:6;7:5;8:4;9:3;10:2;11:1;12:0;13:-1 |
| 13447 | 2;3;4;5;6;7;8;9;10;11 | 2-11 | 10 | 13 | 2 | 15 |  |  | 2:15;3:12;4:8;5:6;6:6;7:4;8:4;9:3;10:2;11:1;12:0;13:-1 |
| 15129 | 2;3;4;5;6;7;8;9;10;11 | 2-11 | 10 | 13 | 2 | 15 |  |  | 2:15;3:14;4:7;5:6;6:6;7:4;8:4;9:3;10:2;11:1;12:0;13:-1 |
| 16159 | 2;3;4;5;6;7;8;9;10;11 | 2-11 | 10 | 13 | 2 | 15 |  |  | 2:15;3:13;4:8;5:6;6:6;7:4;8:4;9:3;10:2;11:1;12:0;13:-1 |

## Deepest All-Ones Samples

| n | all-ones depths | max | counts ge4/ge5/ge6 | max block | positive blocks | residual mod 32 |
|---:|---|---:|---|---:|---|---|
| 16383 | 13;12;11;10;9;8;7;6;5;4;3;2;1;4;3;2;1;2;1;2;1;2;1;2;1;1;5;4;3;2;1;3;2;1;1;2;1;1;1;1;7;6;5;4;3;2;1;1;1;1;1;2;1;1;1;1;1;1;1;1;1;1;1;1 | 13 | 17/13/10 | 11 | 2-12 | 31;31;31;31;31;31;31;31;31;15;23;3;5;15;7;27;25;19;29;3;5;27;25;3;21;21;31;15;23;19;29;23;3;5;29;11;1;17;5;9;31;31;31;15;7;11;17;5;13;13;29;11;17;13;5;1;1;1;1;1;1;1;1;1 |
| 4255 | 4;3;2;1;5;4;3;2;1;1;1;1;4;3;2;1;13;12;11;10;9;8;7;6;5;4;3;2;1;1;4;3;2;1;2;1;2;1;2;1;2;1;1;5;4;3;2;1;3;2;1;1;2;1;1;1;1;7;6;5;4;3;2;1 | 13 | 21/14/10 | 10 | 2-11 | 15;7;27;9;31;15;7;11;17;13;1;9;15;23;3;5;31;31;31;31;31;31;31;31;31;15;7;11;1;9;15;7;27;25;19;29;3;5;27;25;3;21;21;31;15;23;19;29;23;3;5;29;11;1;17;5;9;31;31;31;15;7;11;17 |
| 5673 | 5;4;3;2;1;5;4;3;2;1;1;1;1;4;3;2;1;13;12;11;10;9;8;7;6;5;4;3;2;1;1;4;3;2;1;2;1;2;1;2;1;2;1;1;5;4;3;2;1;3;2;1;1;2;1;1;1;1;7;6;5;4;3;2 | 13 | 22/15/10 | 10 | 2-11 | 31;15;7;27;9;31;15;7;11;17;13;1;9;15;23;3;5;31;31;31;31;31;31;31;31;31;15;7;11;1;9;15;7;27;25;19;29;3;5;27;25;3;21;21;31;15;23;19;29;23;3;5;29;11;1;17;5;9;31;31;31;15;7;11 |
| 6383 | 3;2;1;5;4;3;2;1;1;1;1;4;3;2;1;13;12;11;10;9;8;7;6;5;4;3;2;1;1;4;3;2;1;2;1;2;1;2;1;2;1;1;5;4;3;2;1;3;2;1;1;2;1;1;1;1;7;6;5;4;3;2;1;1 | 13 | 20/14/10 | 10 | 2-11 | 7;27;9;31;15;7;11;17;13;1;9;15;23;3;5;31;31;31;31;31;31;31;31;31;15;7;11;1;9;15;7;27;25;19;29;3;5;27;25;3;21;21;31;15;23;19;29;23;3;5;29;11;1;17;5;9;31;31;31;15;7;11;17;5 |
| 6471 | 2;1;1;13;12;11;10;9;8;7;6;5;4;3;2;1;1;4;3;2;1;2;1;2;1;2;1;2;1;1;5;4;3;2;1;3;2;1;1;2;1;1;1;1;7;6;5;4;3;2;1;1;1;1;1;2;1;1;1;1;1;1;1;1 | 13 | 17/13/10 | 10 | 2-11 | 11;1;9;31;31;31;31;31;31;31;31;31;15;7;11;1;9;15;7;27;25;19;29;3;5;27;25;3;21;21;31;15;23;19;29;23;3;5;29;11;1;17;5;9;31;31;31;15;7;11;17;5;13;13;29;11;17;13;5;1;1;1;1;1 |
| 8511 | 5;4;3;2;1;4;3;2;1;1;1;1;4;3;2;1;13;12;11;10;9;8;7;6;5;4;3;2;1;1;4;3;2;1;2;1;2;1;2;1;2;1;1;5;4;3;2;1;3;2;1;1;2;1;1;1;1;7;6;5;4;3;2;1 | 13 | 21/14/10 | 10 | 2-11 | 31;15;23;19;29;15;7;11;17;13;1;9;15;23;3;5;31;31;31;31;31;31;31;31;31;15;7;11;1;9;15;7;27;25;19;29;3;5;27;25;3;21;21;31;15;23;19;29;23;3;5;29;11;1;17;5;9;31;31;31;15;7;11;17 |
| 9575 | 2;1;5;4;3;2;1;1;1;1;4;3;2;1;13;12;11;10;9;8;7;6;5;4;3;2;1;1;4;3;2;1;2;1;2;1;2;1;2;1;1;5;4;3;2;1;3;2;1;1;2;1;1;1;1;7;6;5;4;3;2;1;1;1 | 13 | 20/14/10 | 10 | 2-11 | 27;9;31;15;7;11;17;13;1;9;15;23;3;5;31;31;31;31;31;31;31;31;31;15;7;11;1;9;15;7;27;25;19;29;3;5;27;25;3;21;21;31;15;23;19;29;23;3;5;29;11;1;17;5;9;31;31;31;15;7;11;17;5;13 |
| 9707 | 1;1;13;12;11;10;9;8;7;6;5;4;3;2;1;1;4;3;2;1;2;1;2;1;2;1;2;1;1;5;4;3;2;1;3;2;1;1;2;1;1;1;1;7;6;5;4;3;2;1;1;1;1;1;2;1;1;1;1;1;1;1;1;1 | 13 | 17/13/10 | 10 | 2-11 | 1;9;31;31;31;31;31;31;31;31;31;15;7;11;1;9;15;7;27;25;19;29;3;5;27;25;3;21;21;31;15;23;19;29;23;3;5;29;11;1;17;5;9;31;31;31;15;7;11;17;5;13;13;29;11;17;13;5;1;1;1;1;1;1 |
| 10921 | 13;12;11;10;9;8;7;6;5;4;3;2;1;1;4;3;2;1;2;1;2;1;2;1;2;1;1;5;4;3;2;1;3;2;1;1;2;1;1;1;1;7;6;5;4;3;2;1;1;1;1;1;2;1;1;1;1;1;1;1;1;1;1;1 | 13 | 17/13/10 | 10 | 2-11 | 31;31;31;31;31;31;31;31;31;15;7;11;1;9;15;7;27;25;19;29;3;5;27;25;3;21;21;31;15;23;19;29;23;3;5;29;11;1;17;5;9;31;31;31;15;7;11;17;5;13;13;29;11;17;13;5;1;1;1;1;1;1;1;1 |
| 11347 | 1;4;3;2;1;5;4;3;2;1;1;1;1;4;3;2;1;13;12;11;10;9;8;7;6;5;4;3;2;1;1;4;3;2;1;2;1;2;1;2;1;2;1;1;5;4;3;2;1;3;2;1;1;2;1;1;1;1;7;6;5;4;3;2 | 13 | 21/14/10 | 10 | 2-11 | 29;15;7;27;9;31;15;7;11;17;13;1;9;15;23;3;5;31;31;31;31;31;31;31;31;31;15;7;11;1;9;15;7;27;25;19;29;3;5;27;25;3;21;21;31;15;23;19;29;23;3;5;29;11;1;17;5;9;31;31;31;15;7;11 |
| 12591 | 3;2;1;1;1;1;3;2;1;1;5;4;3;2;1;5;4;3;2;1;1;1;1;4;3;2;1;13;12;11;10;9;8;7;6;5;4;3;2;1;1;4;3;2;1;2;1;2;1;2;1;2;1;1;5;4;3;2;1;3;2;1;1;2 | 13 | 18/12/8 | 10 | 2-11 | 7;11;1;1;1;9;7;11;17;5;31;15;7;27;9;31;15;7;11;17;13;1;9;15;23;3;5;31;31;31;31;31;31;31;31;31;15;7;11;1;9;15;7;27;25;19;29;3;5;27;25;3;21;21;31;15;23;19;29;23;3;5;29;11 |
| 12767 | 4;3;2;1;4;3;2;1;1;1;1;4;3;2;1;13;12;11;10;9;8;7;6;5;4;3;2;1;1;4;3;2;1;2;1;2;1;2;1;2;1;1;5;4;3;2;1;3;2;1;1;2;1;1;1;1;7;6;5;4;3;2;1;1 | 13 | 20/13/10 | 10 | 2-11 | 15;23;19;29;15;7;11;17;13;1;9;15;23;3;5;31;31;31;31;31;31;31;31;31;15;7;11;1;9;15;7;27;25;19;29;3;5;27;25;3;21;21;31;15;23;19;29;23;3;5;29;11;1;17;5;9;31;31;31;15;7;11;17;5 |

## Local-Island Samples

| n | islands | first sign-change pair | sign-up | causes | height seq | first-failed seq | all-ones depths | residual mod 16 |
|---:|---|---|---|---|---|---|---|---|
| 1567 | 3 | 2->3 | 2 | retention_drop_dominant | 1;1;1;1;2;2;2;6;3;1;2;1;4;1;3;1;2;3;4;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2 | 2;2;2;2;3;3;3;7;4;2;3;2;5;2;4;2;3;4;5;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3 | 4;3;2;1;1;1;1;1;2;1;2;1;2;1;2;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1 | 15;7;11;1;1;1;5;13;11;9;3;5;3;13;11;1;13;5;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1 |
| 1639 | 5 | 4->5 | 4 | retention_drop_dominant | 1;1;2;1;1;1;3;1;1;1;2;4;1;1;1;1;1;1;2;1;1;2;5;2;1;1;7;2;1;4;1;3;1;2;3;4;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2 | 2;2;3;2;2;2;4;2;2;2;3;5;2;2;2;2;2;2;3;2;2;3;6;3;2;2;8;3;2;5;2;4;2;3;4;5;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3 | 2;1;4;3;2;1;4;3;2;1;1;7;6;5;4;3;2;1;3;2;1;1;1;3;2;1;1;2;1;2;1;2;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1 | 11;9;15;7;3;13;15;7;11;1;5;15;15;15;15;7;11;9;7;11;1;5;9;7;3;5;9;3;5;3;13;11;1;13;5;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1 |
| 1775 | 5 | 4->5 | 4 | retention_drop_dominant | 1;1;1;2;1;1;1;4;3;1;2;2;4;2;1;1;1;1;1;1;2;4;3;3;3;1;2;3;4;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2 | 2;2;2;3;2;2;2;5;4;2;3;3;5;3;2;2;2;2;2;2;3;5;4;4;4;2;3;4;5;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3 | 3;2;1;4;3;2;1;1;2;1;1;1;1;7;6;5;4;3;2;1;1;1;1;1;2;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1 | 7;11;9;15;7;3;5;13;11;1;1;5;9;15;15;15;15;7;11;1;5;13;13;13;11;1;13;5;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1 |
| 2079 | 3 | 2->3 | 2 | retention_drop_dominant | 1;1;1;1;2;2;1;5;2;2;7;1;2;3;4;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2 | 2;2;2;2;3;3;2;6;3;3;8;2;3;4;5;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3 | 4;3;2;1;1;2;1;1;1;1;2;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1 | 15;7;11;1;9;3;5;1;1;5;11;1;13;5;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1 |
| 2089 | 3 | 2->3 | 2 | retention_drop_dominant | 2;1;1;1;1;2;2;2;6;3;1;2;1;4;1;3;1;2;3;4;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2 | 3;2;2;2;2;3;3;3;7;4;2;3;2;5;2;4;2;3;4;5;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3 | 5;4;3;2;1;1;1;1;1;2;1;2;1;2;1;2;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1 | 15;15;7;11;1;1;1;5;13;11;9;3;5;3;13;11;1;13;5;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1 |
| 2103 | 5 | 4->5 | 4 | retention_drop_dominant | 1;1;3;1;1;1;2;1;1;1;4;3;1;2;2;4;2;1;1;1;1;1;1;2;4;3;3;3;1;2;3;4;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2 | 2;2;4;2;2;2;3;2;2;2;5;4;2;3;3;5;3;2;2;2;2;2;2;3;5;4;4;4;2;3;4;5;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3 | 2;1;4;3;2;1;4;3;2;1;1;2;1;1;1;1;7;6;5;4;3;2;1;1;1;1;1;2;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1 | 3;13;15;7;11;9;15;7;3;5;13;11;1;1;5;9;15;15;15;15;7;11;1;5;13;13;13;11;1;13;5;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1 |
| 2185 | 5 | 4->5 | 4 | retention_drop_dominant | 2;1;1;2;1;1;1;3;1;1;1;2;4;1;1;1;1;1;1;2;1;1;2;5;2;1;1;7;2;1;4;1;3;1;2;3;4;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2 | 3;2;2;3;2;2;2;4;2;2;2;3;5;2;2;2;2;2;2;3;2;2;3;6;3;2;2;8;3;2;5;2;4;2;3;4;5;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3 | 3;2;1;4;3;2;1;4;3;2;1;1;7;6;5;4;3;2;1;3;2;1;1;1;3;2;1;1;2;1;2;1;2;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1 | 7;11;9;15;7;3;13;15;7;11;1;5;15;15;15;15;7;11;9;7;11;1;5;9;7;3;5;9;3;5;3;13;11;1;13;5;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1 |
| 2431 | 4 | 3->4 | 3 | retention_drop_dominant | 1;1;1;1;1;1;5;4;1;1;2;1;1;3;1;1;3;1;2;6;1;1;1;1;2;2;1;2;1;1;2;1;1;1;2;3;1;1;2;1;2;1;1;1;1;1;3;1;1;1;4;2;2;4;3;1;1;5;4;2;2;2;2;2 | 2;2;2;2;2;2;6;5;2;2;3;2;2;4;2;2;4;2;3;7;2;2;2;2;3;3;2;3;2;2;3;2;2;2;3;4;2;2;3;2;3;2;2;2;2;2;4;2;2;2;5;3;3;5;4;2;2;6;5;3;3;3;3;3 | 6;5;4;3;2;1;1;3;2;1;3;2;1;3;2;1;2;1;1;5;4;3;2;1;1;2;1;3;2;1;4;3;2;1;1;3;2;1;2;1;6;5;4;3;2;1;4;3;2;1;1;1;1;1;3;2;1;1;1;1;1;1;1;1 | 15;15;15;7;3;5;5;7;11;9;7;3;13;7;3;13;11;1;5;15;15;7;11;1;9;11;9;7;11;9;15;7;11;1;13;7;11;9;11;9;15;15;15;7;3;13;15;7;3;5;1;1;5;13;7;3;5;5;1;1;1;1;1;1 |
| 2459 | 5 | 4->5 | 4 | retention_drop_dominant | 1;2;1;1;1;3;1;1;1;2;4;1;1;1;1;1;1;2;1;1;2;5;2;1;1;7;2;1;4;1;3;1;2;3;4;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2 | 2;3;2;2;2;4;2;2;2;3;5;2;2;2;2;2;2;3;2;2;3;6;3;2;2;8;3;2;5;2;4;2;3;4;5;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3 | 1;4;3;2;1;4;3;2;1;1;7;6;5;4;3;2;1;3;2;1;1;1;3;2;1;1;2;1;2;1;2;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1 | 9;15;7;3;13;15;7;11;1;5;15;15;15;15;7;11;9;7;11;1;5;9;7;3;5;9;3;5;3;13;11;1;13;5;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1 |
| 2475 | 3 | 2->3 | 2 | retention_drop_dominant | 1;2;2;2;1;1;1;1;2;2;2;6;3;1;2;1;4;1;3;1;2;3;4;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2 | 2;3;3;3;2;2;2;2;3;3;3;7;4;2;3;2;5;2;4;2;3;4;5;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3 | 1;1;1;5;4;3;2;1;1;1;1;1;2;1;2;1;2;1;2;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1 | 1;1;9;15;15;7;11;1;1;1;5;13;11;9;3;5;3;13;11;1;13;5;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1 |
| 2495 | 4 | 3->4 | 3 | retention_drop_dominant | 1;1;1;1;1;2;1;1;2;5;2;1;1;7;2;1;4;1;3;1;2;3;4;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2 | 2;2;2;2;2;3;2;2;3;6;3;2;2;8;3;2;5;2;4;2;3;4;5;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3 | 5;4;3;2;1;3;2;1;1;1;3;2;1;1;2;1;2;1;2;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1 | 15;15;7;11;9;7;11;1;5;9;7;3;5;9;3;5;3;13;11;1;13;5;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1 |
| 2655 | 3 | 2->3 | 2 | retention_drop_dominant | 1;1;1;1;4;2;1;6;4;2;1;3;1;2;3;4;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2 | 2;2;2;2;5;3;2;7;5;3;2;4;2;3;4;5;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3 | 4;3;2;1;1;2;1;1;1;2;1;2;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1 | 15;7;3;5;9;3;5;5;9;3;13;11;1;13;5;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1 |

## Sign-Change-Up Samples

| n | sign-up | causes | margin jump | retention drop | continuation drop | drop details | margins | retentions | continuations |
|---:|---|---|---:|---:|---:|---|---|---|---|
| 6247 | 4 | retention_drop_dominant | 11 | 15 | 13 | 4:ret=6,cont=2,diff=2,jump=2,cause=retention_drop_dominant | 2:10;3:-1;4:0;5:2;6:0;7:0;8:-1;9:0;10:0;11:0;12:0;13:0 | 2:40;3:25;4:12;5:6;6:4;7:2;8:1;9:0;10:0;11:0;12:0;13:0 | 2:25;3:12;4:6;5:4;6:2;7:1;8:0;9:0;10:0;11:0;12:0;13:0 |
| 12495 | 4 | retention_drop_dominant | 11 | 15 | 13 | 4:ret=6,cont=2,diff=2,jump=2,cause=retention_drop_dominant | 2:10;3:-1;4:0;5:2;6:0;7:0;8:-1;9:0;10:0;11:0;12:0;13:0 | 2:40;3:25;4:12;5:6;6:4;7:2;8:1;9:0;10:0;11:0;12:0;13:0 | 2:25;3:12;4:6;5:4;6:2;7:1;8:0;9:0;10:0;11:0;12:0;13:0 |
| 4935 | 4 | retention_drop_dominant | 10 | 16 | 13 | 4:ret=6,cont=2,diff=2,jump=2,cause=retention_drop_dominant | 2:9;3:-1;4:0;5:2;6:0;7:0;8:-1;9:0;10:0;11:0;12:0;13:0 | 2:41;3:25;4:12;5:6;6:4;7:2;8:1;9:0;10:0;11:0;12:0;13:0 | 2:25;3:12;4:6;5:4;6:2;7:1;8:0;9:0;10:0;11:0;12:0;13:0 |
| 9871 | 4 | retention_drop_dominant | 10 | 16 | 13 | 4:ret=7,cont=2,diff=3,jump=3,cause=retention_drop_dominant | 2:10;3:0;4:-1;5:2;6:0;7:0;8:-1;9:0;10:0;11:0;12:0;13:0 | 2:42;3:26;4:13;5:6;6:4;7:2;8:1;9:0;10:0;11:0;12:0;13:0 | 2:26;3:13;4:6;5:4;6:2;7:1;8:0;9:0;10:0;11:0;12:0;13:0 |
| 10235 | 2 | retention_drop_dominant | 10 | 14 | 2 | 2:ret=14,cont=2,diff=10,jump=10,cause=retention_drop_dominant | 2:-9;3:1;4:-1;5:-1;6:0;7:0;8:0;9:0;10:0;11:0;12:0;13:0 | 2:19;3:5;4:3;5:1;6:0;7:0;8:0;9:0;10:0;11:0;12:0;13:0 | 2:5;3:3;4:1;5:0;6:0;7:0;8:0;9:0;10:0;11:0;12:0;13:0 |
| 13161 | 4 | retention_drop_dominant | 10 | 16 | 13 | 4:ret=7,cont=2,diff=3,jump=3,cause=retention_drop_dominant | 2:10;3:0;4:-1;5:2;6:0;7:0;8:-1;9:0;10:0;11:0;12:0;13:0 | 2:42;3:26;4:13;5:6;6:4;7:2;8:1;9:0;10:0;11:0;12:0;13:0 | 2:26;3:13;4:6;5:4;6:2;7:1;8:0;9:0;10:0;11:0;12:0;13:0 |
| 14807 | 4 | retention_drop_dominant | 10 | 16 | 13 | 4:ret=6,cont=2,diff=2,jump=2,cause=retention_drop_dominant | 2:9;3:-1;4:0;5:2;6:0;7:0;8:-1;9:0;10:0;11:0;12:0;13:0 | 2:41;3:25;4:12;5:6;6:4;7:2;8:1;9:0;10:0;11:0;12:0;13:0 | 2:25;3:12;4:6;5:4;6:2;7:1;8:0;9:0;10:0;11:0;12:0;13:0 |
| 4551 | 3 | retention_drop_dominant | 9 | 15 | 12 | 3:ret=12,cont=5,diff=2,jump=2,cause=retention_drop_dominant | 2:8;3:-1;4:1;5:0;6:-1;7:-1;8:0;9:0;10:0;11:0;12:0;13:0 | 2:38;3:23;4:11;5:6;6:3;7:1;8:0;9:0;10:0;11:0;12:0;13:0 | 2:23;3:11;4:6;5:3;6:1;7:0;8:0;9:0;10:0;11:0;12:0;13:0 |
| 8329 | 4 | retention_drop_dominant | 9 | 15 | 12 | 4:ret=6,cont=2,diff=2,jump=2,cause=retention_drop_dominant | 2:9;3:0;4:0;5:2;6:0;7:0;8:-1;9:0;10:0;11:0;12:0;13:0 | 2:39;3:24;4:12;5:6;6:4;7:2;8:1;9:0;10:0;11:0;12:0;13:0 | 2:24;3:12;4:6;5:4;6:2;7:1;8:0;9:0;10:0;11:0;12:0;13:0 |
| 10543 | 4 | retention_drop_dominant | 9 | 15 | 12 | 4:ret=6,cont=2,diff=2,jump=2,cause=retention_drop_dominant | 2:9;3:0;4:0;5:2;6:0;7:0;8:-1;9:0;10:0;11:0;12:0;13:0 | 2:39;3:24;4:12;5:6;6:4;7:2;8:1;9:0;10:0;11:0;12:0;13:0 | 2:24;3:12;4:6;5:4;6:2;7:1;8:0;9:0;10:0;11:0;12:0;13:0 |
| 11105 | 4 | retention_drop_dominant | 9 | 15 | 12 | 4:ret=6,cont=2,diff=2,jump=2,cause=retention_drop_dominant | 2:9;3:0;4:0;5:2;6:0;7:0;8:-1;9:0;10:0;11:0;12:0;13:0 | 2:39;3:24;4:12;5:6;6:4;7:2;8:1;9:0;10:0;11:0;12:0;13:0 | 2:24;3:12;4:6;5:4;6:2;7:1;8:0;9:0;10:0;11:0;12:0;13:0 |
| 11515 | 2 | retention_drop_dominant | 9 | 13 | 2 | 2:ret=13,cont=2,diff=9,jump=9,cause=retention_drop_dominant | 2:-8;3:1;4:-1;5:-1;6:0;7:0;8:0;9:0;10:0;11:0;12:0;13:0 | 2:18;3:5;4:3;5:1;6:0;7:0;8:0;9:0;10:0;11:0;12:0;13:0 | 2:5;3:3;4:1;5:0;6:0;7:0;8:0;9:0;10:0;11:0;12:0;13:0 |

## Largest Retention-Drop Sign-Change Samples

| n | sign-up | causes | retention drop | continuation drop | drop details | all-ones depths |
|---:|---|---|---:|---:|---|---|
| 12399 | 3 | retention_drop_dominant | 18 | 10 | 3:ret=10,cont=4,diff=2,jump=2,cause=retention_drop_dominant | 3;2;1;2;1;4;3;2;1;3;2;1;2;1;1;1;3;2;1;3;2;1;2;1;2;1;10;9;8;7;6;5;4;3;2;1;3;2;1;1;1;1;3;2;1;1;1;2;1;2;1;2;1;1;3;2;1;4;3;2;1;1;2;1 |
| 14695 | 3 | retention_drop_dominant | 17 | 11 | 3:ret=11,cont=4,diff=3,jump=3,cause=retention_drop_dominant | 2;1;5;4;3;2;1;1;4;3;2;1;3;2;1;2;1;1;1;3;2;1;3;2;1;2;1;2;1;10;9;8;7;6;5;4;3;2;1;3;2;1;1;1;1;3;2;1;1;1;2;1;2;1;2;1;1;3;2;1;4;3;2;1 |
| 16379 | 2 | retention_drop_dominant | 17 | 6 | 2:ret=17,cont=6,diff=5,jump=5,cause=retention_drop_dominant | 1;2;1;2;1;2;1;7;6;5;4;3;2;1;3;2;1;2;1;1;1;3;2;1;6;5;4;3;2;1;2;1;1;5;4;3;2;1;2;1;2;1;1;2;1;1;1;1;2;1;1;2;1;1;1;3;2;1;1;1;1;1;1;1 |
| 7279 | 2 | retention_drop_dominant | 17 | 7 | 2:ret=17,cont=7,diff=3,jump=3,cause=retention_drop_dominant | 3;2;1;2;1;2;1;2;1;7;6;5;4;3;2;1;3;2;1;2;1;1;1;3;2;1;6;5;4;3;2;1;2;1;1;5;4;3;2;1;2;1;2;1;1;2;1;1;1;1;2;1;1;2;1;1;1;3;2;1;1;1;1;1 |
| 9705 | 2 | retention_drop_dominant | 17 | 7 | 2:ret=17,cont=7,diff=3,jump=3,cause=retention_drop_dominant | 4;3;2;1;2;1;2;1;2;1;7;6;5;4;3;2;1;3;2;1;2;1;1;1;3;2;1;6;5;4;3;2;1;2;1;1;5;4;3;2;1;2;1;2;1;1;2;1;1;1;1;2;1;1;2;1;1;1;3;2;1;1;1;1 |
| 10919 | 2 | retention_drop_dominant | 17 | 7 | 2:ret=17,cont=7,diff=3,jump=3,cause=retention_drop_dominant | 2;1;2;1;2;1;2;1;7;6;5;4;3;2;1;3;2;1;2;1;1;1;3;2;1;6;5;4;3;2;1;2;1;1;5;4;3;2;1;2;1;2;1;1;2;1;1;1;1;2;1;1;2;1;1;1;3;2;1;1;1;1;1;1 |
| 13183 | 4 | retention_drop_dominant | 17 | 10 | 4:ret=5,cont=2,diff=1,jump=1,cause=retention_drop_dominant | 6;5;4;3;2;1;2;1;2;1;2;1;1;2;1;1;3;2;1;6;5;4;3;2;1;1;1;1;4;3;2;1;2;1;1;2;1;3;2;1;1;1;3;2;1;1;1;3;2;1;4;3;2;1;1;2;1;3;2;1;4;3;2;1 |
| 7963 | 3 | retention_drop_dominant | 17 | 9 | 3:ret=9,cont=4,diff=1,jump=1,cause=retention_drop_dominant | 1;8;7;6;5;4;3;2;1;1;1;1;3;2;1;3;2;1;2;1;1;2;1;5;4;3;2;1;2;1;3;2;1;1;2;1;1;2;1;1;3;2;1;1;4;3;2;1;2;1;1;1;1;4;3;2;1;1;2;1;3;2;1;4 |
| 10617 | 3 | retention_drop_dominant | 17 | 9 | 3:ret=9,cont=4,diff=1,jump=1,cause=retention_drop_dominant | 2;1;8;7;6;5;4;3;2;1;1;1;1;3;2;1;3;2;1;2;1;1;2;1;5;4;3;2;1;2;1;3;2;1;1;2;1;1;2;1;1;3;2;1;1;4;3;2;1;2;1;1;1;1;4;3;2;1;1;2;1;3;2;1 |
| 12583 | 3 | retention_drop_dominant | 17 | 9 | 3:ret=9,cont=4,diff=1,jump=1,cause=retention_drop_dominant | 2;1;2;1;1;8;7;6;5;4;3;2;1;1;1;1;3;2;1;3;2;1;2;1;1;2;1;5;4;3;2;1;2;1;3;2;1;1;2;1;1;2;1;1;3;2;1;1;4;3;2;1;2;1;1;1;1;4;3;2;1;1;2;1 |
| 4935 | 4 | retention_drop_dominant | 16 | 13 | 4:ret=6,cont=2,diff=2,jump=2,cause=retention_drop_dominant | 2;1;1;3;2;1;4;3;2;1;1;1;1;8;7;6;5;4;3;2;1;1;3;2;1;3;2;1;2;1;3;2;1;4;3;2;1;2;1;3;2;1;4;3;2;1;1;3;2;1;2;1;6;5;4;3;2;1;4;3;2;1;1;1 |
| 9871 | 4 | retention_drop_dominant | 16 | 13 | 4:ret=7,cont=2,diff=3,jump=3,cause=retention_drop_dominant | 3;2;1;3;2;1;4;3;2;1;1;1;1;8;7;6;5;4;3;2;1;1;3;2;1;3;2;1;2;1;3;2;1;4;3;2;1;2;1;3;2;1;4;3;2;1;1;3;2;1;2;1;6;5;4;3;2;1;4;3;2;1;1;1 |

## PressureDecay: Sign-Change-Up Rows

| n | sign-change-up pressure-decay details |
|---:|---|
| 1567 | j=2,margin_j=-2,margin_next=1,margin_jump=3,retention_j=8,retention_next=3,retention_drop=5,continuation_j=3,continuation_next=2,continuation_drop=1,retention_drop_minus_2_continuation_drop=3,cause=retention_drop_dominant |
| 1639 | j=4,margin_j=0,margin_next=1,margin_jump=1,retention_j=6,retention_next=3,retention_drop=3,continuation_j=3,continuation_next=2,continuation_drop=1,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 1775 | j=4,margin_j=0,margin_next=1,margin_jump=1,retention_j=6,retention_next=3,retention_drop=3,continuation_j=3,continuation_next=2,continuation_drop=1,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 1899 | j=2,margin_j=0,margin_next=3,margin_jump=3,retention_j=10,retention_next=5,retention_drop=5,continuation_j=5,continuation_next=4,continuation_drop=1,retention_drop_minus_2_continuation_drop=3,cause=retention_drop_dominant |
| 2079 | j=2,margin_j=0,margin_next=1,margin_jump=1,retention_j=6,retention_next=3,retention_drop=3,continuation_j=3,continuation_next=2,continuation_drop=1,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 2089 | j=2,margin_j=-2,margin_next=1,margin_jump=3,retention_j=8,retention_next=3,retention_drop=5,continuation_j=3,continuation_next=2,continuation_drop=1,retention_drop_minus_2_continuation_drop=3,cause=retention_drop_dominant |
| 2103 | j=4,margin_j=0,margin_next=1,margin_jump=1,retention_j=6,retention_next=3,retention_drop=3,continuation_j=3,continuation_next=2,continuation_drop=1,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 2185 | j=4,margin_j=0,margin_next=1,margin_jump=1,retention_j=6,retention_next=3,retention_drop=3,continuation_j=3,continuation_next=2,continuation_drop=1,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 2431 | j=3,margin_j=0,margin_next=1,margin_jump=1,retention_j=22,retention_next=11,retention_drop=11,continuation_j=11,continuation_next=6,continuation_drop=5,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 2459 | j=4,margin_j=0,margin_next=1,margin_jump=1,retention_j=6,retention_next=3,retention_drop=3,continuation_j=3,continuation_next=2,continuation_drop=1,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 2475 | j=2,margin_j=-3,margin_next=1,margin_jump=4,retention_j=9,retention_next=3,retention_drop=6,continuation_j=3,continuation_next=2,continuation_drop=1,retention_drop_minus_2_continuation_drop=4,cause=retention_drop_dominant |
| 2495 | j=3,margin_j=0,margin_next=1,margin_jump=1,retention_j=6,retention_next=3,retention_drop=3,continuation_j=3,continuation_next=2,continuation_drop=1,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 2655 | j=2,margin_j=-1,margin_next=1,margin_jump=2,retention_j=7,retention_next=3,retention_drop=4,continuation_j=3,continuation_next=2,continuation_drop=1,retention_drop_minus_2_continuation_drop=2,cause=retention_drop_dominant |
| 2715 | j=4,margin_j=0,margin_next=1,margin_jump=1,retention_j=6,retention_next=3,retention_drop=3,continuation_j=3,continuation_next=2,continuation_drop=1,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 2727 | j=4,margin_j=0,margin_next=1,margin_jump=1,retention_j=6,retention_next=3,retention_drop=3,continuation_j=3,continuation_next=2,continuation_drop=1,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 2767 | j=4,margin_j=0,margin_next=1,margin_jump=1,retention_j=6,retention_next=3,retention_drop=3,continuation_j=3,continuation_next=2,continuation_drop=1,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 2785 | j=2,margin_j=-2,margin_next=1,margin_jump=3,retention_j=8,retention_next=3,retention_drop=5,continuation_j=3,continuation_next=2,continuation_drop=1,retention_drop_minus_2_continuation_drop=3,cause=retention_drop_dominant |
| 2815 | j=3,margin_j=0,margin_next=1,margin_jump=1,retention_j=22,retention_next=11,retention_drop=11,continuation_j=11,continuation_next=6,continuation_drop=5,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 2913 | j=4,margin_j=0,margin_next=1,margin_jump=1,retention_j=6,retention_next=3,retention_drop=3,continuation_j=3,continuation_next=2,continuation_drop=1,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 3055 | j=4,margin_j=0,margin_next=1,margin_jump=1,retention_j=6,retention_next=3,retention_drop=3,continuation_j=3,continuation_next=2,continuation_drop=1,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 3135 | j=2,margin_j=-1,margin_next=2,margin_jump=3,retention_j=9,retention_next=4,retention_drop=5,continuation_j=4,continuation_next=3,continuation_drop=1,retention_drop_minus_2_continuation_drop=3,cause=retention_drop_dominant |
| 3155 | j=4,margin_j=0,margin_next=1,margin_jump=1,retention_j=6,retention_next=3,retention_drop=3,continuation_j=3,continuation_next=2,continuation_drop=1,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 3175 | j=4,margin_j=-1,margin_next=2,margin_jump=3,retention_j=13,retention_next=6,retention_drop=7,continuation_j=6,continuation_next=4,continuation_drop=2,retention_drop_minus_2_continuation_drop=3,cause=retention_drop_dominant |
| 3241 | j=3,margin_j=0,margin_next=1,margin_jump=1,retention_j=22,retention_next=11,retention_drop=11,continuation_j=11,continuation_next=6,continuation_drop=5,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 3279 | j=4,margin_j=0,margin_next=1,margin_jump=1,retention_j=6,retention_next=3,retention_drop=3,continuation_j=3,continuation_next=2,continuation_drop=1,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 3323 | j=2,margin_j=-2,margin_next=1,margin_jump=3,retention_j=20,retention_next=9,retention_drop=11,continuation_j=9,continuation_next=5,continuation_drop=4,retention_drop_minus_2_continuation_drop=3,cause=retention_drop_dominant |
| 3627 | j=2,margin_j=0,margin_next=1,margin_jump=1,retention_j=6,retention_next=3,retention_drop=3,continuation_j=3,continuation_next=2,continuation_drop=1,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 3689 | j=4,margin_j=0,margin_next=1,margin_jump=1,retention_j=6,retention_next=3,retention_drop=3,continuation_j=3,continuation_next=2,continuation_drop=1,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 3713 | j=2,margin_j=-2,margin_next=1,margin_jump=3,retention_j=8,retention_next=3,retention_drop=5,continuation_j=3,continuation_next=2,continuation_drop=1,retention_drop_minus_2_continuation_drop=3,cause=retention_drop_dominant |
| 3739 | j=2,margin_j=-1,margin_next=1,margin_jump=2,retention_j=19,retention_next=9,retention_drop=10,continuation_j=9,continuation_next=5,continuation_drop=4,retention_drop_minus_2_continuation_drop=2,cause=retention_drop_dominant |
| 3753 | j=3,margin_j=0,margin_next=1,margin_jump=1,retention_j=22,retention_next=11,retention_drop=11,continuation_j=11,continuation_next=6,continuation_drop=5,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 4073 | j=4,margin_j=0,margin_next=1,margin_jump=1,retention_j=6,retention_next=3,retention_drop=3,continuation_j=3,continuation_next=2,continuation_drop=1,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 4091 | j=4,margin_j=0,margin_next=1,margin_jump=1,retention_j=6,retention_next=3,retention_drop=3,continuation_j=3,continuation_next=2,continuation_drop=1,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 4151 | j=3,margin_j=0,margin_next=1,margin_jump=1,retention_j=10,retention_next=5,retention_drop=5,continuation_j=5,continuation_next=3,continuation_drop=2,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 4207 | j=2,margin_j=0,margin_next=1,margin_jump=1,retention_j=18,retention_next=9,retention_drop=9,continuation_j=9,continuation_next=5,continuation_drop=4,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 4223 | j=4,margin_j=0,margin_next=1,margin_jump=1,retention_j=10,retention_next=5,retention_drop=5,continuation_j=5,continuation_next=3,continuation_drop=2,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 4233 | j=4,margin_j=-1,margin_next=2,margin_jump=3,retention_j=13,retention_next=6,retention_drop=7,continuation_j=6,continuation_next=4,continuation_drop=2,retention_drop_minus_2_continuation_drop=3,cause=retention_drop_dominant |
| 4321 | j=3,margin_j=0,margin_next=1,margin_jump=1,retention_j=22,retention_next=11,retention_drop=11,continuation_j=11,continuation_next=6,continuation_drop=5,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 4335 | j=2,margin_j=0,margin_next=1,margin_jump=1,retention_j=10,retention_next=5,retention_drop=5,continuation_j=5,continuation_next=3,continuation_drop=2,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 4371 | j=4,margin_j=0,margin_next=1,margin_jump=1,retention_j=6,retention_next=3,retention_drop=3,continuation_j=3,continuation_next=2,continuation_drop=1,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 4435 | j=3,margin_j=0,margin_next=1,margin_jump=1,retention_j=6,retention_next=3,retention_drop=3,continuation_j=3,continuation_next=2,continuation_drop=1,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 4551 | j=3,margin_j=-1,margin_next=1,margin_jump=2,retention_j=23,retention_next=11,retention_drop=12,continuation_j=11,continuation_next=6,continuation_drop=5,retention_drop_minus_2_continuation_drop=2,cause=retention_drop_dominant |
| 4583 | j=3,margin_j=0,margin_next=1,margin_jump=1,retention_j=10,retention_next=5,retention_drop=5,continuation_j=5,continuation_next=3,continuation_drop=2,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 4603 | j=4,margin_j=0,margin_next=1,margin_jump=1,retention_j=6,retention_next=3,retention_drop=3,continuation_j=3,continuation_next=2,continuation_drop=1,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 4635 | j=2,margin_j=-1,margin_next=1,margin_jump=2,retention_j=15,retention_next=7,retention_drop=8,continuation_j=7,continuation_next=4,continuation_drop=3,retention_drop_minus_2_continuation_drop=2,cause=retention_drop_dominant |
| 4703 | j=2,margin_j=-2,margin_next=1,margin_jump=3,retention_j=8,retention_next=3,retention_drop=5,continuation_j=3,continuation_next=2,continuation_drop=1,retention_drop_minus_2_continuation_drop=3,cause=retention_drop_dominant |
| 4733 | j=4,margin_j=0,margin_next=1,margin_jump=1,retention_j=6,retention_next=3,retention_drop=3,continuation_j=3,continuation_next=2,continuation_drop=1,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 4763 | j=4,margin_j=-1,margin_next=2,margin_jump=3,retention_j=13,retention_next=6,retention_drop=7,continuation_j=6,continuation_next=4,continuation_drop=2,retention_drop_minus_2_continuation_drop=3,cause=retention_drop_dominant |
| 4827 | j=3,margin_j=-1,margin_next=1,margin_jump=2,retention_j=11,retention_next=5,retention_drop=6,continuation_j=5,continuation_next=3,continuation_drop=2,retention_drop_minus_2_continuation_drop=2,cause=retention_drop_dominant |
| 4919 | j=3,margin_j=-1,margin_next=1,margin_jump=2,retention_j=11,retention_next=5,retention_drop=6,continuation_j=5,continuation_next=3,continuation_drop=2,retention_drop_minus_2_continuation_drop=2,cause=retention_drop_dominant |
| 4935 | j=4,margin_j=0,margin_next=2,margin_jump=2,retention_j=12,retention_next=6,retention_drop=6,continuation_j=6,continuation_next=4,continuation_drop=2,retention_drop_minus_2_continuation_drop=2,cause=retention_drop_dominant |
| 4959 | j=2,margin_j=0,margin_next=1,margin_jump=1,retention_j=6,retention_next=3,retention_drop=3,continuation_j=3,continuation_next=2,continuation_drop=1,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 4985 | j=2,margin_j=-1,margin_next=1,margin_jump=2,retention_j=19,retention_next=9,retention_drop=10,continuation_j=9,continuation_next=5,continuation_drop=4,retention_drop_minus_2_continuation_drop=2,cause=retention_drop_dominant |
| 4991 | j=2,margin_j=0,margin_next=2,margin_jump=2,retention_j=12,retention_next=6,retention_drop=6,continuation_j=6,continuation_next=4,continuation_drop=2,retention_drop_minus_2_continuation_drop=2,cause=retention_drop_dominant |
| 5055 | j=2,margin_j=-2,margin_next=1,margin_jump=3,retention_j=12,retention_next=5,retention_drop=7,continuation_j=5,continuation_next=3,continuation_drop=2,retention_drop_minus_2_continuation_drop=3,cause=retention_drop_dominant |
| 5179 | j=4,margin_j=0,margin_next=1,margin_jump=1,retention_j=6,retention_next=3,retention_drop=3,continuation_j=3,continuation_next=2,continuation_drop=1,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 5191 | j=2,margin_j=0,margin_next=1,margin_jump=1,retention_j=10,retention_next=5,retention_drop=5,continuation_j=5,continuation_next=3,continuation_drop=2,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 5215 | j=2,margin_j=0,margin_next=1,margin_jump=1,retention_j=14,retention_next=7,retention_drop=7,continuation_j=7,continuation_next=4,continuation_drop=3,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 5247 | j=2,margin_j=-1,margin_next=2,margin_jump=3,retention_j=13,retention_next=6,retention_drop=7,continuation_j=6,continuation_next=4,continuation_drop=2,retention_drop_minus_2_continuation_drop=3,cause=retention_drop_dominant |
| 5255 | j=3,margin_j=0,margin_next=2,margin_jump=2,retention_j=8,retention_next=4,retention_drop=4,continuation_j=4,continuation_next=3,continuation_drop=1,retention_drop_minus_2_continuation_drop=2,cause=retention_drop_dominant |
| 5359 | j=4,margin_j=-1,margin_next=2,margin_jump=3,retention_j=13,retention_next=6,retention_drop=7,continuation_j=6,continuation_next=4,continuation_drop=2,retention_drop_minus_2_continuation_drop=3,cause=retention_drop_dominant |
| 5403 | j=2,margin_j=-1,margin_next=1,margin_jump=2,retention_j=11,retention_next=5,retention_drop=6,continuation_j=5,continuation_next=3,continuation_drop=2,retention_drop_minus_2_continuation_drop=2,cause=retention_drop_dominant |
| 5431 | j=3,margin_j=-1,margin_next=1,margin_jump=2,retention_j=11,retention_next=5,retention_drop=6,continuation_j=5,continuation_next=3,continuation_drop=2,retention_drop_minus_2_continuation_drop=2,cause=retention_drop_dominant |
| 5455 | j=4,margin_j=-1,margin_next=1,margin_jump=2,retention_j=7,retention_next=3,retention_drop=4,continuation_j=3,continuation_next=2,continuation_drop=1,retention_drop_minus_2_continuation_drop=2,cause=retention_drop_dominant |
| 5571 | j=2,margin_j=-3,margin_next=1,margin_jump=4,retention_j=9,retention_next=3,retention_drop=6,continuation_j=3,continuation_next=2,continuation_drop=1,retention_drop_minus_2_continuation_drop=4,cause=retention_drop_dominant |
| 5609 | j=2,margin_j=0,margin_next=1,margin_jump=1,retention_j=18,retention_next=9,retention_drop=9,continuation_j=9,continuation_next=5,continuation_drop=4,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 5659 | j=2,margin_j=-3,margin_next=1,margin_jump=4,retention_j=9,retention_next=3,retention_drop=6,continuation_j=3,continuation_next=2,continuation_drop=1,retention_drop_minus_2_continuation_drop=4,cause=retention_drop_dominant |
| 5699 | j=2,margin_j=0,margin_next=3,margin_jump=3,retention_j=10,retention_next=5,retention_drop=5,continuation_j=5,continuation_next=4,continuation_drop=1,retention_drop_minus_2_continuation_drop=3,cause=retention_drop_dominant |
| 5759 | j=3,margin_j=0,margin_next=1,margin_jump=1,retention_j=10,retention_next=5,retention_drop=5,continuation_j=5,continuation_next=3,continuation_drop=2,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 5761 | j=3,margin_j=0,margin_next=1,margin_jump=1,retention_j=22,retention_next=11,retention_drop=11,continuation_j=11,continuation_next=6,continuation_drop=5,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 5827 | j=4,margin_j=0,margin_next=1,margin_jump=1,retention_j=6,retention_next=3,retention_drop=3,continuation_j=3,continuation_next=2,continuation_drop=1,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 5871 | j=2,margin_j=0,margin_next=1,margin_jump=1,retention_j=14,retention_next=7,retention_drop=7,continuation_j=7,continuation_next=4,continuation_drop=3,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 5887 | j=2,margin_j=-2,margin_next=2,margin_jump=4,retention_j=22,retention_next=10,retention_drop=12,continuation_j=10,continuation_next=6,continuation_drop=4,retention_drop_minus_2_continuation_drop=4,cause=retention_drop_dominant |
| 5907 | j=2,margin_j=-3,margin_next=1,margin_jump=4,retention_j=21,retention_next=9,retention_drop=12,continuation_j=9,continuation_next=5,continuation_drop=4,retention_drop_minus_2_continuation_drop=4,cause=retention_drop_dominant |
| 5913 | j=3,margin_j=0,margin_next=1,margin_jump=1,retention_j=6,retention_next=3,retention_drop=3,continuation_j=3,continuation_next=2,continuation_drop=1,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 5983 | j=2,margin_j=-1,margin_next=1,margin_jump=2,retention_j=7,retention_next=3,retention_drop=4,continuation_j=3,continuation_next=2,continuation_drop=1,retention_drop_minus_2_continuation_drop=2,cause=retention_drop_dominant |
| 5991 | j=2,margin_j=0,margin_next=1,margin_jump=1,retention_j=14,retention_next=7,retention_drop=7,continuation_j=7,continuation_next=4,continuation_drop=3,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 6079 | j=2,margin_j=0,margin_next=1,margin_jump=1,retention_j=10,retention_next=5,retention_drop=5,continuation_j=5,continuation_next=3,continuation_drop=2,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 6137 | j=4,margin_j=0,margin_next=1,margin_jump=1,retention_j=6,retention_next=3,retention_drop=3,continuation_j=3,continuation_next=2,continuation_drop=1,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 6139 | j=2,margin_j=-2,margin_next=1,margin_jump=3,retention_j=24,retention_next=11,retention_drop=13,continuation_j=11,continuation_next=6,continuation_drop=5,retention_drop_minus_2_continuation_drop=3,cause=retention_drop_dominant |
| 6207 | j=3,margin_j=0,margin_next=1,margin_jump=1,retention_j=6,retention_next=3,retention_drop=3,continuation_j=3,continuation_next=2,continuation_drop=1,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 6239 | j=2,margin_j=0,margin_next=1,margin_jump=1,retention_j=6,retention_next=3,retention_drop=3,continuation_j=3,continuation_next=2,continuation_drop=1,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 6247 | j=4,margin_j=0,margin_next=2,margin_jump=2,retention_j=12,retention_next=6,retention_drop=6,continuation_j=6,continuation_next=4,continuation_drop=2,retention_drop_minus_2_continuation_drop=2,cause=retention_drop_dominant |
| 6351 | j=4,margin_j=-1,margin_next=2,margin_jump=3,retention_j=13,retention_next=6,retention_drop=7,continuation_j=6,continuation_next=4,continuation_drop=2,retention_drop_minus_2_continuation_drop=3,cause=retention_drop_dominant |
| 6367 | j=2,margin_j=-2,margin_next=1,margin_jump=3,retention_j=8,retention_next=3,retention_drop=5,continuation_j=3,continuation_next=2,continuation_drop=1,retention_drop_minus_2_continuation_drop=3,cause=retention_drop_dominant |
| 6395 | j=2,margin_j=0,margin_next=3,margin_jump=3,retention_j=22,retention_next=11,retention_drop=11,continuation_j=11,continuation_next=7,continuation_drop=4,retention_drop_minus_2_continuation_drop=3,cause=retention_drop_dominant |
| 6427 | j=2,margin_j=-1,margin_next=1,margin_jump=2,retention_j=11,retention_next=5,retention_drop=6,continuation_j=5,continuation_next=3,continuation_drop=2,retention_drop_minus_2_continuation_drop=2,cause=retention_drop_dominant |
| 6557 | j=4,margin_j=0,margin_next=1,margin_jump=1,retention_j=6,retention_next=3,retention_drop=3,continuation_j=3,continuation_next=2,continuation_drop=1,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 6559 | j=2,margin_j=-1,margin_next=1,margin_jump=2,retention_j=7,retention_next=3,retention_drop=4,continuation_j=3,continuation_next=2,continuation_drop=1,retention_drop_minus_2_continuation_drop=2,cause=retention_drop_dominant |
| 6571 | j=2,margin_j=0,margin_next=2,margin_jump=2,retention_j=8,retention_next=4,retention_drop=4,continuation_j=4,continuation_next=3,continuation_drop=1,retention_drop_minus_2_continuation_drop=2,cause=retention_drop_dominant |
| 6653 | j=3,margin_j=0,margin_next=1,margin_jump=1,retention_j=6,retention_next=3,retention_drop=3,continuation_j=3,continuation_next=2,continuation_drop=1,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 6687 | j=2,margin_j=0,margin_next=1,margin_jump=1,retention_j=6,retention_next=3,retention_drop=3,continuation_j=3,continuation_next=2,continuation_drop=1,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 6783 | j=4,margin_j=-1,margin_next=1,margin_jump=2,retention_j=11,retention_next=5,retention_drop=6,continuation_j=5,continuation_next=3,continuation_drop=2,retention_drop_minus_2_continuation_drop=2,cause=retention_drop_dominant |
| 6827 | j=3,margin_j=0,margin_next=1,margin_jump=1,retention_j=22,retention_next=11,retention_drop=11,continuation_j=11,continuation_next=6,continuation_drop=5,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 6847 | j=2,margin_j=0,margin_next=1,margin_jump=1,retention_j=10,retention_next=5,retention_drop=5,continuation_j=5,continuation_next=3,continuation_drop=2,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 6905 | j=4,margin_j=0,margin_next=1,margin_jump=1,retention_j=6,retention_next=3,retention_drop=3,continuation_j=3,continuation_next=2,continuation_drop=1,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 6907 | j=2,margin_j=-1,margin_next=1,margin_jump=2,retention_j=23,retention_next=11,retention_drop=12,continuation_j=11,continuation_next=6,continuation_drop=5,retention_drop_minus_2_continuation_drop=2,cause=retention_drop_dominant |
| 6921 | j=2,margin_j=0,margin_next=1,margin_jump=1,retention_j=10,retention_next=5,retention_drop=5,continuation_j=5,continuation_next=3,continuation_drop=2,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 6939 | j=2,margin_j=-2,margin_next=3,margin_jump=5,retention_j=16,retention_next=7,retention_drop=9,continuation_j=7,continuation_next=5,continuation_drop=2,retention_drop_minus_2_continuation_drop=5,cause=retention_drop_dominant |
| 6953 | j=2,margin_j=0,margin_next=1,margin_jump=1,retention_j=14,retention_next=7,retention_drop=7,continuation_j=7,continuation_next=4,continuation_drop=3,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 7071 | j=2,margin_j=-3,margin_next=1,margin_jump=4,retention_j=9,retention_next=3,retention_drop=6,continuation_j=3,continuation_next=2,continuation_drop=1,retention_drop_minus_2_continuation_drop=4,cause=retention_drop_dominant |
| 7145 | j=4,margin_j=-1,margin_next=2,margin_jump=3,retention_j=13,retention_next=6,retention_drop=7,continuation_j=6,continuation_next=4,continuation_drop=2,retention_drop_minus_2_continuation_drop=3,cause=retention_drop_dominant |
| 7231 | j=2,margin_j=0,margin_next=1,margin_jump=1,retention_j=10,retention_next=5,retention_drop=5,continuation_j=5,continuation_next=3,continuation_drop=2,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 7241 | j=3,margin_j=-1,margin_next=1,margin_jump=2,retention_j=11,retention_next=5,retention_drop=6,continuation_j=5,continuation_next=3,continuation_drop=2,retention_drop_minus_2_continuation_drop=2,cause=retention_drop_dominant |
| 7273 | j=4,margin_j=-1,margin_next=1,margin_jump=2,retention_j=7,retention_next=3,retention_drop=4,continuation_j=3,continuation_next=2,continuation_drop=1,retention_drop_minus_2_continuation_drop=2,cause=retention_drop_dominant |
| 7275 | j=2,margin_j=-3,margin_next=1,margin_jump=4,retention_j=25,retention_next=11,retention_drop=14,continuation_j=11,continuation_next=6,continuation_drop=5,retention_drop_minus_2_continuation_drop=4,cause=retention_drop_dominant |
| 7279 | j=2,margin_j=0,margin_next=3,margin_jump=3,retention_j=34,retention_next=17,retention_drop=17,continuation_j=17,continuation_next=10,continuation_drop=7,retention_drop_minus_2_continuation_drop=3,cause=retention_drop_dominant |
| 7327 | j=2,margin_j=0,margin_next=2,margin_jump=2,retention_j=16,retention_next=8,retention_drop=8,continuation_j=8,continuation_next=5,continuation_drop=3,retention_drop_minus_2_continuation_drop=2,cause=retention_drop_dominant |
| 7367 | j=3,margin_j=0,margin_next=1,margin_jump=1,retention_j=14,retention_next=7,retention_drop=7,continuation_j=7,continuation_next=4,continuation_drop=3,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 7379 | j=3,margin_j=0,margin_next=1,margin_jump=1,retention_j=10,retention_next=5,retention_drop=5,continuation_j=5,continuation_next=3,continuation_drop=2,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 7403 | j=4,margin_j=0,margin_next=2,margin_jump=2,retention_j=12,retention_next=6,retention_drop=6,continuation_j=6,continuation_next=4,continuation_drop=2,retention_drop_minus_2_continuation_drop=2,cause=retention_drop_dominant |
| 7423 | j=4,margin_j=-3,margin_next=2,margin_jump=5,retention_j=11,retention_next=4,retention_drop=7,continuation_j=4,continuation_next=3,continuation_drop=1,retention_drop_minus_2_continuation_drop=5,cause=retention_drop_dominant |
| 7427 | j=2,margin_j=-3,margin_next=1,margin_jump=4,retention_j=9,retention_next=3,retention_drop=6,continuation_j=3,continuation_next=2,continuation_drop=1,retention_drop_minus_2_continuation_drop=4,cause=retention_drop_dominant |
| 7455 | j=2,margin_j=0,margin_next=1,margin_jump=1,retention_j=10,retention_next=5,retention_drop=5,continuation_j=5,continuation_next=3,continuation_drop=2,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 7487 | j=2,margin_j=-1,margin_next=1,margin_jump=2,retention_j=11,retention_next=5,retention_drop=6,continuation_j=5,continuation_next=3,continuation_drop=2,retention_drop_minus_2_continuation_drop=2,cause=retention_drop_dominant |
| 7507 | j=4,margin_j=0,margin_next=1,margin_jump=1,retention_j=10,retention_next=5,retention_drop=5,continuation_j=5,continuation_next=3,continuation_drop=2,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 7545 | j=2,margin_j=-3,margin_next=1,margin_jump=4,retention_j=9,retention_next=3,retention_drop=6,continuation_j=3,continuation_next=2,continuation_drop=1,retention_drop_minus_2_continuation_drop=4,cause=retention_drop_dominant |
| 7681 | j=3,margin_j=0,margin_next=1,margin_jump=1,retention_j=22,retention_next=11,retention_drop=11,continuation_j=11,continuation_next=6,continuation_drop=5,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 7707 | j=2,margin_j=-1,margin_next=1,margin_jump=2,retention_j=11,retention_next=5,retention_drop=6,continuation_j=5,continuation_next=3,continuation_drop=2,retention_drop_minus_2_continuation_drop=2,cause=retention_drop_dominant |
| 7743 | j=3,margin_j=-1,margin_next=1,margin_jump=2,retention_j=7,retention_next=3,retention_drop=4,continuation_j=3,continuation_next=2,continuation_drop=1,retention_drop_minus_2_continuation_drop=2,cause=retention_drop_dominant |
| 7769 | j=4,margin_j=0,margin_next=1,margin_jump=1,retention_j=6,retention_next=3,retention_drop=3,continuation_j=3,continuation_next=2,continuation_drop=1,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 7771 | j=2,margin_j=0,margin_next=1,margin_jump=1,retention_j=22,retention_next=11,retention_drop=11,continuation_j=11,continuation_next=6,continuation_drop=5,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 7787 | j=2,margin_j=-1,margin_next=2,margin_jump=3,retention_j=9,retention_next=4,retention_drop=5,continuation_j=4,continuation_next=3,continuation_drop=1,retention_drop_minus_2_continuation_drop=3,cause=retention_drop_dominant |
| 7807 | j=2,margin_j=-1,margin_next=3,margin_jump=4,retention_j=15,retention_next=7,retention_drop=8,continuation_j=7,continuation_next=5,continuation_drop=2,retention_drop_minus_2_continuation_drop=4,cause=retention_drop_dominant |
| 7849 | j=2,margin_j=-2,margin_next=2,margin_jump=4,retention_j=22,retention_next=10,retention_drop=12,continuation_j=10,continuation_next=6,continuation_drop=4,retention_drop_minus_2_continuation_drop=4,cause=retention_drop_dominant |
| 7871 | j=2,margin_j=-2,margin_next=1,margin_jump=3,retention_j=12,retention_next=5,retention_drop=7,continuation_j=5,continuation_next=3,continuation_drop=2,retention_drop_minus_2_continuation_drop=3,cause=retention_drop_dominant |
| 7883 | j=2,margin_j=0,margin_next=1,margin_jump=1,retention_j=14,retention_next=7,retention_drop=7,continuation_j=7,continuation_next=4,continuation_drop=3,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 7887 | j=4,margin_j=0,margin_next=1,margin_jump=1,retention_j=14,retention_next=7,retention_drop=7,continuation_j=7,continuation_next=4,continuation_drop=3,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 7963 | j=3,margin_j=0,margin_next=1,margin_jump=1,retention_j=18,retention_next=9,retention_drop=9,continuation_j=9,continuation_next=5,continuation_drop=4,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 7977 | j=2,margin_j=-1,margin_next=1,margin_jump=2,retention_j=7,retention_next=3,retention_drop=4,continuation_j=3,continuation_next=2,continuation_drop=1,retention_drop_minus_2_continuation_drop=2,cause=retention_drop_dominant |
| 8039 | j=4,margin_j=0,margin_next=2,margin_jump=2,retention_j=12,retention_next=6,retention_drop=6,continuation_j=6,continuation_next=4,continuation_drop=2,retention_drop_minus_2_continuation_drop=2,cause=retention_drop_dominant |
| 8105 | j=2,margin_j=0,margin_next=1,margin_jump=1,retention_j=10,retention_next=5,retention_drop=5,continuation_j=5,continuation_next=3,continuation_drop=2,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 8147 | j=3,margin_j=0,margin_next=1,margin_jump=1,retention_j=10,retention_next=5,retention_drop=5,continuation_j=5,continuation_next=3,continuation_drop=2,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 8163 | j=2,margin_j=0,margin_next=1,margin_jump=1,retention_j=6,retention_next=3,retention_drop=3,continuation_j=3,continuation_next=2,continuation_drop=1,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 8183 | j=4,margin_j=0,margin_next=1,margin_jump=1,retention_j=6,retention_next=3,retention_drop=3,continuation_j=3,continuation_next=2,continuation_drop=1,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 8185 | j=2,margin_j=-2,margin_next=1,margin_jump=3,retention_j=24,retention_next=11,retention_drop=13,continuation_j=11,continuation_next=6,continuation_drop=5,retention_drop_minus_2_continuation_drop=3,cause=retention_drop_dominant |
| 8187 | j=3,margin_j=-1,margin_next=1,margin_jump=2,retention_j=11,retention_next=5,retention_drop=6,continuation_j=5,continuation_next=3,continuation_drop=2,retention_drop_minus_2_continuation_drop=2,cause=retention_drop_dominant |
| 8319 | j=3,margin_j=0,margin_next=1,margin_jump=1,retention_j=10,retention_next=5,retention_drop=5,continuation_j=5,continuation_next=3,continuation_drop=2,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 8329 | j=4,margin_j=0,margin_next=2,margin_jump=2,retention_j=12,retention_next=6,retention_drop=6,continuation_j=6,continuation_next=4,continuation_drop=2,retention_drop_minus_2_continuation_drop=2,cause=retention_drop_dominant |
| 8357 | j=2,margin_j=-2,margin_next=1,margin_jump=3,retention_j=8,retention_next=3,retention_drop=5,continuation_j=3,continuation_next=2,continuation_drop=1,retention_drop_minus_2_continuation_drop=3,cause=retention_drop_dominant |
| 8413 | j=4,margin_j=0,margin_next=1,margin_jump=1,retention_j=6,retention_next=3,retention_drop=3,continuation_j=3,continuation_next=2,continuation_drop=1,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 8443 | j=3,margin_j=0,margin_next=1,margin_jump=1,retention_j=10,retention_next=5,retention_drop=5,continuation_j=5,continuation_next=3,continuation_drop=2,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 8447 | j=3,margin_j=0,margin_next=1,margin_jump=1,retention_j=22,retention_next=11,retention_drop=11,continuation_j=11,continuation_next=6,continuation_drop=5,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 8467 | j=4,margin_j=-1,margin_next=2,margin_jump=3,retention_j=13,retention_next=6,retention_drop=7,continuation_j=6,continuation_next=4,continuation_drop=2,retention_drop_minus_2_continuation_drop=3,cause=retention_drop_dominant |
| 8475 | j=2,margin_j=0,margin_next=1,margin_jump=1,retention_j=18,retention_next=9,retention_drop=9,continuation_j=9,continuation_next=5,continuation_drop=4,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 8489 | j=2,margin_j=-2,margin_next=1,margin_jump=3,retention_j=8,retention_next=3,retention_drop=5,continuation_j=3,continuation_next=2,continuation_drop=1,retention_drop_minus_2_continuation_drop=3,cause=retention_drop_dominant |
| 8569 | j=2,margin_j=-1,margin_next=1,margin_jump=2,retention_j=11,retention_next=5,retention_drop=6,continuation_j=5,continuation_next=3,continuation_drop=2,retention_drop_minus_2_continuation_drop=2,cause=retention_drop_dominant |
| 8619 | j=4,margin_j=-1,margin_next=1,margin_jump=2,retention_j=7,retention_next=3,retention_drop=4,continuation_j=3,continuation_next=2,continuation_drop=1,retention_drop_minus_2_continuation_drop=2,cause=retention_drop_dominant |
| 8643 | j=3,margin_j=0,margin_next=1,margin_jump=1,retention_j=22,retention_next=11,retention_drop=11,continuation_j=11,continuation_next=6,continuation_drop=5,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 8671 | j=2,margin_j=0,margin_next=1,margin_jump=1,retention_j=10,retention_next=5,retention_drop=5,continuation_j=5,continuation_next=3,continuation_drop=2,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 8683 | j=2,margin_j=-1,margin_next=2,margin_jump=3,retention_j=17,retention_next=8,retention_drop=9,continuation_j=8,continuation_next=5,continuation_drop=3,retention_drop_minus_2_continuation_drop=3,cause=retention_drop_dominant |
| 8741 | j=4,margin_j=0,margin_next=1,margin_jump=1,retention_j=6,retention_next=3,retention_drop=3,continuation_j=3,continuation_next=2,continuation_drop=1,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 8745 | j=2,margin_j=-1,margin_next=1,margin_jump=2,retention_j=7,retention_next=3,retention_drop=4,continuation_j=3,continuation_next=2,continuation_drop=1,retention_drop_minus_2_continuation_drop=2,cause=retention_drop_dominant |
| 8761 | j=2,margin_j=0,margin_next=2,margin_jump=2,retention_j=8,retention_next=4,retention_drop=4,continuation_j=4,continuation_next=3,continuation_drop=1,retention_drop_minus_2_continuation_drop=2,cause=retention_drop_dominant |
| 8767 | j=2,margin_j=-2,margin_next=1,margin_jump=3,retention_j=12,retention_next=5,retention_drop=7,continuation_j=5,continuation_next=3,continuation_drop=2,retention_drop_minus_2_continuation_drop=3,cause=retention_drop_dominant |
| 8831 | j=2,margin_j=-3,margin_next=1,margin_jump=4,retention_j=21,retention_next=9,retention_drop=12,continuation_j=9,continuation_next=5,continuation_drop=4,retention_drop_minus_2_continuation_drop=4,cause=retention_drop_dominant |
| 8861 | j=2,margin_j=-2,margin_next=1,margin_jump=3,retention_j=20,retention_next=9,retention_drop=11,continuation_j=9,continuation_next=5,continuation_drop=4,retention_drop_minus_2_continuation_drop=3,cause=retention_drop_dominant |
| 8959 | j=4,margin_j=0,margin_next=1,margin_jump=1,retention_j=10,retention_next=5,retention_drop=5,continuation_j=5,continuation_next=3,continuation_drop=2,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 8983 | j=3,margin_j=0,margin_next=1,margin_jump=1,retention_j=22,retention_next=11,retention_drop=11,continuation_j=11,continuation_next=6,continuation_drop=5,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 8987 | j=2,margin_j=-1,margin_next=2,margin_jump=3,retention_j=13,retention_next=6,retention_drop=7,continuation_j=6,continuation_next=4,continuation_drop=2,retention_drop_minus_2_continuation_drop=3,cause=retention_drop_dominant |
| 9003 | j=2,margin_j=0,margin_next=3,margin_jump=3,retention_j=10,retention_next=5,retention_drop=5,continuation_j=5,continuation_next=4,continuation_drop=1,retention_drop_minus_2_continuation_drop=3,cause=retention_drop_dominant |
| 9055 | j=2,margin_j=0,margin_next=1,margin_jump=1,retention_j=6,retention_next=3,retention_drop=3,continuation_j=3,continuation_next=2,continuation_drop=1,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 9063 | j=3,margin_j=0,margin_next=1,margin_jump=1,retention_j=6,retention_next=3,retention_drop=3,continuation_j=3,continuation_next=2,continuation_drop=1,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 9087 | j=7,margin_j=0,margin_next=1,margin_jump=1,retention_j=6,retention_next=3,retention_drop=3,continuation_j=3,continuation_next=2,continuation_drop=1,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 9099 | j=2,margin_j=0,margin_next=1,margin_jump=1,retention_j=22,retention_next=11,retention_drop=11,continuation_j=11,continuation_next=6,continuation_drop=5,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 9129 | j=2,margin_j=0,margin_next=1,margin_jump=1,retention_j=10,retention_next=5,retention_drop=5,continuation_j=5,continuation_next=3,continuation_drop=2,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 9167 | j=4,margin_j=0,margin_next=1,margin_jump=1,retention_j=6,retention_next=3,retention_drop=3,continuation_j=3,continuation_next=2,continuation_drop=1,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 9207 | j=4,margin_j=0,margin_next=1,margin_jump=1,retention_j=6,retention_next=3,retention_drop=3,continuation_j=3,continuation_next=2,continuation_drop=1,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 9209 | j=2,margin_j=-1,margin_next=1,margin_jump=2,retention_j=23,retention_next=11,retention_drop=12,continuation_j=11,continuation_next=6,continuation_drop=5,retention_drop_minus_2_continuation_drop=2,cause=retention_drop_dominant |
| 9211 | j=3,margin_j=-1,margin_next=1,margin_jump=2,retention_j=11,retention_next=5,retention_drop=6,continuation_j=5,continuation_next=3,continuation_drop=2,retention_drop_minus_2_continuation_drop=2,cause=retention_drop_dominant |
| 9243 | j=2,margin_j=-2,margin_next=3,margin_jump=5,retention_j=16,retention_next=7,retention_drop=9,continuation_j=7,continuation_next=5,continuation_drop=2,retention_drop_minus_2_continuation_drop=5,cause=retention_drop_dominant |
| 9279 | j=2,margin_j=-3,margin_next=1,margin_jump=4,retention_j=13,retention_next=5,retention_drop=8,continuation_j=5,continuation_next=3,continuation_drop=2,retention_drop_minus_2_continuation_drop=4,cause=retention_drop_dominant |
| 9371 | j=4,margin_j=0,margin_next=2,margin_jump=2,retention_j=12,retention_next=6,retention_drop=6,continuation_j=6,continuation_next=4,continuation_drop=2,retention_drop_minus_2_continuation_drop=2,cause=retention_drop_dominant |
| 9467 | j=2,margin_j=-2,margin_next=1,margin_jump=3,retention_j=16,retention_next=7,retention_drop=9,continuation_j=7,continuation_next=4,continuation_drop=3,retention_drop_minus_2_continuation_drop=3,cause=retention_drop_dominant |
| 9499 | j=3,margin_j=0,margin_next=1,margin_jump=1,retention_j=10,retention_next=5,retention_drop=5,continuation_j=5,continuation_next=3,continuation_drop=2,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 9527 | j=4,margin_j=0,margin_next=2,margin_jump=2,retention_j=12,retention_next=6,retention_drop=6,continuation_j=6,continuation_next=4,continuation_drop=2,retention_drop_minus_2_continuation_drop=2,cause=retention_drop_dominant |
| 9641 | j=2,margin_j=0,margin_next=1,margin_jump=1,retention_j=10,retention_next=5,retention_drop=5,continuation_j=5,continuation_next=3,continuation_drop=2,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 9655 | j=3,margin_j=-1,margin_next=1,margin_jump=2,retention_j=11,retention_next=5,retention_drop=6,continuation_j=5,continuation_next=3,continuation_drop=2,retention_drop_minus_2_continuation_drop=2,cause=retention_drop_dominant |
| 9697 | j=4,margin_j=-1,margin_next=1,margin_jump=2,retention_j=7,retention_next=3,retention_drop=4,continuation_j=3,continuation_next=2,continuation_drop=1,retention_drop_minus_2_continuation_drop=2,cause=retention_drop_dominant |
| 9703 | j=3,margin_j=-3,margin_next=1,margin_jump=4,retention_j=13,retention_next=5,retention_drop=8,continuation_j=5,continuation_next=3,continuation_drop=2,retention_drop_minus_2_continuation_drop=4,cause=retention_drop_dominant |
| 9705 | j=2,margin_j=0,margin_next=3,margin_jump=3,retention_j=34,retention_next=17,retention_drop=17,continuation_j=17,continuation_next=10,continuation_drop=7,retention_drop_minus_2_continuation_drop=3,cause=retention_drop_dominant |
| 9755 | j=2,margin_j=-2,margin_next=1,margin_jump=3,retention_j=8,retention_next=3,retention_drop=5,continuation_j=3,continuation_next=2,continuation_drop=1,retention_drop_minus_2_continuation_drop=3,cause=retention_drop_dominant |
| 9769 | j=2,margin_j=0,margin_next=2,margin_jump=2,retention_j=16,retention_next=8,retention_drop=8,continuation_j=8,continuation_next=5,continuation_drop=3,retention_drop_minus_2_continuation_drop=2,cause=retention_drop_dominant |
| 9837 | j=4,margin_j=0,margin_next=1,margin_jump=1,retention_j=6,retention_next=3,retention_drop=3,continuation_j=3,continuation_next=2,continuation_drop=1,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 9855 | j=3,margin_j=0,margin_next=2,margin_jump=2,retention_j=8,retention_next=4,retention_drop=4,continuation_j=4,continuation_next=3,continuation_drop=1,retention_drop_minus_2_continuation_drop=2,cause=retention_drop_dominant |
| 9871 | j=4,margin_j=-1,margin_next=2,margin_jump=3,retention_j=13,retention_next=6,retention_drop=7,continuation_j=6,continuation_next=4,continuation_drop=2,retention_drop_minus_2_continuation_drop=3,cause=retention_drop_dominant |
| 9897 | j=4,margin_j=-3,margin_next=2,margin_jump=5,retention_j=11,retention_next=4,retention_drop=7,continuation_j=4,continuation_next=3,continuation_drop=1,retention_drop_minus_2_continuation_drop=5,cause=retention_drop_dominant |
| 9901 | j=2,margin_j=-2,margin_next=1,margin_jump=3,retention_j=8,retention_next=3,retention_drop=5,continuation_j=3,continuation_next=2,continuation_drop=1,retention_drop_minus_2_continuation_drop=3,cause=retention_drop_dominant |
| 9971 | j=2,margin_j=-1,margin_next=1,margin_jump=2,retention_j=19,retention_next=9,retention_drop=10,continuation_j=9,continuation_next=5,continuation_drop=4,retention_drop_minus_2_continuation_drop=2,cause=retention_drop_dominant |
| 10009 | j=4,margin_j=0,margin_next=1,margin_jump=1,retention_j=10,retention_next=5,retention_drop=5,continuation_j=5,continuation_next=3,continuation_drop=2,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 10111 | j=2,margin_j=0,margin_next=2,margin_jump=2,retention_j=12,retention_next=6,retention_drop=6,continuation_j=6,continuation_next=4,continuation_drop=2,retention_drop_minus_2_continuation_drop=2,cause=retention_drop_dominant |
| 10131 | j=2,margin_j=-1,margin_next=3,margin_jump=4,retention_j=11,retention_next=5,retention_drop=6,continuation_j=5,continuation_next=4,continuation_drop=1,retention_drop_minus_2_continuation_drop=4,cause=retention_drop_dominant |
| 10155 | j=2,margin_j=-2,margin_next=1,margin_jump=3,retention_j=12,retention_next=5,retention_drop=7,continuation_j=5,continuation_next=3,continuation_drop=2,retention_drop_minus_2_continuation_drop=3,cause=retention_drop_dominant |
| 10215 | j=4,margin_j=-1,margin_next=1,margin_jump=2,retention_j=7,retention_next=3,retention_drop=4,continuation_j=3,continuation_next=2,continuation_drop=1,retention_drop_minus_2_continuation_drop=2,cause=retention_drop_dominant |
| 10235 | j=2,margin_j=-9,margin_next=1,margin_jump=10,retention_j=19,retention_next=5,retention_drop=14,continuation_j=5,continuation_next=3,continuation_drop=2,retention_drop_minus_2_continuation_drop=10,cause=retention_drop_dominant |
| 10241 | j=3,margin_j=0,margin_next=1,margin_jump=1,retention_j=22,retention_next=11,retention_drop=11,continuation_j=11,continuation_next=6,continuation_drop=5,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 10359 | j=4,margin_j=0,margin_next=1,margin_jump=1,retention_j=6,retention_next=3,retention_drop=3,continuation_j=3,continuation_next=2,continuation_drop=1,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 10361 | j=2,margin_j=0,margin_next=1,margin_jump=1,retention_j=22,retention_next=11,retention_drop=11,continuation_j=11,continuation_next=6,continuation_drop=5,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 10363 | j=3,margin_j=-1,margin_next=1,margin_jump=2,retention_j=11,retention_next=5,retention_drop=6,continuation_j=5,continuation_next=3,continuation_drop=2,retention_drop_minus_2_continuation_drop=2,cause=retention_drop_dominant |
| 10399 | j=2,margin_j=-1,margin_next=3,margin_jump=4,retention_j=15,retention_next=7,retention_drop=8,continuation_j=7,continuation_next=5,continuation_drop=2,retention_drop_minus_2_continuation_drop=4,cause=retention_drop_dominant |
| 10409 | j=2,margin_j=-1,margin_next=3,margin_jump=4,retention_j=15,retention_next=7,retention_drop=8,continuation_j=7,continuation_next=5,continuation_drop=2,retention_drop_minus_2_continuation_drop=4,cause=retention_drop_dominant |
| 10465 | j=2,margin_j=-2,margin_next=2,margin_jump=4,retention_j=22,retention_next=10,retention_drop=12,continuation_j=10,continuation_next=6,continuation_drop=4,retention_drop_minus_2_continuation_drop=4,cause=retention_drop_dominant |
| 10491 | j=2,margin_j=-3,margin_next=2,margin_jump=5,retention_j=15,retention_next=6,retention_drop=9,continuation_j=6,continuation_next=4,continuation_drop=2,retention_drop_minus_2_continuation_drop=5,cause=retention_drop_dominant |
| 10495 | j=2,margin_j=0,margin_next=3,margin_jump=3,retention_j=14,retention_next=7,retention_drop=7,continuation_j=7,continuation_next=5,continuation_drop=2,retention_drop_minus_2_continuation_drop=3,cause=retention_drop_dominant |
| 10543 | j=4,margin_j=0,margin_next=2,margin_jump=2,retention_j=12,retention_next=6,retention_drop=6,continuation_j=6,continuation_next=4,continuation_drop=2,retention_drop_minus_2_continuation_drop=2,cause=retention_drop_dominant |
| 10617 | j=3,margin_j=0,margin_next=1,margin_jump=1,retention_j=18,retention_next=9,retention_drop=9,continuation_j=9,continuation_next=5,continuation_drop=4,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 10651 | j=2,margin_j=-1,margin_next=1,margin_jump=2,retention_j=15,retention_next=7,retention_drop=8,continuation_j=7,continuation_next=4,continuation_drop=3,retention_drop_minus_2_continuation_drop=2,cause=retention_drop_dominant |
| 10687 | j=3,margin_j=0,margin_next=1,margin_jump=1,retention_j=10,retention_next=5,retention_drop=5,continuation_j=5,continuation_next=3,continuation_drop=2,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 10731 | j=2,margin_j=-1,margin_next=1,margin_jump=2,retention_j=7,retention_next=3,retention_drop=4,continuation_j=3,continuation_next=2,continuation_drop=1,retention_drop_minus_2_continuation_drop=2,cause=retention_drop_dominant |
| 10861 | j=4,margin_j=0,margin_next=1,margin_jump=1,retention_j=6,retention_next=3,retention_drop=3,continuation_j=3,continuation_next=2,continuation_drop=1,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 10863 | j=2,margin_j=0,margin_next=1,margin_jump=1,retention_j=18,retention_next=9,retention_drop=9,continuation_j=9,continuation_next=5,continuation_drop=4,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 10883 | j=2,margin_j=0,margin_next=1,margin_jump=1,retention_j=6,retention_next=3,retention_drop=3,continuation_j=3,continuation_next=2,continuation_drop=1,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 10909 | j=4,margin_j=0,margin_next=1,margin_jump=1,retention_j=6,retention_next=3,retention_drop=3,continuation_j=3,continuation_next=2,continuation_drop=1,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 10913 | j=2,margin_j=-2,margin_next=1,margin_jump=3,retention_j=24,retention_next=11,retention_drop=13,continuation_j=11,continuation_next=6,continuation_drop=5,retention_drop_minus_2_continuation_drop=3,cause=retention_drop_dominant |
| 10919 | j=2,margin_j=-1,margin_next=2,margin_jump=3,retention_j=33,retention_next=16,retention_drop=17,continuation_j=16,continuation_next=9,continuation_drop=7,retention_drop_minus_2_continuation_drop=3,cause=retention_drop_dominant |
| 10975 | j=2,margin_j=-1,margin_next=1,margin_jump=2,retention_j=7,retention_next=3,retention_drop=4,continuation_j=3,continuation_next=2,continuation_drop=1,retention_drop_minus_2_continuation_drop=2,cause=retention_drop_dominant |
| 10991 | j=2,margin_j=-1,margin_next=1,margin_jump=2,retention_j=15,retention_next=7,retention_drop=8,continuation_j=7,continuation_next=4,continuation_drop=3,retention_drop_minus_2_continuation_drop=2,cause=retention_drop_dominant |
| 11035 | j=2,margin_j=-3,margin_next=1,margin_jump=4,retention_j=17,retention_next=7,retention_drop=10,continuation_j=7,continuation_next=4,continuation_drop=3,retention_drop_minus_2_continuation_drop=4,cause=retention_drop_dominant |
| 11055 | j=2,margin_j=-1,margin_next=1,margin_jump=2,retention_j=15,retention_next=7,retention_drop=8,continuation_j=7,continuation_next=4,continuation_drop=3,retention_drop_minus_2_continuation_drop=2,cause=retention_drop_dominant |
| 11069 | j=3,margin_j=0,margin_next=1,margin_jump=1,retention_j=10,retention_next=5,retention_drop=5,continuation_j=5,continuation_next=3,continuation_drop=2,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 11091 | j=2,margin_j=-1,margin_next=1,margin_jump=2,retention_j=7,retention_next=3,retention_drop=4,continuation_j=3,continuation_next=2,continuation_drop=1,retention_drop_minus_2_continuation_drop=2,cause=retention_drop_dominant |
| 11103 | j=2,margin_j=-4,margin_next=1,margin_jump=5,retention_j=10,retention_next=3,retention_drop=7,continuation_j=3,continuation_next=2,continuation_drop=1,retention_drop_minus_2_continuation_drop=5,cause=retention_drop_dominant |
| 11105 | j=4,margin_j=0,margin_next=2,margin_jump=2,retention_j=12,retention_next=6,retention_drop=6,continuation_j=6,continuation_next=4,continuation_drop=2,retention_drop_minus_2_continuation_drop=2,cause=retention_drop_dominant |
| 11111 | j=3,margin_j=0,margin_next=1,margin_jump=1,retention_j=6,retention_next=3,retention_drop=3,continuation_j=3,continuation_next=2,continuation_drop=1,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 11131 | j=2,margin_j=-1,margin_next=1,margin_jump=2,retention_j=11,retention_next=5,retention_drop=6,continuation_j=5,continuation_next=3,continuation_drop=2,retention_drop_minus_2_continuation_drop=2,cause=retention_drop_dominant |
| 11135 | j=4,margin_j=-4,margin_next=1,margin_jump=5,retention_j=10,retention_next=3,retention_drop=7,continuation_j=3,continuation_next=2,continuation_drop=1,retention_drop_minus_2_continuation_drop=5,cause=retention_drop_dominant |
| 11141 | j=2,margin_j=-2,margin_next=1,margin_jump=3,retention_j=8,retention_next=3,retention_drop=5,continuation_j=3,continuation_next=2,continuation_drop=1,retention_drop_minus_2_continuation_drop=3,cause=retention_drop_dominant |
| 11147 | j=2,margin_j=-3,margin_next=1,margin_jump=4,retention_j=9,retention_next=3,retention_drop=6,continuation_j=3,continuation_next=2,continuation_drop=1,retention_drop_minus_2_continuation_drop=4,cause=retention_drop_dominant |
| 11167 | j=2,margin_j=-4,margin_next=1,margin_jump=5,retention_j=10,retention_next=3,retention_drop=7,continuation_j=3,continuation_next=2,continuation_drop=1,retention_drop_minus_2_continuation_drop=5,cause=retention_drop_dominant |
| 11199 | j=3,margin_j=0,margin_next=1,margin_jump=1,retention_j=6,retention_next=3,retention_drop=3,continuation_j=3,continuation_next=2,continuation_drop=1,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 11217 | j=4,margin_j=0,margin_next=1,margin_jump=1,retention_j=6,retention_next=3,retention_drop=3,continuation_j=3,continuation_next=2,continuation_drop=1,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 11257 | j=3,margin_j=0,margin_next=1,margin_jump=1,retention_j=10,retention_next=5,retention_drop=5,continuation_j=5,continuation_next=3,continuation_drop=2,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 11261 | j=4,margin_j=0,margin_next=1,margin_jump=1,retention_j=10,retention_next=5,retention_drop=5,continuation_j=5,continuation_next=3,continuation_drop=2,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 11289 | j=4,margin_j=-1,margin_next=2,margin_jump=3,retention_j=13,retention_next=6,retention_drop=7,continuation_j=6,continuation_next=4,continuation_drop=2,retention_drop_minus_2_continuation_drop=3,cause=retention_drop_dominant |
| 11291 | j=2,margin_j=-3,margin_next=1,margin_jump=4,retention_j=25,retention_next=11,retention_drop=14,continuation_j=11,continuation_next=6,continuation_drop=5,retention_drop_minus_2_continuation_drop=4,cause=retention_drop_dominant |
| 11425 | j=2,margin_j=-1,margin_next=1,margin_jump=2,retention_j=11,retention_next=5,retention_drop=6,continuation_j=5,continuation_next=3,continuation_drop=2,retention_drop_minus_2_continuation_drop=2,cause=retention_drop_dominant |
| 11455 | j=3,margin_j=0,margin_next=1,margin_jump=1,retention_j=10,retention_next=5,retention_drop=5,continuation_j=5,continuation_next=3,continuation_drop=2,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 11499 | j=3,margin_j=-3,margin_next=1,margin_jump=4,retention_j=13,retention_next=5,retention_drop=8,continuation_j=5,continuation_next=3,continuation_drop=2,retention_drop_minus_2_continuation_drop=4,cause=retention_drop_dominant |
| 11515 | j=2,margin_j=-8,margin_next=1,margin_jump=9,retention_j=18,retention_next=5,retention_drop=13,continuation_j=5,continuation_next=3,continuation_drop=2,retention_drop_minus_2_continuation_drop=9,cause=retention_drop_dominant |
| 11519 | j=2,margin_j=0,margin_next=2,margin_jump=2,retention_j=20,retention_next=10,retention_drop=10,continuation_j=10,continuation_next=6,continuation_drop=4,retention_drop_minus_2_continuation_drop=2,cause=retention_drop_dominant |
| 11523 | j=3,margin_j=0,margin_next=1,margin_jump=1,retention_j=22,retention_next=11,retention_drop=11,continuation_j=11,continuation_next=6,continuation_drop=5,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 11561 | j=2,margin_j=0,margin_next=1,margin_jump=1,retention_j=10,retention_next=5,retention_drop=5,continuation_j=5,continuation_next=3,continuation_drop=2,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 11577 | j=2,margin_j=-1,margin_next=2,margin_jump=3,retention_j=17,retention_next=8,retention_drop=9,continuation_j=8,continuation_next=5,continuation_drop=3,retention_drop_minus_2_continuation_drop=3,cause=retention_drop_dominant |
| 11653 | j=4,margin_j=0,margin_next=1,margin_jump=1,retention_j=6,retention_next=3,retention_drop=3,continuation_j=3,continuation_next=2,continuation_drop=1,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 11659 | j=3,margin_j=-1,margin_next=1,margin_jump=2,retention_j=11,retention_next=5,retention_drop=6,continuation_j=5,continuation_next=3,continuation_drop=2,retention_drop_minus_2_continuation_drop=2,cause=retention_drop_dominant |
| 11681 | j=2,margin_j=0,margin_next=2,margin_jump=2,retention_j=8,retention_next=4,retention_drop=4,continuation_j=4,continuation_next=3,continuation_drop=1,retention_drop_minus_2_continuation_drop=2,cause=retention_drop_dominant |
| 11689 | j=2,margin_j=-2,margin_next=1,margin_jump=3,retention_j=12,retention_next=5,retention_drop=7,continuation_j=5,continuation_next=3,continuation_drop=2,retention_drop_minus_2_continuation_drop=3,cause=retention_drop_dominant |
| 11711 | j=2,margin_j=-2,margin_next=2,margin_jump=4,retention_j=14,retention_next=6,retention_drop=8,continuation_j=6,continuation_next=4,continuation_drop=2,retention_drop_minus_2_continuation_drop=4,cause=retention_drop_dominant |
| 11743 | j=2,margin_j=0,margin_next=1,margin_jump=1,retention_j=14,retention_next=7,retention_drop=7,continuation_j=7,continuation_next=4,continuation_drop=3,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 11775 | j=2,margin_j=0,margin_next=3,margin_jump=3,retention_j=22,retention_next=11,retention_drop=11,continuation_j=11,continuation_next=7,continuation_drop=4,retention_drop_minus_2_continuation_drop=3,cause=retention_drop_dominant |
| 11803 | j=2,margin_j=-2,margin_next=2,margin_jump=4,retention_j=14,retention_next=6,retention_drop=8,continuation_j=6,continuation_next=4,continuation_drop=2,retention_drop_minus_2_continuation_drop=4,cause=retention_drop_dominant |
| 11823 | j=4,margin_j=-1,margin_next=1,margin_jump=2,retention_j=7,retention_next=3,retention_drop=4,continuation_j=3,continuation_next=2,continuation_drop=1,retention_drop_minus_2_continuation_drop=2,cause=retention_drop_dominant |
| 11827 | j=3,margin_j=0,margin_next=1,margin_jump=1,retention_j=6,retention_next=3,retention_drop=3,continuation_j=3,continuation_next=2,continuation_drop=1,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 11945 | j=4,margin_j=0,margin_next=1,margin_jump=1,retention_j=10,retention_next=5,retention_drop=5,continuation_j=5,continuation_next=3,continuation_drop=2,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 11977 | j=3,margin_j=0,margin_next=1,margin_jump=1,retention_j=22,retention_next=11,retention_drop=11,continuation_j=11,continuation_next=6,continuation_drop=5,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 11983 | j=2,margin_j=0,margin_next=1,margin_jump=1,retention_j=14,retention_next=7,retention_drop=7,continuation_j=7,continuation_next=4,continuation_drop=3,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 12031 | j=2,margin_j=0,margin_next=1,margin_jump=1,retention_j=18,retention_next=9,retention_drop=9,continuation_j=9,continuation_next=5,continuation_drop=4,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 12059 | j=4,margin_j=0,margin_next=2,margin_jump=2,retention_j=12,retention_next=6,retention_drop=6,continuation_j=6,continuation_next=4,continuation_drop=2,retention_drop_minus_2_continuation_drop=2,cause=retention_drop_dominant |
| 12073 | j=2,margin_j=0,margin_next=1,margin_jump=1,retention_j=6,retention_next=3,retention_drop=3,continuation_j=3,continuation_next=2,continuation_drop=1,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 12143 | j=4,margin_j=0,margin_next=1,margin_jump=1,retention_j=6,retention_next=3,retention_drop=3,continuation_j=3,continuation_next=2,continuation_drop=1,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 12221 | j=3,margin_j=0,margin_next=1,margin_jump=1,retention_j=10,retention_next=5,retention_drop=5,continuation_j=5,continuation_next=3,continuation_drop=2,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 12223 | j=2,margin_j=-1,margin_next=1,margin_jump=2,retention_j=15,retention_next=7,retention_drop=8,continuation_j=7,continuation_next=4,continuation_drop=3,retention_drop_minus_2_continuation_drop=2,cause=retention_drop_dominant |
| 12263 | j=3,margin_j=0,margin_next=1,margin_jump=1,retention_j=18,retention_next=9,retention_drop=9,continuation_j=9,continuation_next=5,continuation_drop=4,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 12275 | j=4,margin_j=0,margin_next=1,margin_jump=1,retention_j=6,retention_next=3,retention_drop=3,continuation_j=3,continuation_next=2,continuation_drop=1,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 12279 | j=3,margin_j=0,margin_next=2,margin_jump=2,retention_j=12,retention_next=6,retention_drop=6,continuation_j=6,continuation_next=4,continuation_drop=2,retention_drop_minus_2_continuation_drop=2,cause=retention_drop_dominant |
| 12281 | j=3,margin_j=-1,margin_next=1,margin_jump=2,retention_j=11,retention_next=5,retention_drop=6,continuation_j=5,continuation_next=3,continuation_drop=2,retention_drop_minus_2_continuation_drop=2,cause=retention_drop_dominant |
| 12319 | j=2,margin_j=-7,margin_next=1,margin_jump=8,retention_j=13,retention_next=3,retention_drop=10,continuation_j=3,continuation_next=2,continuation_drop=1,retention_drop_minus_2_continuation_drop=8,cause=retention_drop_dominant |
| 12399 | j=3,margin_j=0,margin_next=2,margin_jump=2,retention_j=20,retention_next=10,retention_drop=10,continuation_j=10,continuation_next=6,continuation_drop=4,retention_drop_minus_2_continuation_drop=2,cause=retention_drop_dominant |
| 12415 | j=2,margin_j=-2,margin_next=1,margin_jump=3,retention_j=16,retention_next=7,retention_drop=9,continuation_j=7,continuation_next=4,continuation_drop=3,retention_drop_minus_2_continuation_drop=3,cause=retention_drop_dominant |
| 12463 | j=4,margin_j=0,margin_next=1,margin_jump=1,retention_j=14,retention_next=7,retention_drop=7,continuation_j=7,continuation_next=4,continuation_drop=3,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 12495 | j=4,margin_j=0,margin_next=2,margin_jump=2,retention_j=12,retention_next=6,retention_drop=6,continuation_j=6,continuation_next=4,continuation_drop=2,retention_drop_minus_2_continuation_drop=2,cause=retention_drop_dominant |
| 12523 | j=2,margin_j=0,margin_next=1,margin_jump=1,retention_j=10,retention_next=5,retention_drop=5,continuation_j=5,continuation_next=3,continuation_drop=2,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 12541 | j=2,margin_j=-2,margin_next=1,margin_jump=3,retention_j=8,retention_next=3,retention_drop=5,continuation_j=3,continuation_next=2,continuation_drop=1,retention_drop_minus_2_continuation_drop=3,cause=retention_drop_dominant |
| 12571 | j=2,margin_j=-2,margin_next=2,margin_jump=4,retention_j=10,retention_next=4,retention_drop=6,continuation_j=4,continuation_next=3,continuation_drop=1,retention_drop_minus_2_continuation_drop=4,cause=retention_drop_dominant |
| 12583 | j=3,margin_j=0,margin_next=1,margin_jump=1,retention_j=18,retention_next=9,retention_drop=9,continuation_j=9,continuation_next=5,continuation_drop=4,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 12621 | j=4,margin_j=0,margin_next=1,margin_jump=1,retention_j=6,retention_next=3,retention_drop=3,continuation_j=3,continuation_next=2,continuation_drop=1,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 12665 | j=3,margin_j=0,margin_next=1,margin_jump=1,retention_j=10,retention_next=5,retention_drop=5,continuation_j=5,continuation_next=3,continuation_drop=2,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 12671 | j=4,margin_j=0,margin_next=1,margin_jump=1,retention_j=10,retention_next=5,retention_drop=5,continuation_j=5,continuation_next=3,continuation_drop=2,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 12691 | j=2,margin_j=0,margin_next=1,margin_jump=1,retention_j=14,retention_next=7,retention_drop=7,continuation_j=7,continuation_next=4,continuation_drop=3,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 12701 | j=4,margin_j=-1,margin_next=2,margin_jump=3,retention_j=13,retention_next=6,retention_drop=7,continuation_j=6,continuation_next=4,continuation_drop=2,retention_drop_minus_2_continuation_drop=3,cause=retention_drop_dominant |
| 12703 | j=2,margin_j=-2,margin_next=1,margin_jump=3,retention_j=24,retention_next=11,retention_drop=13,continuation_j=11,continuation_next=6,continuation_drop=5,retention_drop_minus_2_continuation_drop=3,cause=retention_drop_dominant |
| 12807 | j=3,margin_j=0,margin_next=1,margin_jump=1,retention_j=6,retention_next=3,retention_drop=3,continuation_j=3,continuation_next=2,continuation_drop=1,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 12867 | j=2,margin_j=0,margin_next=2,margin_jump=2,retention_j=8,retention_next=4,retention_drop=4,continuation_j=4,continuation_next=3,continuation_drop=1,retention_drop_minus_2_continuation_drop=2,cause=retention_drop_dominant |
| 12873 | j=3,margin_j=-1,margin_next=1,margin_jump=2,retention_j=11,retention_next=5,retention_drop=6,continuation_j=5,continuation_next=3,continuation_drop=2,retention_drop_minus_2_continuation_drop=2,cause=retention_drop_dominant |
| 12927 | j=2,margin_j=-1,margin_next=2,margin_jump=3,retention_j=13,retention_next=6,retention_drop=7,continuation_j=6,continuation_next=4,continuation_drop=2,retention_drop_minus_2_continuation_drop=3,cause=retention_drop_dominant |
| 12929 | j=4,margin_j=-1,margin_next=1,margin_jump=2,retention_j=7,retention_next=3,retention_drop=4,continuation_j=3,continuation_next=2,continuation_drop=1,retention_drop_minus_2_continuation_drop=2,cause=retention_drop_dominant |
| 12937 | j=3,margin_j=-3,margin_next=1,margin_jump=4,retention_j=13,retention_next=5,retention_drop=8,continuation_j=5,continuation_next=3,continuation_drop=2,retention_drop_minus_2_continuation_drop=4,cause=retention_drop_dominant |
| 12955 | j=2,margin_j=-7,margin_next=1,margin_jump=8,retention_j=17,retention_next=5,retention_drop=12,continuation_j=5,continuation_next=3,continuation_drop=2,retention_drop_minus_2_continuation_drop=8,cause=retention_drop_dominant |
| 12965 | j=3,margin_j=0,margin_next=1,margin_jump=1,retention_j=22,retention_next=11,retention_drop=11,continuation_j=11,continuation_next=6,continuation_drop=5,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 13025 | j=2,margin_j=0,margin_next=2,margin_jump=2,retention_j=16,retention_next=8,retention_drop=8,continuation_j=8,continuation_next=5,continuation_drop=3,retention_drop_minus_2_continuation_drop=2,cause=retention_drop_dominant |
| 13055 | j=2,margin_j=0,margin_next=2,margin_jump=2,retention_j=20,retention_next=10,retention_drop=10,continuation_j=10,continuation_next=6,continuation_drop=4,retention_drop_minus_2_continuation_drop=2,cause=retention_drop_dominant |
| 13115 | j=2,margin_j=0,margin_next=2,margin_jump=2,retention_j=20,retention_next=10,retention_drop=10,continuation_j=10,continuation_next=6,continuation_drop=4,retention_drop_minus_2_continuation_drop=2,cause=retention_drop_dominant |
| 13117 | j=3,margin_j=-1,margin_next=1,margin_jump=2,retention_j=11,retention_next=5,retention_drop=6,continuation_j=5,continuation_next=3,continuation_drop=2,retention_drop_minus_2_continuation_drop=2,cause=retention_drop_dominant |
| 13161 | j=4,margin_j=-1,margin_next=2,margin_jump=3,retention_j=13,retention_next=6,retention_drop=7,continuation_j=6,continuation_next=4,continuation_drop=2,retention_drop_minus_2_continuation_drop=3,cause=retention_drop_dominant |
| 13183 | j=4,margin_j=0,margin_next=1,margin_jump=1,retention_j=10,retention_next=5,retention_drop=5,continuation_j=5,continuation_next=3,continuation_drop=2,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 13201 | j=2,margin_j=-2,margin_next=1,margin_jump=3,retention_j=8,retention_next=3,retention_drop=5,continuation_j=3,continuation_next=2,continuation_drop=1,retention_drop_minus_2_continuation_drop=3,cause=retention_drop_dominant |
| 13203 | j=2,margin_j=-4,margin_next=1,margin_jump=5,retention_j=10,retention_next=3,retention_drop=7,continuation_j=3,continuation_next=2,continuation_drop=1,retention_drop_minus_2_continuation_drop=5,cause=retention_drop_dominant |
| 13211 | j=2,margin_j=-2,margin_next=1,margin_jump=3,retention_j=12,retention_next=5,retention_drop=7,continuation_j=5,continuation_next=3,continuation_drop=2,retention_drop_minus_2_continuation_drop=3,cause=retention_drop_dominant |
| 13255 | j=3,margin_j=0,margin_next=1,margin_jump=1,retention_j=18,retention_next=9,retention_drop=9,continuation_j=9,continuation_next=5,continuation_drop=4,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 13279 | j=2,margin_j=-1,margin_next=2,margin_jump=3,retention_j=13,retention_next=6,retention_drop=7,continuation_j=6,continuation_next=4,continuation_drop=2,retention_drop_minus_2_continuation_drop=3,cause=retention_drop_dominant |
| 13293 | j=2,margin_j=-1,margin_next=1,margin_jump=2,retention_j=19,retention_next=9,retention_drop=10,continuation_j=9,continuation_next=5,continuation_drop=4,retention_drop_minus_2_continuation_drop=2,cause=retention_drop_dominant |
| 13309 | j=2,margin_j=0,margin_next=2,margin_jump=2,retention_j=12,retention_next=6,retention_drop=6,continuation_j=6,continuation_next=4,continuation_drop=2,retention_drop_minus_2_continuation_drop=2,cause=retention_drop_dominant |
| 13345 | j=4,margin_j=0,margin_next=1,margin_jump=1,retention_j=10,retention_next=5,retention_drop=5,continuation_j=5,continuation_next=3,continuation_drop=2,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 13481 | j=2,margin_j=0,margin_next=2,margin_jump=2,retention_j=12,retention_next=6,retention_drop=6,continuation_j=6,continuation_next=4,continuation_drop=2,retention_drop_minus_2_continuation_drop=2,cause=retention_drop_dominant |
| 13503 | j=4,margin_j=-1,margin_next=1,margin_jump=2,retention_j=11,retention_next=5,retention_drop=6,continuation_j=5,continuation_next=3,continuation_drop=2,retention_drop_minus_2_continuation_drop=2,cause=retention_drop_dominant |
| 13507 | j=2,margin_j=0,margin_next=2,margin_jump=2,retention_j=12,retention_next=6,retention_drop=6,continuation_j=6,continuation_next=4,continuation_drop=2,retention_drop_minus_2_continuation_drop=2,cause=retention_drop_dominant |
| 13543 | j=3,margin_j=0,margin_next=3,margin_jump=3,retention_j=10,retention_next=5,retention_drop=5,continuation_j=5,continuation_next=4,continuation_drop=1,retention_drop_minus_2_continuation_drop=3,cause=retention_drop_dominant |
| 13567 | j=4,margin_j=0,margin_next=2,margin_jump=2,retention_j=12,retention_next=6,retention_drop=6,continuation_j=6,continuation_next=4,continuation_drop=2,retention_drop_minus_2_continuation_drop=2,cause=retention_drop_dominant |
| 13587 | j=2,margin_j=0,margin_next=2,margin_jump=2,retention_j=12,retention_next=6,retention_drop=6,continuation_j=6,continuation_next=4,continuation_drop=2,retention_drop_minus_2_continuation_drop=2,cause=retention_drop_dominant |
| 13595 | j=2,margin_j=-3,margin_next=1,margin_jump=4,retention_j=13,retention_next=5,retention_drop=8,continuation_j=5,continuation_next=3,continuation_drop=2,retention_drop_minus_2_continuation_drop=4,cause=retention_drop_dominant |
| 13647 | j=2,margin_j=-6,margin_next=1,margin_jump=7,retention_j=20,retention_next=7,retention_drop=13,continuation_j=7,continuation_next=4,continuation_drop=3,retention_drop_minus_2_continuation_drop=7,cause=retention_drop_dominant |
| 13651 | j=2,margin_j=0,margin_next=3,margin_jump=3,retention_j=22,retention_next=11,retention_drop=11,continuation_j=11,continuation_next=7,continuation_drop=4,retention_drop_minus_2_continuation_drop=3,cause=retention_drop_dominant |
| 13655 | j=3,margin_j=-1,margin_next=1,margin_jump=2,retention_j=23,retention_next=11,retention_drop=12,continuation_j=11,continuation_next=6,continuation_drop=5,retention_drop_minus_2_continuation_drop=2,cause=retention_drop_dominant |
| 13663 | j=2,margin_j=0,margin_next=1,margin_jump=1,retention_j=6,retention_next=3,retention_drop=3,continuation_j=3,continuation_next=2,continuation_drop=1,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 13671 | j=2,margin_j=-5,margin_next=1,margin_jump=6,retention_j=19,retention_next=7,retention_drop=12,continuation_j=7,continuation_next=4,continuation_drop=3,retention_drop_minus_2_continuation_drop=6,cause=retention_drop_dominant |
| 13811 | j=4,margin_j=0,margin_next=1,margin_jump=1,retention_j=6,retention_next=3,retention_drop=3,continuation_j=3,continuation_next=2,continuation_drop=1,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 13815 | j=3,margin_j=0,margin_next=2,margin_jump=2,retention_j=12,retention_next=6,retention_drop=6,continuation_j=6,continuation_next=4,continuation_drop=2,retention_drop_minus_2_continuation_drop=2,cause=retention_drop_dominant |
| 13817 | j=3,margin_j=-1,margin_next=1,margin_jump=2,retention_j=11,retention_next=5,retention_drop=6,continuation_j=5,continuation_next=3,continuation_drop=2,retention_drop_minus_2_continuation_drop=2,cause=retention_drop_dominant |
| 13843 | j=2,margin_j=-2,margin_next=2,margin_jump=4,retention_j=10,retention_next=4,retention_drop=6,continuation_j=4,continuation_next=3,continuation_drop=1,retention_drop_minus_2_continuation_drop=4,cause=retention_drop_dominant |
| 13865 | j=2,margin_j=-1,margin_next=3,margin_jump=4,retention_j=15,retention_next=7,retention_drop=8,continuation_j=7,continuation_next=5,continuation_drop=2,retention_drop_minus_2_continuation_drop=4,cause=retention_drop_dominant |
| 13879 | j=2,margin_j=-2,margin_next=1,margin_jump=3,retention_j=16,retention_next=7,retention_drop=9,continuation_j=7,continuation_next=4,continuation_drop=3,retention_drop_minus_2_continuation_drop=3,cause=retention_drop_dominant |
| 13953 | j=2,margin_j=-2,margin_next=2,margin_jump=4,retention_j=22,retention_next=10,retention_drop=12,continuation_j=10,continuation_next=6,continuation_drop=4,retention_drop_minus_2_continuation_drop=4,cause=retention_drop_dominant |
| 13993 | j=2,margin_j=0,margin_next=3,margin_jump=3,retention_j=14,retention_next=7,retention_drop=7,continuation_j=7,continuation_next=5,continuation_drop=2,retention_drop_minus_2_continuation_drop=3,cause=retention_drop_dominant |
| 14013 | j=3,margin_j=0,margin_next=2,margin_jump=2,retention_j=8,retention_next=4,retention_drop=4,continuation_j=4,continuation_next=3,continuation_drop=1,retention_drop_minus_2_continuation_drop=2,cause=retention_drop_dominant |
| 14057 | j=4,margin_j=0,margin_next=2,margin_jump=2,retention_j=12,retention_next=6,retention_drop=6,continuation_j=6,continuation_next=4,continuation_drop=2,retention_drop_minus_2_continuation_drop=2,cause=retention_drop_dominant |
| 14143 | j=2,margin_j=-1,margin_next=2,margin_jump=3,retention_j=9,retention_next=4,retention_drop=5,continuation_j=4,continuation_next=3,continuation_drop=1,retention_drop_minus_2_continuation_drop=3,cause=retention_drop_dominant |
| 14201 | j=2,margin_j=-1,margin_next=1,margin_jump=2,retention_j=15,retention_next=7,retention_drop=8,continuation_j=7,continuation_next=4,continuation_drop=3,retention_drop_minus_2_continuation_drop=2,cause=retention_drop_dominant |
| 14249 | j=3,margin_j=0,margin_next=1,margin_jump=1,retention_j=10,retention_next=5,retention_drop=5,continuation_j=5,continuation_next=3,continuation_drop=2,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 14291 | j=4,margin_j=0,margin_next=2,margin_jump=2,retention_j=12,retention_next=6,retention_drop=6,continuation_j=6,continuation_next=4,continuation_drop=2,retention_drop_minus_2_continuation_drop=2,cause=retention_drop_dominant |
| 14391 | j=4,margin_j=0,margin_next=1,margin_jump=1,retention_j=6,retention_next=3,retention_drop=3,continuation_j=3,continuation_next=2,continuation_drop=1,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 14481 | j=4,margin_j=0,margin_next=1,margin_jump=1,retention_j=6,retention_next=3,retention_drop=3,continuation_j=3,continuation_next=2,continuation_drop=1,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 14483 | j=3,margin_j=0,margin_next=1,margin_jump=1,retention_j=10,retention_next=5,retention_drop=5,continuation_j=5,continuation_next=3,continuation_drop=2,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 14545 | j=4,margin_j=0,margin_next=1,margin_jump=1,retention_j=6,retention_next=3,retention_drop=3,continuation_j=3,continuation_next=2,continuation_drop=1,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 14547 | j=4,margin_j=0,margin_next=1,margin_jump=1,retention_j=6,retention_next=3,retention_drop=3,continuation_j=3,continuation_next=2,continuation_drop=1,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 14551 | j=3,margin_j=0,margin_next=2,margin_jump=2,retention_j=12,retention_next=6,retention_drop=6,continuation_j=6,continuation_next=4,continuation_drop=2,retention_drop_minus_2_continuation_drop=2,cause=retention_drop_dominant |
| 14555 | j=3,margin_j=-2,margin_next=1,margin_jump=3,retention_j=12,retention_next=5,retention_drop=7,continuation_j=5,continuation_next=3,continuation_drop=2,retention_drop_minus_2_continuation_drop=3,cause=retention_drop_dominant |
| 14575 | j=2,margin_j=-6,margin_next=1,margin_jump=7,retention_j=16,retention_next=5,retention_drop=11,continuation_j=5,continuation_next=3,continuation_drop=2,retention_drop_minus_2_continuation_drop=7,cause=retention_drop_dominant |
| 14633 | j=2,margin_j=-1,margin_next=1,margin_jump=2,retention_j=7,retention_next=3,retention_drop=4,continuation_j=3,continuation_next=2,continuation_drop=1,retention_drop_minus_2_continuation_drop=2,cause=retention_drop_dominant |
| 14655 | j=2,margin_j=0,margin_next=2,margin_jump=2,retention_j=16,retention_next=8,retention_drop=8,continuation_j=8,continuation_next=5,continuation_drop=3,retention_drop_minus_2_continuation_drop=2,cause=retention_drop_dominant |
| 14695 | j=3,margin_j=0,margin_next=3,margin_jump=3,retention_j=22,retention_next=11,retention_drop=11,continuation_j=11,continuation_next=7,continuation_drop=4,retention_drop_minus_2_continuation_drop=3,cause=retention_drop_dominant |
| 14713 | j=2,margin_j=-3,margin_next=1,margin_jump=4,retention_j=17,retention_next=7,retention_drop=10,continuation_j=7,continuation_next=4,continuation_drop=3,retention_drop_minus_2_continuation_drop=4,cause=retention_drop_dominant |
| 14757 | j=4,margin_j=0,margin_next=1,margin_jump=1,retention_j=6,retention_next=3,retention_drop=3,continuation_j=3,continuation_next=2,continuation_drop=1,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 14783 | j=3,margin_j=-1,margin_next=1,margin_jump=2,retention_j=7,retention_next=3,retention_drop=4,continuation_j=3,continuation_next=2,continuation_drop=1,retention_drop_minus_2_continuation_drop=2,cause=retention_drop_dominant |
| 14787 | j=2,margin_j=0,margin_next=2,margin_jump=2,retention_j=8,retention_next=4,retention_drop=4,continuation_j=4,continuation_next=3,continuation_drop=1,retention_drop_minus_2_continuation_drop=2,cause=retention_drop_dominant |
| 14807 | j=4,margin_j=0,margin_next=2,margin_jump=2,retention_j=12,retention_next=6,retention_drop=6,continuation_j=6,continuation_next=4,continuation_drop=2,retention_drop_minus_2_continuation_drop=2,cause=retention_drop_dominant |
| 14841 | j=2,margin_j=-1,margin_next=1,margin_jump=2,retention_j=11,retention_next=5,retention_drop=6,continuation_j=5,continuation_next=3,continuation_drop=2,retention_drop_minus_2_continuation_drop=2,cause=retention_drop_dominant |
| 14853 | j=2,margin_j=-2,margin_next=1,margin_jump=3,retention_j=8,retention_next=3,retention_drop=5,continuation_j=3,continuation_next=2,continuation_drop=1,retention_drop_minus_2_continuation_drop=3,cause=retention_drop_dominant |
| 14863 | j=2,margin_j=-1,margin_next=1,margin_jump=2,retention_j=11,retention_next=5,retention_drop=6,continuation_j=5,continuation_next=3,continuation_drop=2,retention_drop_minus_2_continuation_drop=2,cause=retention_drop_dominant |
| 14889 | j=2,margin_j=-4,margin_next=1,margin_jump=5,retention_j=10,retention_next=3,retention_drop=7,continuation_j=3,continuation_next=2,continuation_drop=1,retention_drop_minus_2_continuation_drop=5,cause=retention_drop_dominant |
| 14943 | j=2,margin_j=0,margin_next=1,margin_jump=1,retention_j=10,retention_next=5,retention_drop=5,continuation_j=5,continuation_next=3,continuation_drop=2,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 14957 | j=2,margin_j=0,margin_next=1,margin_jump=1,retention_j=18,retention_next=9,retention_drop=9,continuation_j=9,continuation_next=5,continuation_drop=4,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 15009 | j=3,margin_j=0,margin_next=1,margin_jump=1,retention_j=10,retention_next=5,retention_drop=5,continuation_j=5,continuation_next=3,continuation_drop=2,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 15013 | j=3,margin_j=0,margin_next=1,margin_jump=1,retention_j=22,retention_next=11,retention_drop=11,continuation_j=11,continuation_next=6,continuation_drop=5,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 15015 | j=3,margin_j=0,margin_next=1,margin_jump=1,retention_j=10,retention_next=5,retention_drop=5,continuation_j=5,continuation_next=3,continuation_drop=2,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 15051 | j=4,margin_j=-1,margin_next=2,margin_jump=3,retention_j=13,retention_next=6,retention_drop=7,continuation_j=6,continuation_next=4,continuation_drop=2,retention_drop_minus_2_continuation_drop=3,cause=retention_drop_dominant |
| 15091 | j=2,margin_j=-3,margin_next=1,margin_jump=4,retention_j=9,retention_next=3,retention_drop=6,continuation_j=3,continuation_next=2,continuation_drop=1,retention_drop_minus_2_continuation_drop=4,cause=retention_drop_dominant |
| 15099 | j=2,margin_j=-2,margin_next=2,margin_jump=4,retention_j=18,retention_next=8,retention_drop=10,continuation_j=8,continuation_next=5,continuation_drop=3,retention_drop_minus_2_continuation_drop=4,cause=retention_drop_dominant |
| 15167 | j=2,margin_j=-1,margin_next=1,margin_jump=2,retention_j=11,retention_next=5,retention_drop=6,continuation_j=5,continuation_next=3,continuation_drop=2,retention_drop_minus_2_continuation_drop=2,cause=retention_drop_dominant |
| 15197 | j=2,margin_j=0,margin_next=3,margin_jump=3,retention_j=10,retention_next=5,retention_drop=5,continuation_j=5,continuation_next=4,continuation_drop=1,retention_drop_minus_2_continuation_drop=3,cause=retention_drop_dominant |
| 15233 | j=2,margin_j=-1,margin_next=1,margin_jump=2,retention_j=11,retention_next=5,retention_drop=6,continuation_j=5,continuation_next=3,continuation_drop=2,retention_drop_minus_2_continuation_drop=2,cause=retention_drop_dominant |
| 15273 | j=3,margin_j=0,margin_next=1,margin_jump=1,retention_j=10,retention_next=5,retention_drop=5,continuation_j=5,continuation_next=3,continuation_drop=2,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 15295 | j=2,margin_j=-2,margin_next=1,margin_jump=3,retention_j=12,retention_next=5,retention_drop=7,continuation_j=5,continuation_next=3,continuation_drop=2,retention_drop_minus_2_continuation_drop=3,cause=retention_drop_dominant |
| 15303 | j=3,margin_j=0,margin_next=1,margin_jump=1,retention_j=6,retention_next=3,retention_drop=3,continuation_j=3,continuation_next=2,continuation_drop=1,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 15323 | j=4,margin_j=-1,margin_next=1,margin_jump=2,retention_j=7,retention_next=3,retention_drop=4,continuation_j=3,continuation_next=2,continuation_drop=1,retention_drop_minus_2_continuation_drop=2,cause=retention_drop_dominant |
| 15353 | j=2,margin_j=-8,margin_next=1,margin_jump=9,retention_j=18,retention_next=5,retention_drop=13,continuation_j=5,continuation_next=3,continuation_drop=2,retention_drop_minus_2_continuation_drop=9,cause=retention_drop_dominant |
| 15357 | j=3,margin_j=0,margin_next=1,margin_jump=1,retention_j=10,retention_next=5,retention_drop=5,continuation_j=5,continuation_next=3,continuation_drop=2,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 15363 | j=3,margin_j=0,margin_next=1,margin_jump=1,retention_j=22,retention_next=11,retention_drop=11,continuation_j=11,continuation_next=6,continuation_drop=5,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 15387 | j=2,margin_j=-2,margin_next=2,margin_jump=4,retention_j=22,retention_next=10,retention_drop=12,continuation_j=10,continuation_next=6,continuation_drop=4,retention_drop_minus_2_continuation_drop=4,cause=retention_drop_dominant |
| 15471 | j=2,margin_j=-3,margin_next=1,margin_jump=4,retention_j=13,retention_next=5,retention_drop=8,continuation_j=5,continuation_next=3,continuation_drop=2,retention_drop_minus_2_continuation_drop=4,cause=retention_drop_dominant |
| 15537 | j=4,margin_j=0,margin_next=1,margin_jump=1,retention_j=6,retention_next=3,retention_drop=3,continuation_j=3,continuation_next=2,continuation_drop=1,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 15539 | j=4,margin_j=0,margin_next=1,margin_jump=1,retention_j=6,retention_next=3,retention_drop=3,continuation_j=3,continuation_next=2,continuation_drop=1,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 15543 | j=2,margin_j=0,margin_next=1,margin_jump=1,retention_j=22,retention_next=11,retention_drop=11,continuation_j=11,continuation_next=6,continuation_drop=5,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 15545 | j=3,margin_j=-1,margin_next=1,margin_jump=2,retention_j=11,retention_next=5,retention_drop=6,continuation_j=5,continuation_next=3,continuation_drop=2,retention_drop_minus_2_continuation_drop=2,cause=retention_drop_dominant |
| 15575 | j=2,margin_j=0,margin_next=1,margin_jump=1,retention_j=10,retention_next=5,retention_drop=5,continuation_j=5,continuation_next=3,continuation_drop=2,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 15585 | j=2,margin_j=-2,margin_next=1,margin_jump=3,retention_j=12,retention_next=5,retention_drop=7,continuation_j=5,continuation_next=3,continuation_drop=2,retention_drop_minus_2_continuation_drop=3,cause=retention_drop_dominant |
| 15599 | j=2,margin_j=-2,margin_next=2,margin_jump=4,retention_j=14,retention_next=6,retention_drop=8,continuation_j=6,continuation_next=4,continuation_drop=2,retention_drop_minus_2_continuation_drop=4,cause=retention_drop_dominant |
| 15615 | j=2,margin_j=-1,margin_next=3,margin_jump=4,retention_j=15,retention_next=7,retention_drop=8,continuation_j=7,continuation_next=5,continuation_drop=2,retention_drop_minus_2_continuation_drop=4,cause=retention_drop_dominant |
| 15647 | j=2,margin_j=0,margin_next=2,margin_jump=2,retention_j=12,retention_next=6,retention_drop=6,continuation_j=6,continuation_next=4,continuation_drop=2,retention_drop_minus_2_continuation_drop=2,cause=retention_drop_dominant |
| 15657 | j=2,margin_j=0,margin_next=1,margin_jump=1,retention_j=14,retention_next=7,retention_drop=7,continuation_j=7,continuation_next=4,continuation_drop=3,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 15679 | j=3,margin_j=0,margin_next=1,margin_jump=1,retention_j=6,retention_next=3,retention_drop=3,continuation_j=3,continuation_next=2,continuation_drop=1,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 15699 | j=2,margin_j=-4,margin_next=1,margin_jump=5,retention_j=22,retention_next=9,retention_drop=13,continuation_j=9,continuation_next=5,continuation_drop=4,retention_drop_minus_2_continuation_drop=5,cause=retention_drop_dominant |
| 15737 | j=2,margin_j=-2,margin_next=2,margin_jump=4,retention_j=14,retention_next=6,retention_drop=8,continuation_j=6,continuation_next=4,continuation_drop=2,retention_drop_minus_2_continuation_drop=4,cause=retention_drop_dominant |
| 15743 | j=2,margin_j=-1,margin_next=2,margin_jump=3,retention_j=13,retention_next=6,retention_drop=7,continuation_j=6,continuation_next=4,continuation_drop=2,retention_drop_minus_2_continuation_drop=3,cause=retention_drop_dominant |
| 15767 | j=3,margin_j=0,margin_next=2,margin_jump=2,retention_j=8,retention_next=4,retention_drop=4,continuation_j=4,continuation_next=3,continuation_drop=1,retention_drop_minus_2_continuation_drop=2,cause=retention_drop_dominant |
| 15769 | j=3,margin_j=0,margin_next=1,margin_jump=1,retention_j=6,retention_next=3,retention_drop=3,continuation_j=3,continuation_next=2,continuation_drop=1,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 15775 | j=2,margin_j=-4,margin_next=1,margin_jump=5,retention_j=14,retention_next=5,retention_drop=9,continuation_j=5,continuation_next=3,continuation_drop=2,retention_drop_minus_2_continuation_drop=5,cause=retention_drop_dominant |
| 15815 | j=3,margin_j=-1,margin_next=1,margin_jump=2,retention_j=23,retention_next=11,retention_drop=12,continuation_j=11,continuation_next=6,continuation_drop=5,retention_drop_minus_2_continuation_drop=2,cause=retention_drop_dominant |
| 15851 | j=2,margin_j=0,margin_next=2,margin_jump=2,retention_j=8,retention_next=4,retention_drop=4,continuation_j=4,continuation_next=3,continuation_drop=1,retention_drop_minus_2_continuation_drop=2,cause=retention_drop_dominant |
| 15967 | j=2,margin_j=0,margin_next=1,margin_jump=1,retention_j=6,retention_next=3,retention_drop=3,continuation_j=3,continuation_next=2,continuation_drop=1,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 15977 | j=2,margin_j=0,margin_next=1,margin_jump=1,retention_j=14,retention_next=7,retention_drop=7,continuation_j=7,continuation_next=4,continuation_drop=3,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 16041 | j=2,margin_j=0,margin_next=1,margin_jump=1,retention_j=18,retention_next=9,retention_drop=9,continuation_j=9,continuation_next=5,continuation_drop=4,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 16047 | j=2,margin_j=0,margin_next=1,margin_jump=1,retention_j=14,retention_next=7,retention_drop=7,continuation_j=7,continuation_next=4,continuation_drop=3,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 16079 | j=4,margin_j=-2,margin_next=1,margin_jump=3,retention_j=12,retention_next=5,retention_drop=7,continuation_j=5,continuation_next=3,continuation_drop=2,retention_drop_minus_2_continuation_drop=3,cause=retention_drop_dominant |
| 16097 | j=2,margin_j=0,margin_next=1,margin_jump=1,retention_j=6,retention_next=3,retention_drop=3,continuation_j=3,continuation_next=2,continuation_drop=1,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 16127 | j=4,margin_j=0,margin_next=2,margin_jump=2,retention_j=12,retention_next=6,retention_drop=6,continuation_j=6,continuation_next=4,continuation_drop=2,retention_drop_minus_2_continuation_drop=2,cause=retention_drop_dominant |
| 16155 | j=2,margin_j=0,margin_next=1,margin_jump=1,retention_j=18,retention_next=9,retention_drop=9,continuation_j=9,continuation_next=5,continuation_drop=4,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 16183 | j=3,margin_j=-1,margin_next=1,margin_jump=2,retention_j=23,retention_next=11,retention_drop=12,continuation_j=11,continuation_next=6,continuation_drop=5,retention_drop_minus_2_continuation_drop=2,cause=retention_drop_dominant |
| 16293 | j=4,margin_j=0,margin_next=1,margin_jump=1,retention_j=6,retention_next=3,retention_drop=3,continuation_j=3,continuation_next=2,continuation_drop=1,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 16297 | j=2,margin_j=-1,margin_next=1,margin_jump=2,retention_j=15,retention_next=7,retention_drop=8,continuation_j=7,continuation_next=4,continuation_drop=3,retention_drop_minus_2_continuation_drop=2,cause=retention_drop_dominant |
| 16319 | j=2,margin_j=0,margin_next=2,margin_jump=2,retention_j=24,retention_next=12,retention_drop=12,continuation_j=12,continuation_next=7,continuation_drop=5,retention_drop_minus_2_continuation_drop=2,cause=retention_drop_dominant |
| 16365 | j=4,margin_j=0,margin_next=1,margin_jump=1,retention_j=6,retention_next=3,retention_drop=3,continuation_j=3,continuation_next=2,continuation_drop=1,retention_drop_minus_2_continuation_drop=1,cause=retention_drop_dominant |
| 16371 | j=2,margin_j=-2,margin_next=1,margin_jump=3,retention_j=24,retention_next=11,retention_drop=13,continuation_j=11,continuation_next=6,continuation_drop=5,retention_drop_minus_2_continuation_drop=3,cause=retention_drop_dominant |
| 16375 | j=3,margin_j=-2,margin_next=1,margin_jump=3,retention_j=12,retention_next=5,retention_drop=7,continuation_j=5,continuation_next=3,continuation_drop=2,retention_drop_minus_2_continuation_drop=3,cause=retention_drop_dominant |
| 16379 | j=2,margin_j=-2,margin_next=3,margin_jump=5,retention_j=32,retention_next=15,retention_drop=17,continuation_j=15,continuation_next=9,continuation_drop=6,retention_drop_minus_2_continuation_drop=5,cause=retention_drop_dominant |

## PressureDecay: Local-Island Rows

| n | local-island pressure-decay details |
|---:|---|
| 1567 | n=1567,island_depth=3,left_edge_j=2,margin_left=-2,margin_island=1,margin_right=0,retention_left=8,retention_island=3,retention_right=2,continuation_left=3,continuation_island=2,continuation_right=1 |
| 1639 | n=1639,island_depth=5,left_edge_j=4,margin_left=0,margin_island=1,margin_right=0,retention_left=6,retention_island=3,retention_right=2,continuation_left=3,continuation_island=2,continuation_right=1 |
| 1775 | n=1775,island_depth=5,left_edge_j=4,margin_left=0,margin_island=1,margin_right=0,retention_left=6,retention_island=3,retention_right=2,continuation_left=3,continuation_island=2,continuation_right=1 |
| 2079 | n=2079,island_depth=3,left_edge_j=2,margin_left=0,margin_island=1,margin_right=0,retention_left=6,retention_island=3,retention_right=2,continuation_left=3,continuation_island=2,continuation_right=1 |
| 2089 | n=2089,island_depth=3,left_edge_j=2,margin_left=-2,margin_island=1,margin_right=0,retention_left=8,retention_island=3,retention_right=2,continuation_left=3,continuation_island=2,continuation_right=1 |
| 2103 | n=2103,island_depth=5,left_edge_j=4,margin_left=0,margin_island=1,margin_right=0,retention_left=6,retention_island=3,retention_right=2,continuation_left=3,continuation_island=2,continuation_right=1 |
| 2185 | n=2185,island_depth=5,left_edge_j=4,margin_left=0,margin_island=1,margin_right=0,retention_left=6,retention_island=3,retention_right=2,continuation_left=3,continuation_island=2,continuation_right=1 |
| 2431 | n=2431,island_depth=4,left_edge_j=3,margin_left=0,margin_island=1,margin_right=0,retention_left=22,retention_island=11,retention_right=6,continuation_left=11,continuation_island=6,continuation_right=3 |
| 2459 | n=2459,island_depth=5,left_edge_j=4,margin_left=0,margin_island=1,margin_right=0,retention_left=6,retention_island=3,retention_right=2,continuation_left=3,continuation_island=2,continuation_right=1 |
| 2475 | n=2475,island_depth=3,left_edge_j=2,margin_left=-3,margin_island=1,margin_right=0,retention_left=9,retention_island=3,retention_right=2,continuation_left=3,continuation_island=2,continuation_right=1 |
| 2495 | n=2495,island_depth=4,left_edge_j=3,margin_left=0,margin_island=1,margin_right=0,retention_left=6,retention_island=3,retention_right=2,continuation_left=3,continuation_island=2,continuation_right=1 |
| 2655 | n=2655,island_depth=3,left_edge_j=2,margin_left=-1,margin_island=1,margin_right=0,retention_left=7,retention_island=3,retention_right=2,continuation_left=3,continuation_island=2,continuation_right=1 |
| 2715 | n=2715,island_depth=5,left_edge_j=4,margin_left=0,margin_island=1,margin_right=0,retention_left=6,retention_island=3,retention_right=2,continuation_left=3,continuation_island=2,continuation_right=1 |
| 2727 | n=2727,island_depth=5,left_edge_j=4,margin_left=0,margin_island=1,margin_right=0,retention_left=6,retention_island=3,retention_right=2,continuation_left=3,continuation_island=2,continuation_right=1 |
| 2767 | n=2767,island_depth=5,left_edge_j=4,margin_left=0,margin_island=1,margin_right=0,retention_left=6,retention_island=3,retention_right=2,continuation_left=3,continuation_island=2,continuation_right=1 |
| 2785 | n=2785,island_depth=3,left_edge_j=2,margin_left=-2,margin_island=1,margin_right=0,retention_left=8,retention_island=3,retention_right=2,continuation_left=3,continuation_island=2,continuation_right=1 |
| 2913 | n=2913,island_depth=5,left_edge_j=4,margin_left=0,margin_island=1,margin_right=0,retention_left=6,retention_island=3,retention_right=2,continuation_left=3,continuation_island=2,continuation_right=1 |
| 3055 | n=3055,island_depth=5,left_edge_j=4,margin_left=0,margin_island=1,margin_right=0,retention_left=6,retention_island=3,retention_right=2,continuation_left=3,continuation_island=2,continuation_right=1 |
| 3155 | n=3155,island_depth=5,left_edge_j=4,margin_left=0,margin_island=1,margin_right=0,retention_left=6,retention_island=3,retention_right=2,continuation_left=3,continuation_island=2,continuation_right=1 |
| 3175 | n=3175,island_depth=5,left_edge_j=4,margin_left=-1,margin_island=2,margin_right=0,retention_left=13,retention_island=6,retention_right=4,continuation_left=6,continuation_island=4,continuation_right=2 |
| 3241 | n=3241,island_depth=4,left_edge_j=3,margin_left=0,margin_island=1,margin_right=0,retention_left=22,retention_island=11,retention_right=6,continuation_left=11,continuation_island=6,continuation_right=3 |
| 3279 | n=3279,island_depth=5,left_edge_j=4,margin_left=0,margin_island=1,margin_right=0,retention_left=6,retention_island=3,retention_right=2,continuation_left=3,continuation_island=2,continuation_right=1 |
| 3323 | n=3323,island_depth=3,left_edge_j=2,margin_left=-2,margin_island=1,margin_right=-1,retention_left=20,retention_island=9,retention_right=5,continuation_left=9,continuation_island=5,continuation_right=2 |
| 3627 | n=3627,island_depth=3,left_edge_j=2,margin_left=0,margin_island=1,margin_right=0,retention_left=6,retention_island=3,retention_right=2,continuation_left=3,continuation_island=2,continuation_right=1 |
| 3689 | n=3689,island_depth=5,left_edge_j=4,margin_left=0,margin_island=1,margin_right=0,retention_left=6,retention_island=3,retention_right=2,continuation_left=3,continuation_island=2,continuation_right=1 |
| 3713 | n=3713,island_depth=3,left_edge_j=2,margin_left=-2,margin_island=1,margin_right=0,retention_left=8,retention_island=3,retention_right=2,continuation_left=3,continuation_island=2,continuation_right=1 |
| 3739 | n=3739,island_depth=3,left_edge_j=2,margin_left=-1,margin_island=1,margin_right=-1,retention_left=19,retention_island=9,retention_right=5,continuation_left=9,continuation_island=5,continuation_right=2 |
| 4073 | n=4073,island_depth=5,left_edge_j=4,margin_left=0,margin_island=1,margin_right=0,retention_left=6,retention_island=3,retention_right=2,continuation_left=3,continuation_island=2,continuation_right=1 |
| 4091 | n=4091,island_depth=5,left_edge_j=4,margin_left=0,margin_island=1,margin_right=0,retention_left=6,retention_island=3,retention_right=2,continuation_left=3,continuation_island=2,continuation_right=1 |
| 4207 | n=4207,island_depth=3,left_edge_j=2,margin_left=0,margin_island=1,margin_right=-1,retention_left=18,retention_island=9,retention_right=5,continuation_left=9,continuation_island=5,continuation_right=2 |
| 4223 | n=4223,island_depth=5,left_edge_j=4,margin_left=0,margin_island=1,margin_right=-1,retention_left=10,retention_island=5,retention_right=3,continuation_left=5,continuation_island=3,continuation_right=1 |
| 4233 | n=4233,island_depth=5,left_edge_j=4,margin_left=-1,margin_island=2,margin_right=0,retention_left=13,retention_island=6,retention_right=4,continuation_left=6,continuation_island=4,continuation_right=2 |
| 4321 | n=4321,island_depth=4,left_edge_j=3,margin_left=0,margin_island=1,margin_right=0,retention_left=22,retention_island=11,retention_right=6,continuation_left=11,continuation_island=6,continuation_right=3 |
| 4335 | n=4335,island_depth=3,left_edge_j=2,margin_left=0,margin_island=1,margin_right=-1,retention_left=10,retention_island=5,retention_right=3,continuation_left=5,continuation_island=3,continuation_right=1 |
| 4371 | n=4371,island_depth=5,left_edge_j=4,margin_left=0,margin_island=1,margin_right=0,retention_left=6,retention_island=3,retention_right=2,continuation_left=3,continuation_island=2,continuation_right=1 |
| 4435 | n=4435,island_depth=4,left_edge_j=3,margin_left=0,margin_island=1,margin_right=0,retention_left=6,retention_island=3,retention_right=2,continuation_left=3,continuation_island=2,continuation_right=1 |
| 4551 | n=4551,island_depth=4,left_edge_j=3,margin_left=-1,margin_island=1,margin_right=0,retention_left=23,retention_island=11,retention_right=6,continuation_left=11,continuation_island=6,continuation_right=3 |
| 4603 | n=4603,island_depth=5,left_edge_j=4,margin_left=0,margin_island=1,margin_right=0,retention_left=6,retention_island=3,retention_right=2,continuation_left=3,continuation_island=2,continuation_right=1 |
| 4635 | n=4635,island_depth=3,left_edge_j=2,margin_left=-1,margin_island=1,margin_right=0,retention_left=15,retention_island=7,retention_right=4,continuation_left=7,continuation_island=4,continuation_right=2 |
| 4703 | n=4703,island_depth=3,left_edge_j=2,margin_left=-2,margin_island=1,margin_right=0,retention_left=8,retention_island=3,retention_right=2,continuation_left=3,continuation_island=2,continuation_right=1 |
| 4733 | n=4733,island_depth=5,left_edge_j=4,margin_left=0,margin_island=1,margin_right=0,retention_left=6,retention_island=3,retention_right=2,continuation_left=3,continuation_island=2,continuation_right=1 |
| 4763 | n=4763,island_depth=5,left_edge_j=4,margin_left=-1,margin_island=2,margin_right=0,retention_left=13,retention_island=6,retention_right=4,continuation_left=6,continuation_island=4,continuation_right=2 |
| 4935 | n=4935,island_depth=5,left_edge_j=4,margin_left=0,margin_island=2,margin_right=0,retention_left=12,retention_island=6,retention_right=4,continuation_left=6,continuation_island=4,continuation_right=2 |
| 4959 | n=4959,island_depth=3,left_edge_j=2,margin_left=0,margin_island=1,margin_right=0,retention_left=6,retention_island=3,retention_right=2,continuation_left=3,continuation_island=2,continuation_right=1 |
| 4985 | n=4985,island_depth=3,left_edge_j=2,margin_left=-1,margin_island=1,margin_right=-1,retention_left=19,retention_island=9,retention_right=5,continuation_left=9,continuation_island=5,continuation_right=2 |
| 5179 | n=5179,island_depth=5,left_edge_j=4,margin_left=0,margin_island=1,margin_right=0,retention_left=6,retention_island=3,retention_right=2,continuation_left=3,continuation_island=2,continuation_right=1 |
| 5215 | n=5215,island_depth=3,left_edge_j=2,margin_left=0,margin_island=1,margin_right=0,retention_left=14,retention_island=7,retention_right=4,continuation_left=7,continuation_island=4,continuation_right=2 |
| 5359 | n=5359,island_depth=5,left_edge_j=4,margin_left=-1,margin_island=2,margin_right=0,retention_left=13,retention_island=6,retention_right=4,continuation_left=6,continuation_island=4,continuation_right=2 |
| 5455 | n=5455,island_depth=5,left_edge_j=4,margin_left=-1,margin_island=1,margin_right=0,retention_left=7,retention_island=3,retention_right=2,continuation_left=3,continuation_island=2,continuation_right=1 |
| 5571 | n=5571,island_depth=3,left_edge_j=2,margin_left=-3,margin_island=1,margin_right=0,retention_left=9,retention_island=3,retention_right=2,continuation_left=3,continuation_island=2,continuation_right=1 |
| 5609 | n=5609,island_depth=3,left_edge_j=2,margin_left=0,margin_island=1,margin_right=-1,retention_left=18,retention_island=9,retention_right=5,continuation_left=9,continuation_island=5,continuation_right=2 |
| 5659 | n=5659,island_depth=3,left_edge_j=2,margin_left=-3,margin_island=1,margin_right=0,retention_left=9,retention_island=3,retention_right=2,continuation_left=3,continuation_island=2,continuation_right=1 |
| 5761 | n=5761,island_depth=4,left_edge_j=3,margin_left=0,margin_island=1,margin_right=0,retention_left=22,retention_island=11,retention_right=6,continuation_left=11,continuation_island=6,continuation_right=3 |
| 5827 | n=5827,island_depth=5,left_edge_j=4,margin_left=0,margin_island=1,margin_right=0,retention_left=6,retention_island=3,retention_right=2,continuation_left=3,continuation_island=2,continuation_right=1 |
| 5871 | n=5871,island_depth=3,left_edge_j=2,margin_left=0,margin_island=1,margin_right=-2,retention_left=14,retention_island=7,retention_right=4,continuation_left=7,continuation_island=4,continuation_right=1 |
| 5907 | n=5907,island_depth=3,left_edge_j=2,margin_left=-3,margin_island=1,margin_right=-1,retention_left=21,retention_island=9,retention_right=5,continuation_left=9,continuation_island=5,continuation_right=2 |
| 5913 | n=5913,island_depth=4,left_edge_j=3,margin_left=0,margin_island=1,margin_right=0,retention_left=6,retention_island=3,retention_right=2,continuation_left=3,continuation_island=2,continuation_right=1 |
| 5983 | n=5983,island_depth=3,left_edge_j=2,margin_left=-1,margin_island=1,margin_right=0,retention_left=7,retention_island=3,retention_right=2,continuation_left=3,continuation_island=2,continuation_right=1 |
| 6137 | n=6137,island_depth=5,left_edge_j=4,margin_left=0,margin_island=1,margin_right=0,retention_left=6,retention_island=3,retention_right=2,continuation_left=3,continuation_island=2,continuation_right=1 |
| 6207 | n=6207,island_depth=4,left_edge_j=3,margin_left=0,margin_island=1,margin_right=0,retention_left=6,retention_island=3,retention_right=2,continuation_left=3,continuation_island=2,continuation_right=1 |
| 6239 | n=6239,island_depth=3,left_edge_j=2,margin_left=0,margin_island=1,margin_right=0,retention_left=6,retention_island=3,retention_right=2,continuation_left=3,continuation_island=2,continuation_right=1 |
| 6247 | n=6247,island_depth=5,left_edge_j=4,margin_left=0,margin_island=2,margin_right=0,retention_left=12,retention_island=6,retention_right=4,continuation_left=6,continuation_island=4,continuation_right=2 |
| 6351 | n=6351,island_depth=5,left_edge_j=4,margin_left=-1,margin_island=2,margin_right=0,retention_left=13,retention_island=6,retention_right=4,continuation_left=6,continuation_island=4,continuation_right=2 |
| 6367 | n=6367,island_depth=3,left_edge_j=2,margin_left=-2,margin_island=1,margin_right=0,retention_left=8,retention_island=3,retention_right=2,continuation_left=3,continuation_island=2,continuation_right=1 |
| 6557 | n=6557,island_depth=5,left_edge_j=4,margin_left=0,margin_island=1,margin_right=0,retention_left=6,retention_island=3,retention_right=2,continuation_left=3,continuation_island=2,continuation_right=1 |
| 6559 | n=6559,island_depth=3,left_edge_j=2,margin_left=-1,margin_island=1,margin_right=0,retention_left=7,retention_island=3,retention_right=2,continuation_left=3,continuation_island=2,continuation_right=1 |
| 6653 | n=6653,island_depth=4,left_edge_j=3,margin_left=0,margin_island=1,margin_right=0,retention_left=6,retention_island=3,retention_right=2,continuation_left=3,continuation_island=2,continuation_right=1 |
| 6687 | n=6687,island_depth=3,left_edge_j=2,margin_left=0,margin_island=1,margin_right=0,retention_left=6,retention_island=3,retention_right=2,continuation_left=3,continuation_island=2,continuation_right=1 |
| 6783 | n=6783,island_depth=5,left_edge_j=4,margin_left=-1,margin_island=1,margin_right=-1,retention_left=11,retention_island=5,retention_right=3,continuation_left=5,continuation_island=3,continuation_right=1 |
| 6827 | n=6827,island_depth=4,left_edge_j=3,margin_left=0,margin_island=1,margin_right=0,retention_left=22,retention_island=11,retention_right=6,continuation_left=11,continuation_island=6,continuation_right=3 |
| 6905 | n=6905,island_depth=5,left_edge_j=4,margin_left=0,margin_island=1,margin_right=0,retention_left=6,retention_island=3,retention_right=2,continuation_left=3,continuation_island=2,continuation_right=1 |
| 6953 | n=6953,island_depth=3,left_edge_j=2,margin_left=0,margin_island=1,margin_right=0,retention_left=14,retention_island=7,retention_right=4,continuation_left=7,continuation_island=4,continuation_right=2 |
| 7071 | n=7071,island_depth=3,left_edge_j=2,margin_left=-3,margin_island=1,margin_right=0,retention_left=9,retention_island=3,retention_right=2,continuation_left=3,continuation_island=2,continuation_right=1 |
| 7145 | n=7145,island_depth=5,left_edge_j=4,margin_left=-1,margin_island=2,margin_right=0,retention_left=13,retention_island=6,retention_right=4,continuation_left=6,continuation_island=4,continuation_right=2 |
| 7273 | n=7273,island_depth=5,left_edge_j=4,margin_left=-1,margin_island=1,margin_right=0,retention_left=7,retention_island=3,retention_right=2,continuation_left=3,continuation_island=2,continuation_right=1 |
| 7327 | n=7327,island_depth=3,left_edge_j=2,margin_left=0,margin_island=2,margin_right=-1,retention_left=16,retention_island=8,retention_right=5,continuation_left=8,continuation_island=5,continuation_right=2 |
| 7367 | n=7367,island_depth=4,left_edge_j=3,margin_left=0,margin_island=1,margin_right=0,retention_left=14,retention_island=7,retention_right=4,continuation_left=7,continuation_island=4,continuation_right=2 |
| 7403 | n=7403,island_depth=5,left_edge_j=4,margin_left=0,margin_island=2,margin_right=0,retention_left=12,retention_island=6,retention_right=4,continuation_left=6,continuation_island=4,continuation_right=2 |
| 7427 | n=7427,island_depth=3,left_edge_j=2,margin_left=-3,margin_island=1,margin_right=0,retention_left=9,retention_island=3,retention_right=2,continuation_left=3,continuation_island=2,continuation_right=1 |
| 7455 | n=7455,island_depth=3,left_edge_j=2,margin_left=0,margin_island=1,margin_right=-1,retention_left=10,retention_island=5,retention_right=3,continuation_left=5,continuation_island=3,continuation_right=1 |
| 7507 | n=7507,island_depth=5,left_edge_j=4,margin_left=0,margin_island=1,margin_right=-1,retention_left=10,retention_island=5,retention_right=3,continuation_left=5,continuation_island=3,continuation_right=1 |
| 7545 | n=7545,island_depth=3,left_edge_j=2,margin_left=-3,margin_island=1,margin_right=0,retention_left=9,retention_island=3,retention_right=2,continuation_left=3,continuation_island=2,continuation_right=1 |
| 7681 | n=7681,island_depth=4,left_edge_j=3,margin_left=0,margin_island=1,margin_right=0,retention_left=22,retention_island=11,retention_right=6,continuation_left=11,continuation_island=6,continuation_right=3 |
| 7707 | n=7707,island_depth=3,left_edge_j=2,margin_left=-1,margin_island=1,margin_right=-1,retention_left=11,retention_island=5,retention_right=3,continuation_left=5,continuation_island=3,continuation_right=1 |
| 7743 | n=7743,island_depth=4,left_edge_j=3,margin_left=-1,margin_island=1,margin_right=0,retention_left=7,retention_island=3,retention_right=2,continuation_left=3,continuation_island=2,continuation_right=1 |
| 7769 | n=7769,island_depth=5,left_edge_j=4,margin_left=0,margin_island=1,margin_right=0,retention_left=6,retention_island=3,retention_right=2,continuation_left=3,continuation_island=2,continuation_right=1 |
| 7887 | n=7887,island_depth=5,left_edge_j=4,margin_left=0,margin_island=1,margin_right=0,retention_left=14,retention_island=7,retention_right=4,continuation_left=7,continuation_island=4,continuation_right=2 |
| 7977 | n=7977,island_depth=3,left_edge_j=2,margin_left=-1,margin_island=1,margin_right=0,retention_left=7,retention_island=3,retention_right=2,continuation_left=3,continuation_island=2,continuation_right=1 |
| 8039 | n=8039,island_depth=5,left_edge_j=4,margin_left=0,margin_island=2,margin_right=0,retention_left=12,retention_island=6,retention_right=4,continuation_left=6,continuation_island=4,continuation_right=2 |
| 8163 | n=8163,island_depth=3,left_edge_j=2,margin_left=0,margin_island=1,margin_right=0,retention_left=6,retention_island=3,retention_right=2,continuation_left=3,continuation_island=2,continuation_right=1 |
| 8183 | n=8183,island_depth=5,left_edge_j=4,margin_left=0,margin_island=1,margin_right=0,retention_left=6,retention_island=3,retention_right=2,continuation_left=3,continuation_island=2,continuation_right=1 |
| 8329 | n=8329,island_depth=5,left_edge_j=4,margin_left=0,margin_island=2,margin_right=0,retention_left=12,retention_island=6,retention_right=4,continuation_left=6,continuation_island=4,continuation_right=2 |
| 8357 | n=8357,island_depth=3,left_edge_j=2,margin_left=-2,margin_island=1,margin_right=0,retention_left=8,retention_island=3,retention_right=2,continuation_left=3,continuation_island=2,continuation_right=1 |
| 8413 | n=8413,island_depth=5,left_edge_j=4,margin_left=0,margin_island=1,margin_right=0,retention_left=6,retention_island=3,retention_right=2,continuation_left=3,continuation_island=2,continuation_right=1 |
| 8443 | n=8443,island_depth=4,left_edge_j=3,margin_left=0,margin_island=1,margin_right=-1,retention_left=10,retention_island=5,retention_right=3,continuation_left=5,continuation_island=3,continuation_right=1 |
| 8467 | n=8467,island_depth=5,left_edge_j=4,margin_left=-1,margin_island=2,margin_right=0,retention_left=13,retention_island=6,retention_right=4,continuation_left=6,continuation_island=4,continuation_right=2 |
| 8489 | n=8489,island_depth=3,left_edge_j=2,margin_left=-2,margin_island=1,margin_right=0,retention_left=8,retention_island=3,retention_right=2,continuation_left=3,continuation_island=2,continuation_right=1 |
| 8619 | n=8619,island_depth=5,left_edge_j=4,margin_left=-1,margin_island=1,margin_right=0,retention_left=7,retention_island=3,retention_right=2,continuation_left=3,continuation_island=2,continuation_right=1 |
| 8643 | n=8643,island_depth=4,left_edge_j=3,margin_left=0,margin_island=1,margin_right=0,retention_left=22,retention_island=11,retention_right=6,continuation_left=11,continuation_island=6,continuation_right=3 |
| 8671 | n=8671,island_depth=3,left_edge_j=2,margin_left=0,margin_island=1,margin_right=-1,retention_left=10,retention_island=5,retention_right=3,continuation_left=5,continuation_island=3,continuation_right=1 |
| 8683 | n=8683,island_depth=3,left_edge_j=2,margin_left=-1,margin_island=2,margin_right=-1,retention_left=17,retention_island=8,retention_right=5,continuation_left=8,continuation_island=5,continuation_right=2 |
| 8741 | n=8741,island_depth=5,left_edge_j=4,margin_left=0,margin_island=1,margin_right=0,retention_left=6,retention_island=3,retention_right=2,continuation_left=3,continuation_island=2,continuation_right=1 |
| 8745 | n=8745,island_depth=3,left_edge_j=2,margin_left=-1,margin_island=1,margin_right=0,retention_left=7,retention_island=3,retention_right=2,continuation_left=3,continuation_island=2,continuation_right=1 |
| 8861 | n=8861,island_depth=3,left_edge_j=2,margin_left=-2,margin_island=1,margin_right=-1,retention_left=20,retention_island=9,retention_right=5,continuation_left=9,continuation_island=5,continuation_right=2 |
| 8983 | n=8983,island_depth=4,left_edge_j=3,margin_left=0,margin_island=1,margin_right=0,retention_left=22,retention_island=11,retention_right=6,continuation_left=11,continuation_island=6,continuation_right=3 |
| 9055 | n=9055,island_depth=3,left_edge_j=2,margin_left=0,margin_island=1,margin_right=0,retention_left=6,retention_island=3,retention_right=2,continuation_left=3,continuation_island=2,continuation_right=1 |
| 9063 | n=9063,island_depth=4,left_edge_j=3,margin_left=0,margin_island=1,margin_right=0,retention_left=6,retention_island=3,retention_right=2,continuation_left=3,continuation_island=2,continuation_right=1 |
| 9087 | n=9087,island_depth=8,left_edge_j=7,margin_left=0,margin_island=1,margin_right=0,retention_left=6,retention_island=3,retention_right=2,continuation_left=3,continuation_island=2,continuation_right=1 |
| 9167 | n=9167,island_depth=5,left_edge_j=4,margin_left=0,margin_island=1,margin_right=0,retention_left=6,retention_island=3,retention_right=2,continuation_left=3,continuation_island=2,continuation_right=1 |
| 9207 | n=9207,island_depth=5,left_edge_j=4,margin_left=0,margin_island=1,margin_right=0,retention_left=6,retention_island=3,retention_right=2,continuation_left=3,continuation_island=2,continuation_right=1 |
| 9371 | n=9371,island_depth=5,left_edge_j=4,margin_left=0,margin_island=2,margin_right=0,retention_left=12,retention_island=6,retention_right=4,continuation_left=6,continuation_island=4,continuation_right=2 |
| 9467 | n=9467,island_depth=3,left_edge_j=2,margin_left=-2,margin_island=1,margin_right=0,retention_left=16,retention_island=7,retention_right=4,continuation_left=7,continuation_island=4,continuation_right=2 |
| 9499 | n=9499,island_depth=4,left_edge_j=3,margin_left=0,margin_island=1,margin_right=-1,retention_left=10,retention_island=5,retention_right=3,continuation_left=5,continuation_island=3,continuation_right=1 |
| 9527 | n=9527,island_depth=5,left_edge_j=4,margin_left=0,margin_island=2,margin_right=0,retention_left=12,retention_island=6,retention_right=4,continuation_left=6,continuation_island=4,continuation_right=2 |
| 9697 | n=9697,island_depth=5,left_edge_j=4,margin_left=-1,margin_island=1,margin_right=0,retention_left=7,retention_island=3,retention_right=2,continuation_left=3,continuation_island=2,continuation_right=1 |
| 9755 | n=9755,island_depth=3,left_edge_j=2,margin_left=-2,margin_island=1,margin_right=0,retention_left=8,retention_island=3,retention_right=2,continuation_left=3,continuation_island=2,continuation_right=1 |
| 9769 | n=9769,island_depth=3,left_edge_j=2,margin_left=0,margin_island=2,margin_right=-1,retention_left=16,retention_island=8,retention_right=5,continuation_left=8,continuation_island=5,continuation_right=2 |
| 9837 | n=9837,island_depth=5,left_edge_j=4,margin_left=0,margin_island=1,margin_right=0,retention_left=6,retention_island=3,retention_right=2,continuation_left=3,continuation_island=2,continuation_right=1 |
| 9871 | n=9871,island_depth=5,left_edge_j=4,margin_left=-1,margin_island=2,margin_right=0,retention_left=13,retention_island=6,retention_right=4,continuation_left=6,continuation_island=4,continuation_right=2 |
| 9901 | n=9901,island_depth=3,left_edge_j=2,margin_left=-2,margin_island=1,margin_right=0,retention_left=8,retention_island=3,retention_right=2,continuation_left=3,continuation_island=2,continuation_right=1 |
| 9971 | n=9971,island_depth=3,left_edge_j=2,margin_left=-1,margin_island=1,margin_right=-1,retention_left=19,retention_island=9,retention_right=5,continuation_left=9,continuation_island=5,continuation_right=2 |
| 10009 | n=10009,island_depth=5,left_edge_j=4,margin_left=0,margin_island=1,margin_right=-1,retention_left=10,retention_island=5,retention_right=3,continuation_left=5,continuation_island=3,continuation_right=1 |
| 10215 | n=10215,island_depth=5,left_edge_j=4,margin_left=-1,margin_island=1,margin_right=0,retention_left=7,retention_island=3,retention_right=2,continuation_left=3,continuation_island=2,continuation_right=1 |
| 10235 | n=10235,island_depth=3,left_edge_j=2,margin_left=-9,margin_island=1,margin_right=-1,retention_left=19,retention_island=5,retention_right=3,continuation_left=5,continuation_island=3,continuation_right=1 |
| 10241 | n=10241,island_depth=4,left_edge_j=3,margin_left=0,margin_island=1,margin_right=0,retention_left=22,retention_island=11,retention_right=6,continuation_left=11,continuation_island=6,continuation_right=3 |
| 10359 | n=10359,island_depth=5,left_edge_j=4,margin_left=0,margin_island=1,margin_right=0,retention_left=6,retention_island=3,retention_right=2,continuation_left=3,continuation_island=2,continuation_right=1 |
| 10491 | n=10491,island_depth=3,left_edge_j=2,margin_left=-3,margin_island=2,margin_right=0,retention_left=15,retention_island=6,retention_right=4,continuation_left=6,continuation_island=4,continuation_right=2 |
| 10543 | n=10543,island_depth=5,left_edge_j=4,margin_left=0,margin_island=2,margin_right=0,retention_left=12,retention_island=6,retention_right=4,continuation_left=6,continuation_island=4,continuation_right=2 |
| 10651 | n=10651,island_depth=3,left_edge_j=2,margin_left=-1,margin_island=1,margin_right=0,retention_left=15,retention_island=7,retention_right=4,continuation_left=7,continuation_island=4,continuation_right=2 |
| 10687 | n=10687,island_depth=4,left_edge_j=3,margin_left=0,margin_island=1,margin_right=-1,retention_left=10,retention_island=5,retention_right=3,continuation_left=5,continuation_island=3,continuation_right=1 |
| 10731 | n=10731,island_depth=3,left_edge_j=2,margin_left=-1,margin_island=1,margin_right=0,retention_left=7,retention_island=3,retention_right=2,continuation_left=3,continuation_island=2,continuation_right=1 |
| 10861 | n=10861,island_depth=5,left_edge_j=4,margin_left=0,margin_island=1,margin_right=0,retention_left=6,retention_island=3,retention_right=2,continuation_left=3,continuation_island=2,continuation_right=1 |
| 10863 | n=10863,island_depth=3,left_edge_j=2,margin_left=0,margin_island=1,margin_right=-1,retention_left=18,retention_island=9,retention_right=5,continuation_left=9,continuation_island=5,continuation_right=2 |
| 10883 | n=10883,island_depth=3,left_edge_j=2,margin_left=0,margin_island=1,margin_right=0,retention_left=6,retention_island=3,retention_right=2,continuation_left=3,continuation_island=2,continuation_right=1 |
| 10909 | n=10909,island_depth=5,left_edge_j=4,margin_left=0,margin_island=1,margin_right=0,retention_left=6,retention_island=3,retention_right=2,continuation_left=3,continuation_island=2,continuation_right=1 |
| 10975 | n=10975,island_depth=3,left_edge_j=2,margin_left=-1,margin_island=1,margin_right=0,retention_left=7,retention_island=3,retention_right=2,continuation_left=3,continuation_island=2,continuation_right=1 |
| 10991 | n=10991,island_depth=3,left_edge_j=2,margin_left=-1,margin_island=1,margin_right=-2,retention_left=15,retention_island=7,retention_right=4,continuation_left=7,continuation_island=4,continuation_right=1 |
| 11055 | n=11055,island_depth=3,left_edge_j=2,margin_left=-1,margin_island=1,margin_right=0,retention_left=15,retention_island=7,retention_right=4,continuation_left=7,continuation_island=4,continuation_right=2 |
| 11091 | n=11091,island_depth=3,left_edge_j=2,margin_left=-1,margin_island=1,margin_right=0,retention_left=7,retention_island=3,retention_right=2,continuation_left=3,continuation_island=2,continuation_right=1 |
| 11103 | n=11103,island_depth=3,left_edge_j=2,margin_left=-4,margin_island=1,margin_right=0,retention_left=10,retention_island=3,retention_right=2,continuation_left=3,continuation_island=2,continuation_right=1 |
| 11105 | n=11105,island_depth=5,left_edge_j=4,margin_left=0,margin_island=2,margin_right=0,retention_left=12,retention_island=6,retention_right=4,continuation_left=6,continuation_island=4,continuation_right=2 |
| 11111 | n=11111,island_depth=4,left_edge_j=3,margin_left=0,margin_island=1,margin_right=0,retention_left=6,retention_island=3,retention_right=2,continuation_left=3,continuation_island=2,continuation_right=1 |
| 11135 | n=11135,island_depth=5,left_edge_j=4,margin_left=-4,margin_island=1,margin_right=0,retention_left=10,retention_island=3,retention_right=2,continuation_left=3,continuation_island=2,continuation_right=1 |
| 11141 | n=11141,island_depth=3,left_edge_j=2,margin_left=-2,margin_island=1,margin_right=0,retention_left=8,retention_island=3,retention_right=2,continuation_left=3,continuation_island=2,continuation_right=1 |
| 11147 | n=11147,island_depth=3,left_edge_j=2,margin_left=-3,margin_island=1,margin_right=0,retention_left=9,retention_island=3,retention_right=2,continuation_left=3,continuation_island=2,continuation_right=1 |
| 11167 | n=11167,island_depth=3,left_edge_j=2,margin_left=-4,margin_island=1,margin_right=0,retention_left=10,retention_island=3,retention_right=2,continuation_left=3,continuation_island=2,continuation_right=1 |
| 11199 | n=11199,island_depth=4,left_edge_j=3,margin_left=0,margin_island=1,margin_right=0,retention_left=6,retention_island=3,retention_right=2,continuation_left=3,continuation_island=2,continuation_right=1 |
| 11217 | n=11217,island_depth=5,left_edge_j=4,margin_left=0,margin_island=1,margin_right=0,retention_left=6,retention_island=3,retention_right=2,continuation_left=3,continuation_island=2,continuation_right=1 |
| 11257 | n=11257,island_depth=4,left_edge_j=3,margin_left=0,margin_island=1,margin_right=-1,retention_left=10,retention_island=5,retention_right=3,continuation_left=5,continuation_island=3,continuation_right=1 |
| 11261 | n=11261,island_depth=5,left_edge_j=4,margin_left=0,margin_island=1,margin_right=-1,retention_left=10,retention_island=5,retention_right=3,continuation_left=5,continuation_island=3,continuation_right=1 |
| 11289 | n=11289,island_depth=5,left_edge_j=4,margin_left=-1,margin_island=2,margin_right=0,retention_left=13,retention_island=6,retention_right=4,continuation_left=6,continuation_island=4,continuation_right=2 |
| 11291 | n=11291,island_depth=3,left_edge_j=2,margin_left=-3,margin_island=1,margin_right=0,retention_left=25,retention_island=11,retention_right=6,continuation_left=11,continuation_island=6,continuation_right=3 |
| 11455 | n=11455,island_depth=4,left_edge_j=3,margin_left=0,margin_island=1,margin_right=-1,retention_left=10,retention_island=5,retention_right=3,continuation_left=5,continuation_island=3,continuation_right=1 |
| 11515 | n=11515,island_depth=3,left_edge_j=2,margin_left=-8,margin_island=1,margin_right=-1,retention_left=18,retention_island=5,retention_right=3,continuation_left=5,continuation_island=3,continuation_right=1 |
| 11523 | n=11523,island_depth=4,left_edge_j=3,margin_left=0,margin_island=1,margin_right=0,retention_left=22,retention_island=11,retention_right=6,continuation_left=11,continuation_island=6,continuation_right=3 |
| 11561 | n=11561,island_depth=3,left_edge_j=2,margin_left=0,margin_island=1,margin_right=-1,retention_left=10,retention_island=5,retention_right=3,continuation_left=5,continuation_island=3,continuation_right=1 |
| 11577 | n=11577,island_depth=3,left_edge_j=2,margin_left=-1,margin_island=2,margin_right=-1,retention_left=17,retention_island=8,retention_right=5,continuation_left=8,continuation_island=5,continuation_right=2 |
| 11653 | n=11653,island_depth=5,left_edge_j=4,margin_left=0,margin_island=1,margin_right=0,retention_left=6,retention_island=3,retention_right=2,continuation_left=3,continuation_island=2,continuation_right=1 |
| 11711 | n=11711,island_depth=3,left_edge_j=2,margin_left=-2,margin_island=2,margin_right=0,retention_left=14,retention_island=6,retention_right=4,continuation_left=6,continuation_island=4,continuation_right=2 |
| 11743 | n=11743,island_depth=3,left_edge_j=2,margin_left=0,margin_island=1,margin_right=0,retention_left=14,retention_island=7,retention_right=4,continuation_left=7,continuation_island=4,continuation_right=2 |
| 11803 | n=11803,island_depth=3,left_edge_j=2,margin_left=-2,margin_island=2,margin_right=0,retention_left=14,retention_island=6,retention_right=4,continuation_left=6,continuation_island=4,continuation_right=2 |
| 11823 | n=11823,island_depth=5,left_edge_j=4,margin_left=-1,margin_island=1,margin_right=0,retention_left=7,retention_island=3,retention_right=2,continuation_left=3,continuation_island=2,continuation_right=1 |
| 11827 | n=11827,island_depth=4,left_edge_j=3,margin_left=0,margin_island=1,margin_right=0,retention_left=6,retention_island=3,retention_right=2,continuation_left=3,continuation_island=2,continuation_right=1 |
| 11977 | n=11977,island_depth=4,left_edge_j=3,margin_left=0,margin_island=1,margin_right=0,retention_left=22,retention_island=11,retention_right=6,continuation_left=11,continuation_island=6,continuation_right=3 |
| 11983 | n=11983,island_depth=3,left_edge_j=2,margin_left=0,margin_island=1,margin_right=0,retention_left=14,retention_island=7,retention_right=4,continuation_left=7,continuation_island=4,continuation_right=2 |
| 12059 | n=12059,island_depth=5,left_edge_j=4,margin_left=0,margin_island=2,margin_right=0,retention_left=12,retention_island=6,retention_right=4,continuation_left=6,continuation_island=4,continuation_right=2 |
| 12073 | n=12073,island_depth=3,left_edge_j=2,margin_left=0,margin_island=1,margin_right=0,retention_left=6,retention_island=3,retention_right=2,continuation_left=3,continuation_island=2,continuation_right=1 |
| 12143 | n=12143,island_depth=5,left_edge_j=4,margin_left=0,margin_island=1,margin_right=0,retention_left=6,retention_island=3,retention_right=2,continuation_left=3,continuation_island=2,continuation_right=1 |
| 12223 | n=12223,island_depth=3,left_edge_j=2,margin_left=-1,margin_island=1,margin_right=0,retention_left=15,retention_island=7,retention_right=4,continuation_left=7,continuation_island=4,continuation_right=2 |
| 12263 | n=12263,island_depth=4,left_edge_j=3,margin_left=0,margin_island=1,margin_right=-1,retention_left=18,retention_island=9,retention_right=5,continuation_left=9,continuation_island=5,continuation_right=2 |
| 12275 | n=12275,island_depth=5,left_edge_j=4,margin_left=0,margin_island=1,margin_right=0,retention_left=6,retention_island=3,retention_right=2,continuation_left=3,continuation_island=2,continuation_right=1 |
| 12279 | n=12279,island_depth=4,left_edge_j=3,margin_left=0,margin_island=2,margin_right=0,retention_left=12,retention_island=6,retention_right=4,continuation_left=6,continuation_island=4,continuation_right=2 |
| 12319 | n=12319,island_depth=3,left_edge_j=2,margin_left=-7,margin_island=1,margin_right=0,retention_left=13,retention_island=3,retention_right=2,continuation_left=3,continuation_island=2,continuation_right=1 |
| 12463 | n=12463,island_depth=5,left_edge_j=4,margin_left=0,margin_island=1,margin_right=0,retention_left=14,retention_island=7,retention_right=4,continuation_left=7,continuation_island=4,continuation_right=2 |
| 12495 | n=12495,island_depth=5,left_edge_j=4,margin_left=0,margin_island=2,margin_right=0,retention_left=12,retention_island=6,retention_right=4,continuation_left=6,continuation_island=4,continuation_right=2 |
| 12541 | n=12541,island_depth=3,left_edge_j=2,margin_left=-2,margin_island=1,margin_right=0,retention_left=8,retention_island=3,retention_right=2,continuation_left=3,continuation_island=2,continuation_right=1 |
| 12621 | n=12621,island_depth=5,left_edge_j=4,margin_left=0,margin_island=1,margin_right=0,retention_left=6,retention_island=3,retention_right=2,continuation_left=3,continuation_island=2,continuation_right=1 |
| 12665 | n=12665,island_depth=4,left_edge_j=3,margin_left=0,margin_island=1,margin_right=-1,retention_left=10,retention_island=5,retention_right=3,continuation_left=5,continuation_island=3,continuation_right=1 |
| 12671 | n=12671,island_depth=5,left_edge_j=4,margin_left=0,margin_island=1,margin_right=-1,retention_left=10,retention_island=5,retention_right=3,continuation_left=5,continuation_island=3,continuation_right=1 |
| 12691 | n=12691,island_depth=3,left_edge_j=2,margin_left=0,margin_island=1,margin_right=0,retention_left=14,retention_island=7,retention_right=4,continuation_left=7,continuation_island=4,continuation_right=2 |
| 12701 | n=12701,island_depth=5,left_edge_j=4,margin_left=-1,margin_island=2,margin_right=0,retention_left=13,retention_island=6,retention_right=4,continuation_left=6,continuation_island=4,continuation_right=2 |
| 12703 | n=12703,island_depth=3,left_edge_j=2,margin_left=-2,margin_island=1,margin_right=0,retention_left=24,retention_island=11,retention_right=6,continuation_left=11,continuation_island=6,continuation_right=3 |
| 12807 | n=12807,island_depth=4,left_edge_j=3,margin_left=0,margin_island=1,margin_right=0,retention_left=6,retention_island=3,retention_right=2,continuation_left=3,continuation_island=2,continuation_right=1 |
| 12929 | n=12929,island_depth=5,left_edge_j=4,margin_left=-1,margin_island=1,margin_right=0,retention_left=7,retention_island=3,retention_right=2,continuation_left=3,continuation_island=2,continuation_right=1 |
| 12955 | n=12955,island_depth=3,left_edge_j=2,margin_left=-7,margin_island=1,margin_right=-1,retention_left=17,retention_island=5,retention_right=3,continuation_left=5,continuation_island=3,continuation_right=1 |
| 12965 | n=12965,island_depth=4,left_edge_j=3,margin_left=0,margin_island=1,margin_right=0,retention_left=22,retention_island=11,retention_right=6,continuation_left=11,continuation_island=6,continuation_right=3 |
| 13025 | n=13025,island_depth=3,left_edge_j=2,margin_left=0,margin_island=2,margin_right=-1,retention_left=16,retention_island=8,retention_right=5,continuation_left=8,continuation_island=5,continuation_right=2 |
| 13161 | n=13161,island_depth=5,left_edge_j=4,margin_left=-1,margin_island=2,margin_right=0,retention_left=13,retention_island=6,retention_right=4,continuation_left=6,continuation_island=4,continuation_right=2 |
| 13183 | n=13183,island_depth=5,left_edge_j=4,margin_left=0,margin_island=1,margin_right=-1,retention_left=10,retention_island=5,retention_right=3,continuation_left=5,continuation_island=3,continuation_right=1 |
| 13201 | n=13201,island_depth=3,left_edge_j=2,margin_left=-2,margin_island=1,margin_right=0,retention_left=8,retention_island=3,retention_right=2,continuation_left=3,continuation_island=2,continuation_right=1 |
| 13203 | n=13203,island_depth=3,left_edge_j=2,margin_left=-4,margin_island=1,margin_right=0,retention_left=10,retention_island=3,retention_right=2,continuation_left=3,continuation_island=2,continuation_right=1 |
| 13211 | n=13211,island_depth=3,left_edge_j=2,margin_left=-2,margin_island=1,margin_right=-1,retention_left=12,retention_island=5,retention_right=3,continuation_left=5,continuation_island=3,continuation_right=1 |
| 13279 | n=13279,island_depth=3,left_edge_j=2,margin_left=-1,margin_island=2,margin_right=0,retention_left=13,retention_island=6,retention_right=4,continuation_left=6,continuation_island=4,continuation_right=2 |
| 13293 | n=13293,island_depth=3,left_edge_j=2,margin_left=-1,margin_island=1,margin_right=-1,retention_left=19,retention_island=9,retention_right=5,continuation_left=9,continuation_island=5,continuation_right=2 |
| 13345 | n=13345,island_depth=5,left_edge_j=4,margin_left=0,margin_island=1,margin_right=-1,retention_left=10,retention_island=5,retention_right=3,continuation_left=5,continuation_island=3,continuation_right=1 |
| 13503 | n=13503,island_depth=5,left_edge_j=4,margin_left=-1,margin_island=1,margin_right=-1,retention_left=11,retention_island=5,retention_right=3,continuation_left=5,continuation_island=3,continuation_right=1 |
| 13567 | n=13567,island_depth=5,left_edge_j=4,margin_left=0,margin_island=2,margin_right=0,retention_left=12,retention_island=6,retention_right=4,continuation_left=6,continuation_island=4,continuation_right=2 |
| 13647 | n=13647,island_depth=3,left_edge_j=2,margin_left=-6,margin_island=1,margin_right=-2,retention_left=20,retention_island=7,retention_right=4,continuation_left=7,continuation_island=4,continuation_right=1 |
| 13655 | n=13655,island_depth=4,left_edge_j=3,margin_left=-1,margin_island=1,margin_right=0,retention_left=23,retention_island=11,retention_right=6,continuation_left=11,continuation_island=6,continuation_right=3 |
| 13663 | n=13663,island_depth=3,left_edge_j=2,margin_left=0,margin_island=1,margin_right=0,retention_left=6,retention_island=3,retention_right=2,continuation_left=3,continuation_island=2,continuation_right=1 |
| 13671 | n=13671,island_depth=3,left_edge_j=2,margin_left=-5,margin_island=1,margin_right=0,retention_left=19,retention_island=7,retention_right=4,continuation_left=7,continuation_island=4,continuation_right=2 |
| 13811 | n=13811,island_depth=5,left_edge_j=4,margin_left=0,margin_island=1,margin_right=0,retention_left=6,retention_island=3,retention_right=2,continuation_left=3,continuation_island=2,continuation_right=1 |
| 13815 | n=13815,island_depth=4,left_edge_j=3,margin_left=0,margin_island=2,margin_right=0,retention_left=12,retention_island=6,retention_right=4,continuation_left=6,continuation_island=4,continuation_right=2 |
| 13879 | n=13879,island_depth=3,left_edge_j=2,margin_left=-2,margin_island=1,margin_right=0,retention_left=16,retention_island=7,retention_right=4,continuation_left=7,continuation_island=4,continuation_right=2 |
| 14057 | n=14057,island_depth=5,left_edge_j=4,margin_left=0,margin_island=2,margin_right=0,retention_left=12,retention_island=6,retention_right=4,continuation_left=6,continuation_island=4,continuation_right=2 |
| 14201 | n=14201,island_depth=3,left_edge_j=2,margin_left=-1,margin_island=1,margin_right=0,retention_left=15,retention_island=7,retention_right=4,continuation_left=7,continuation_island=4,continuation_right=2 |
| 14249 | n=14249,island_depth=4,left_edge_j=3,margin_left=0,margin_island=1,margin_right=-1,retention_left=10,retention_island=5,retention_right=3,continuation_left=5,continuation_island=3,continuation_right=1 |
| 14291 | n=14291,island_depth=5,left_edge_j=4,margin_left=0,margin_island=2,margin_right=0,retention_left=12,retention_island=6,retention_right=4,continuation_left=6,continuation_island=4,continuation_right=2 |
| 14391 | n=14391,island_depth=5,left_edge_j=4,margin_left=0,margin_island=1,margin_right=0,retention_left=6,retention_island=3,retention_right=2,continuation_left=3,continuation_island=2,continuation_right=1 |
| 14481 | n=14481,island_depth=5,left_edge_j=4,margin_left=0,margin_island=1,margin_right=0,retention_left=6,retention_island=3,retention_right=2,continuation_left=3,continuation_island=2,continuation_right=1 |
| 14545 | n=14545,island_depth=5,left_edge_j=4,margin_left=0,margin_island=1,margin_right=0,retention_left=6,retention_island=3,retention_right=2,continuation_left=3,continuation_island=2,continuation_right=1 |
| 14547 | n=14547,island_depth=5,left_edge_j=4,margin_left=0,margin_island=1,margin_right=0,retention_left=6,retention_island=3,retention_right=2,continuation_left=3,continuation_island=2,continuation_right=1 |
| 14551 | n=14551,island_depth=4,left_edge_j=3,margin_left=0,margin_island=2,margin_right=0,retention_left=12,retention_island=6,retention_right=4,continuation_left=6,continuation_island=4,continuation_right=2 |
| 14575 | n=14575,island_depth=3,left_edge_j=2,margin_left=-6,margin_island=1,margin_right=-1,retention_left=16,retention_island=5,retention_right=3,continuation_left=5,continuation_island=3,continuation_right=1 |
| 14633 | n=14633,island_depth=3,left_edge_j=2,margin_left=-1,margin_island=1,margin_right=0,retention_left=7,retention_island=3,retention_right=2,continuation_left=3,continuation_island=2,continuation_right=1 |
| 14757 | n=14757,island_depth=5,left_edge_j=4,margin_left=0,margin_island=1,margin_right=0,retention_left=6,retention_island=3,retention_right=2,continuation_left=3,continuation_island=2,continuation_right=1 |
| 14783 | n=14783,island_depth=4,left_edge_j=3,margin_left=-1,margin_island=1,margin_right=0,retention_left=7,retention_island=3,retention_right=2,continuation_left=3,continuation_island=2,continuation_right=1 |
| 14807 | n=14807,island_depth=5,left_edge_j=4,margin_left=0,margin_island=2,margin_right=0,retention_left=12,retention_island=6,retention_right=4,continuation_left=6,continuation_island=4,continuation_right=2 |
| 14853 | n=14853,island_depth=3,left_edge_j=2,margin_left=-2,margin_island=1,margin_right=0,retention_left=8,retention_island=3,retention_right=2,continuation_left=3,continuation_island=2,continuation_right=1 |
| 14863 | n=14863,island_depth=3,left_edge_j=2,margin_left=-1,margin_island=1,margin_right=-1,retention_left=11,retention_island=5,retention_right=3,continuation_left=5,continuation_island=3,continuation_right=1 |
| 14889 | n=14889,island_depth=3,left_edge_j=2,margin_left=-4,margin_island=1,margin_right=0,retention_left=10,retention_island=3,retention_right=2,continuation_left=3,continuation_island=2,continuation_right=1 |
| 14943 | n=14943,island_depth=3,left_edge_j=2,margin_left=0,margin_island=1,margin_right=-1,retention_left=10,retention_island=5,retention_right=3,continuation_left=5,continuation_island=3,continuation_right=1 |
| 14957 | n=14957,island_depth=3,left_edge_j=2,margin_left=0,margin_island=1,margin_right=-1,retention_left=18,retention_island=9,retention_right=5,continuation_left=9,continuation_island=5,continuation_right=2 |
| 15009 | n=15009,island_depth=4,left_edge_j=3,margin_left=0,margin_island=1,margin_right=-1,retention_left=10,retention_island=5,retention_right=3,continuation_left=5,continuation_island=3,continuation_right=1 |
| 15051 | n=15051,island_depth=5,left_edge_j=4,margin_left=-1,margin_island=2,margin_right=0,retention_left=13,retention_island=6,retention_right=4,continuation_left=6,continuation_island=4,continuation_right=2 |
| 15091 | n=15091,island_depth=3,left_edge_j=2,margin_left=-3,margin_island=1,margin_right=0,retention_left=9,retention_island=3,retention_right=2,continuation_left=3,continuation_island=2,continuation_right=1 |
| 15273 | n=15273,island_depth=4,left_edge_j=3,margin_left=0,margin_island=1,margin_right=-1,retention_left=10,retention_island=5,retention_right=3,continuation_left=5,continuation_island=3,continuation_right=1 |
| 15303 | n=15303,island_depth=4,left_edge_j=3,margin_left=0,margin_island=1,margin_right=0,retention_left=6,retention_island=3,retention_right=2,continuation_left=3,continuation_island=2,continuation_right=1 |
| 15323 | n=15323,island_depth=5,left_edge_j=4,margin_left=-1,margin_island=1,margin_right=0,retention_left=7,retention_island=3,retention_right=2,continuation_left=3,continuation_island=2,continuation_right=1 |
| 15353 | n=15353,island_depth=3,left_edge_j=2,margin_left=-8,margin_island=1,margin_right=-1,retention_left=18,retention_island=5,retention_right=3,continuation_left=5,continuation_island=3,continuation_right=1 |
| 15363 | n=15363,island_depth=4,left_edge_j=3,margin_left=0,margin_island=1,margin_right=0,retention_left=22,retention_island=11,retention_right=6,continuation_left=11,continuation_island=6,continuation_right=3 |
| 15387 | n=15387,island_depth=3,left_edge_j=2,margin_left=-2,margin_island=2,margin_right=0,retention_left=22,retention_island=10,retention_right=6,continuation_left=10,continuation_island=6,continuation_right=3 |
| 15471 | n=15471,island_depth=3,left_edge_j=2,margin_left=-3,margin_island=1,margin_right=-1,retention_left=13,retention_island=5,retention_right=3,continuation_left=5,continuation_island=3,continuation_right=1 |
| 15537 | n=15537,island_depth=5,left_edge_j=4,margin_left=0,margin_island=1,margin_right=0,retention_left=6,retention_island=3,retention_right=2,continuation_left=3,continuation_island=2,continuation_right=1 |
| 15539 | n=15539,island_depth=5,left_edge_j=4,margin_left=0,margin_island=1,margin_right=0,retention_left=6,retention_island=3,retention_right=2,continuation_left=3,continuation_island=2,continuation_right=1 |
| 15599 | n=15599,island_depth=3,left_edge_j=2,margin_left=-2,margin_island=2,margin_right=0,retention_left=14,retention_island=6,retention_right=4,continuation_left=6,continuation_island=4,continuation_right=2 |
| 15647 | n=15647,island_depth=3,left_edge_j=2,margin_left=0,margin_island=2,margin_right=0,retention_left=12,retention_island=6,retention_right=4,continuation_left=6,continuation_island=4,continuation_right=2 |
| 15657 | n=15657,island_depth=3,left_edge_j=2,margin_left=0,margin_island=1,margin_right=0,retention_left=14,retention_island=7,retention_right=4,continuation_left=7,continuation_island=4,continuation_right=2 |
| 15679 | n=15679,island_depth=4,left_edge_j=3,margin_left=0,margin_island=1,margin_right=0,retention_left=6,retention_island=3,retention_right=2,continuation_left=3,continuation_island=2,continuation_right=1 |
| 15737 | n=15737,island_depth=3,left_edge_j=2,margin_left=-2,margin_island=2,margin_right=0,retention_left=14,retention_island=6,retention_right=4,continuation_left=6,continuation_island=4,continuation_right=2 |
| 15769 | n=15769,island_depth=4,left_edge_j=3,margin_left=0,margin_island=1,margin_right=0,retention_left=6,retention_island=3,retention_right=2,continuation_left=3,continuation_island=2,continuation_right=1 |
| 15775 | n=15775,island_depth=3,left_edge_j=2,margin_left=-4,margin_island=1,margin_right=-1,retention_left=14,retention_island=5,retention_right=3,continuation_left=5,continuation_island=3,continuation_right=1 |
| 15967 | n=15967,island_depth=3,left_edge_j=2,margin_left=0,margin_island=1,margin_right=0,retention_left=6,retention_island=3,retention_right=2,continuation_left=3,continuation_island=2,continuation_right=1 |
| 15977 | n=15977,island_depth=3,left_edge_j=2,margin_left=0,margin_island=1,margin_right=0,retention_left=14,retention_island=7,retention_right=4,continuation_left=7,continuation_island=4,continuation_right=2 |
| 16047 | n=16047,island_depth=3,left_edge_j=2,margin_left=0,margin_island=1,margin_right=0,retention_left=14,retention_island=7,retention_right=4,continuation_left=7,continuation_island=4,continuation_right=2 |
| 16079 | n=16079,island_depth=5,left_edge_j=4,margin_left=-2,margin_island=1,margin_right=-1,retention_left=12,retention_island=5,retention_right=3,continuation_left=5,continuation_island=3,continuation_right=1 |
| 16097 | n=16097,island_depth=3,left_edge_j=2,margin_left=0,margin_island=1,margin_right=0,retention_left=6,retention_island=3,retention_right=2,continuation_left=3,continuation_island=2,continuation_right=1 |
| 16127 | n=16127,island_depth=5,left_edge_j=4,margin_left=0,margin_island=2,margin_right=0,retention_left=12,retention_island=6,retention_right=4,continuation_left=6,continuation_island=4,continuation_right=2 |
| 16183 | n=16183,island_depth=4,left_edge_j=3,margin_left=-1,margin_island=1,margin_right=0,retention_left=23,retention_island=11,retention_right=6,continuation_left=11,continuation_island=6,continuation_right=3 |
| 16293 | n=16293,island_depth=5,left_edge_j=4,margin_left=0,margin_island=1,margin_right=0,retention_left=6,retention_island=3,retention_right=2,continuation_left=3,continuation_island=2,continuation_right=1 |
| 16297 | n=16297,island_depth=3,left_edge_j=2,margin_left=-1,margin_island=1,margin_right=0,retention_left=15,retention_island=7,retention_right=4,continuation_left=7,continuation_island=4,continuation_right=2 |
| 16365 | n=16365,island_depth=5,left_edge_j=4,margin_left=0,margin_island=1,margin_right=0,retention_left=6,retention_island=3,retention_right=2,continuation_left=3,continuation_island=2,continuation_right=1 |

## Reading

The scan keeps time profiles and pressure-depth profiles separate.  The
current data should be used to decide whether the next Lean predicate is a
positive block, a local-island existence predicate, or a frontier-below
predicate.

This is not evidence for an unconditional pressure-prefix theorem.  The
presence of local islands and sign-change-up rows means pressure is a
margin sign profile, not just carrier nesting.

Checkpoint 132 adds the direct all-ones-depth observable
`v2(residual + 1)`.  This separates the previous residue-class signal
from the actual low-bit all-ones concentration inside the window.


## Frontier Depth By Residual Mod 16 First

| residual mod 16 first | frontier depth counts |
|---:|---|
| 1 | 2:485;3:20;4:1 |
| 3 | 2:462;3:4;4:5 |
| 5 | 2:449;3:8 |
| 7 | 2:576;3:15;4:1 |
| 9 | 2:483;3:45;4:4;5:3 |
| 11 | 2:499;3:18;4:5;5:3 |
| 13 | 2:465;3:13;4:3;5:3 |
| 15 | 2:751;3:88;4:12 |

## Frontier Depth By Residual Mod 16 Mode

| residual mod 16 mode | frontier depth counts |
|---:|---|
| 1 | 2:3618;3:208;4:31;5:9 |
| 7 | 2:230 |
| 9 | 2:11 |
| 11 | 2:25;3:3 |
| 15 | 2:286 |

## Frontier Depth By Residual Mod 32 First

| residual mod 32 first | frontier depth counts |
|---:|---|
| 1 | 2:255;3:17;4:1 |
| 3 | 2:227;3:2;4:1 |
| 5 | 2:223;3:7 |
| 7 | 2:297;3:12;4:1 |
| 9 | 2:289;3:29;4:1 |
| 11 | 2:254;3:3;4:1 |
| 13 | 2:214;3:4;4:1;5:1 |
| 15 | 2:323;3:32 |
| 17 | 2:230;3:3 |
| 19 | 2:235;3:2;4:4 |
| 21 | 2:226;3:1 |
| 23 | 2:279;3:3 |
| 25 | 2:194;3:16;4:3;5:3 |
| 27 | 2:245;3:15;4:4;5:3 |
| 29 | 2:251;3:9;4:2;5:2 |
| 31 | 2:428;3:56;4:12 |

## Frontier Depth By Residual Mod 32 Mode

| residual mod 32 mode | frontier depth counts |
|---:|---|
| 1 | 2:3675;3:208;4:31;5:9 |
| 3 | 2:6 |
| 5 | 2:24 |
| 7 | 2:111 |
| 9 | 2:78 |
| 11 | 2:1 |
| 15 | 2:69 |
| 19 | 2:2 |
| 23 | 2:20 |
| 27 | 2:54;3:3 |
| 29 | 2:8 |
| 31 | 2:122 |

## Positive Block Length By Residual Mod 16 First

| residual mod 16 first | max block length counts |
|---:|---|
| 1 | 0:520;1:378;2:56;3:23;4:32;5:8;6:3;7:1;8:3;10:2 |
| 3 | 0:552;1:357;2:35;3:20;4:33;5:14;6:3;7:3;8:5;10:1 |
| 5 | 0:568;1:357;2:40;3:16;4:29;5:7;6:6;8:2 |
| 7 | 0:433;1:452;2:70;3:10;4:29;5:14;6:8;7:2;8:4;10:3 |
| 9 | 0:488;1:347;2:71;3:38;4:38;5:19;6:10;7:2;8:8;10:2 |
| 11 | 0:499;1:367;2:47;3:42;4:30;5:17;6:8;7:1;8:9;9:1;10:3 |
| 13 | 0:539;1:337;2:58;3:25;4:34;5:20;6:3;7:2;8:4;10:1 |
| 15 | 0:172;1:371;2:193;3:88;4:97;5:44;6:26;7:15;8:7;9:2;10:7;11:1 |

## Positive Block Length By Residual Mod 32 First

| residual mod 32 first | max block length counts |
|---:|---|
| 1 | 0:241;1:195;2:33;3:16;4:19;5:3;6:3;8:2;10:2 |
| 3 | 0:281;1:187;2:10;3:8;4:18;5:4;6:2;8:1 |
| 5 | 0:284;1:175;2:22;3:7;4:18;5:2;6:4;8:2 |
| 7 | 0:203;1:231;2:39;3:9;4:12;5:7;6:6;7:2;8:2;10:2 |
| 9 | 0:192;1:204;2:42;3:25;4:25;5:10;6:6;7:2;8:3;10:2 |
| 11 | 0:255;1:198;2:19;3:8;4:20;5:5;6:2;8:4;10:2 |
| 13 | 0:292;1:163;2:19;3:12;4:14;5:8;8:4 |
| 15 | 0:156;1:236;2:76;3:12;4:13;5:11;6:3;7:1;10:3 |
| 17 | 0:279;1:183;2:23;3:7;4:13;5:5;7:1;8:1 |
| 19 | 0:271;1:170;2:25;3:12;4:15;5:10;6:1;7:3;8:4;10:1 |
| 21 | 0:284;1:182;2:18;3:9;4:11;5:5;6:2 |
| 23 | 0:230;1:221;2:31;3:1;4:17;5:7;6:2;8:2;10:1 |
| 25 | 0:296;1:143;2:29;3:13;4:13;5:9;6:4;8:5 |
| 27 | 0:244;1:169;2:28;3:34;4:10;5:12;6:6;7:1;8:5;9:1;10:1 |
| 29 | 0:247;1:174;2:39;3:13;4:20;5:12;6:3;7:2;10:1 |
| 31 | 0:16;1:135;2:117;3:76;4:84;5:33;6:23;7:14;8:7;9:2;10:4;11:1 |

## Positive Block Length By All-Ones Depth First

| all-ones depth first | max block length counts |
|---:|---|
| 1 | 0:2115;1:1419;2:225;3:102;4:133;5:54;6:22;7:5;8:17;10:5 |
| 2 | 0:1051;1:724;2:82;3:62;4:63;5:31;6:11;7:4;8:14;9:1;10:4 |
| 3 | 0:433;1:452;2:70;3:10;4:29;5:14;6:8;7:2;8:4;10:3 |
| 4 | 0:156;1:236;2:76;3:12;4:13;5:11;6:3;7:1;10:3 |
| 5 | 0:16;1:109;2:75;3:32;4:16;5:4;6:1;7:2;10:2 |
| 6 | 1:23;2:31;3:37;4:31;5:4;7:1 |
| 7 | 1:3;2:7;3:7;4:32;5:15;6:1 |
| 8 | 2:4;4:5;5:9;6:13 |
| 9 | 5:1;6:8;7:8 |
| 10 | 7:3;8:4 |
| 11 | 8:3;9:2 |
| 12 | 10:1 |
| 13 | 10:1;11:1 |

## Positive Block Length By All-Ones Depth Mode

| all-ones depth mode | max block length counts |
|---:|---|
| 1 | 0:3771;1:2966;2:570;3:262;4:322;5:143;6:67;7:26;8:42;9:3;10:19;11:1 |

## Positive Block Length By All-Ones Depth Max

| all-ones depth max | max block length counts |
|---:|---|
| 1 | 0:147 |
| 2 | 0:782 |
| 3 | 0:1670;1:22 |
| 4 | 0:878;1:120;2:6 |
| 5 | 0:207;1:310;2:49;3:14 |
| 6 | 0:87;1:2445;2:401;3:141;4:25 |
| 7 | 1:57;2:93;3:101;4:201;5:10 |
| 8 | 1:12;2:21;3:6;4:96;5:127;6:13 |
| 9 | 5:3;6:54;7:8 |
| 10 | 5:3;7:18;8:4 |
| 11 | 8:38;9:2 |
| 12 | 9:1;10:1 |
| 13 | 10:18;11:1 |

## Positive Block Length By Count All-Ones Depth Ge 4

| count all-ones depth ge 4 | max block length counts |
|---:|---|
| 0 | 0:2599;1:22 |
| 1 | 0:693;1:86;2:4 |
| 2 | 0:232;1:109;2:24;3:12 |
| 3 | 0:113;1:149;2:44;3:50;4:12 |
| 4 | 0:29;1:143;2:65;3:18;4:141;5:4 |
| 5 | 0:74;1:460;2:87;3:8;4:42;5:35;6:2 |
| 6 | 0:22;1:518;2:72;3:21;4:9;5:38;6:24;7:1 |
| 7 | 0:6;1:843;2:22;3:46;4:10;5:10;6:13;7:1 |
| 8 | 0:3;1:413;2:30;3:3;4:7;5:14;6:6;7:1 |
| 9 | 1:120;2:38;3:9;4:32;5:13 |
| 10 | 1:48;2:40;3:12;4:24;5:22;6:1 |
| 11 | 1:42;2:40;3:26;4:6;5:2;6:7 |
| 12 | 1:12;2:74;3:7;4:9;5:2;6:3;7:1;8:1 |
| 13 | 1:1;2:20;3:35;4:7;5:1;6:1;7:5;8:1 |
| 14 | 2:9;3:2;4:4;6:10;7:8;8:3 |
| 15 | 2:1;3:12;4:3;7:1;8:37;9:2 |
| 16 | 3:1;4:10;5:1;7:5;9:1;10:1 |
| 17 | 4:4;5:1;7:3;10:5;11:1 |
| 18 | 4:2;10:2 |
| 19 | 10:1 |
| 20 | 10:4 |
| 21 | 10:5 |
| 22 | 10:1 |

## Positive Block Length By Count All-Ones Depth Ge 5

| count all-ones depth ge 5 | max block length counts |
|---:|---|
| 0 | 0:3477;1:142;2:6 |
| 1 | 0:184;1:232;2:41;3:12 |
| 2 | 0:101;1:1240;2:143;3:54;4:18 |
| 3 | 0:9;1:1196;2:130;3:28;4:173;5:10 |
| 4 | 1:104;2:79;3:63;4:19;5:76;6:6 |
| 5 | 1:23;2:63;3:20;4:18;5:13;6:33;7:2 |
| 6 | 1:29;2:95;3:34;4:53;5:4;6:8;7:1 |
| 7 | 2:12;3:37;4:8;5:33;6:2;7:2 |
| 8 | 2:1;3:14;4:10;5:2;6:11;7:4;8:2 |
| 9 | 4:4;5:2;6:7;7:2;8:1 |
| 10 | 4:3;5:1;7:2;9:1 |
| 11 | 4:14;5:1;7:8;8:2;9:1 |
| 12 | 4:2;7:4;8:37;9:1;10:2 |
| 13 | 5:1;7:1;10:8;11:1 |
| 14 | 10:7 |
| 15 | 10:2 |

## Positive Block Length By Count All-Ones Depth Ge 6

| count all-ones depth ge 6 | max block length counts |
|---:|---|
| 0 | 0:3684;1:452;2:55;3:14 |
| 1 | 0:87;1:2401;2:280;3:60;4:18 |
| 2 | 1:80;2:196;3:104;4:184;5:10 |
| 3 | 1:21;2:20;3:83;4:30;5:88;6:7 |
| 4 | 1:12;2:19;3:1;4:58;5:4;6:42;7:2 |
| 5 | 4:13;5:34;6:10;7:5 |
| 6 | 4:4;5:4;6:2;7:4;8:2 |
| 7 | 4:15;5:2;6:6;7:2;8:1 |
| 8 | 7:12;8:2;9:2;10:1 |
| 9 | 5:1;7:1;8:37;9:1;10:1 |
| 10 | 10:17;11:1 |

## Frontier Depth By All-Ones Depth First

| all-ones depth first | frontier depth counts |
|---:|---|
| 1 | 2:1882;3:86;4:8;5:6 |
| 2 | 2:961;3:22;4:10;5:3 |
| 3 | 2:576;3:15;4:1 |
| 4 | 2:323;3:32 |
| 5 | 2:204;3:30;4:7 |
| 6 | 2:110;3:13;4:4 |
| 7 | 2:55;3:9;4:1 |
| 8 | 2:27;3:4 |
| 9 | 2:17 |
| 10 | 2:7 |
| 11 | 2:5 |
| 12 | 2:1 |
| 13 | 2:2 |

## Frontier Depth By All-Ones Depth Max

| all-ones depth max | frontier depth counts |
|---:|---|
| 3 | 2:22 |
| 4 | 2:104;3:22 |
| 5 | 2:288;3:78;4:7 |
| 6 | 2:2940;3:62;4:10 |
| 7 | 2:400;3:39;4:14;5:9 |
| 8 | 2:266;3:9 |
| 9 | 2:64;3:1 |
| 10 | 2:25 |
| 11 | 2:40 |
| 12 | 2:2 |
| 13 | 2:19 |

## Frontier Depth By Count All-Ones Depth Ge 4

| count all-ones depth ge 4 | frontier depth counts |
|---:|---|
| 0 | 2:22 |
| 1 | 2:72;3:18 |
| 2 | 2:89;3:50;4:6 |
| 3 | 2:194;3:53;4:8 |
| 4 | 2:331;3:38;4:2 |
| 5 | 2:594;3:27;4:13 |
| 6 | 2:653;3:19;4:2;5:9 |
| 7 | 2:943;3:2 |
| 8 | 2:474 |
| 9 | 2:209;3:3 |
| 10 | 2:146;3:1 |
| 11 | 2:123 |
| 12 | 2:109 |
| 13 | 2:71 |
| 14 | 2:36 |
| 15 | 2:56 |
| 16 | 2:19 |
| 17 | 2:14 |
| 18 | 2:4 |
| 19 | 2:1 |
| 20 | 2:4 |
| 21 | 2:5 |
| 22 | 2:1 |

## Local Island Rows By Residual Mod 16 First

| residual mod 16 first | local island count rows |
|---:|---|
| 1 | 1:16 |
| 3 | 1:20 |
| 5 | 1:9 |
| 7 | 1:34 |
| 9 | 1:43 |
| 11 | 1:29 |
| 13 | 1:22 |
| 15 | 1:79 |

## Sign-Change-Up Rows By Residual Mod 16 First

| residual mod 16 first | sign-change-up count rows |
|---:|---|
| 1 | 1:30 |
| 3 | 1:29 |
| 5 | 1:13 |
| 7 | 1:44 |
| 9 | 1:72 |
| 11 | 1:52 |
| 13 | 1:31 |
| 15 | 1:133 |

## Local Island Rows By All-Ones Depth First

| all-ones depth first | local island count rows |
|---:|---|
| 1 | 1:90 |
| 2 | 1:49 |
| 3 | 1:34 |
| 4 | 1:39 |
| 5 | 1:24 |
| 6 | 1:11 |
| 7 | 1:5 |

## Local Island Rows By All-Ones Depth Max

| all-ones depth max | local island count rows |
|---:|---|
| 4 | 1:22 |
| 5 | 1:72 |
| 6 | 1:47 |
| 7 | 1:82 |
| 8 | 1:28 |
| 10 | 1:1 |

## Local Island Rows By Count All-Ones Depth Ge 4

| count all-ones depth ge 4 | local island count rows |
|---:|---|
| 1 | 1:18 |
| 2 | 1:44 |
| 3 | 1:29 |
| 4 | 1:19 |
| 5 | 1:27 |
| 6 | 1:49 |
| 7 | 1:7 |
| 9 | 1:5 |
| 10 | 1:7 |
| 11 | 1:20 |
| 12 | 1:15 |
| 13 | 1:11 |
| 17 | 1:1 |

## Sign-Change-Up Rows By All-Ones Depth First

| all-ones depth first | sign-change-up count rows |
|---:|---|
| 1 | 1:146 |
| 2 | 1:81 |
| 3 | 1:44 |
| 4 | 1:41 |
| 5 | 1:39 |
| 6 | 1:26 |
| 7 | 1:19 |
| 8 | 1:8 |

## Sign-Change-Up Rows By All-Ones Depth Max

| all-ones depth max | sign-change-up count rows |
|---:|---|
| 4 | 1:22 |
| 5 | 1:86 |
| 6 | 1:89 |
| 7 | 1:156 |
| 8 | 1:47 |
| 9 | 1:1 |
| 10 | 1:3 |

## Sign-Change-Up Rows By Count All-Ones Depth Ge 4

| count all-ones depth ge 4 | sign-change-up count rows |
|---:|---|
| 1 | 1:18 |
| 2 | 1:56 |
| 3 | 1:63 |
| 4 | 1:45 |
| 5 | 1:69 |
| 6 | 1:66 |
| 7 | 1:9 |
| 9 | 1:13 |
| 10 | 1:13 |
| 11 | 1:25 |
| 12 | 1:15 |
| 13 | 1:11 |
| 17 | 1:1 |

## Sign-Change-Up Depth Counts

- depth counts: `2:211; 3:91; 4:101; 7:1`
- cause counts: `retention_drop_dominant:404`
