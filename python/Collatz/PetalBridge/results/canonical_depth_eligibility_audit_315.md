# Canonical Depth Eligibility Audit (cp-315)

Claim prefix: 1024 blocks. Capacity horizon: 4096 blocks.
This is finite computational evidence, not a Lean theorem.

| root | claim_blocks | horizon_blocks | prefix_claims | prefix_paid | prefix_outstanding | prefix_outstanding_detail | first_state_one_time | prefix_max_lag | stream_outstanding | stream_max_total_queue | stream_max_level_two_queue | depth1_depth2_collisions | collisions_with_one_level_two_slot | first_depth1_depth2_collision | prefix_candidate_survived |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| 7 | 1024 | 4096 | 1025 | 1025 | 0 | none | 5 | 1 | 0 | 1 | 0 | 0 | 0 | none | True |
| 27 | 1024 | 4096 | 1032 | 1031 | 1 | b9:d5->l5 | 41 | 14 | 1 | 6 | 1 | 1 | 1 | b7:endpoint20:height2 | False |
| 31 | 1024 | 4096 | 1032 | 1031 | 1 | b8:d5->l5 | 39 | 14 | 1 | 6 | 1 | 1 | 1 | b6:endpoint18:height2 | False |
| 511 | 1024 | 4096 | 1027 | 1025 | 2 | b0:d8->l8;b0:d9->l9 | 20 | 2 | 2 | 5 | 0 | 0 | 0 | none | False |
