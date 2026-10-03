# FLT3/5/7 Cross-Invariant Ultra — Findings 001

Branch: **research/FLT357-CrossInvariant-Ultra-261004-v0**

Base: FLT7 Ultra PR #111 head
`3c1930be8a911591f364d2adcbc62b4165e1948d`.

This file is the durable incremental result of a bounded pre-audit.  Update it
during research; do not reserve discoveries for a final report.

## Current status

- Workspace initialized.
- No A/B/C outcome selected yet.
- Starting observation from p=7:
  `(A)=P7*J^7`, `A=lambda*u*beta^7`;
  the unit/additive-descent layers remain open.
- Goal: project that layer decomposition backward onto the completed p=3 and
  p=5 proofs without forcing false carrier equivalences.

## Cross-exponent matrix

| Layer | p=3 | p=5 | p=7 |
| --- | --- | --- | --- |
| production carrier | TBD | TBD | current degree-six cyclotomic carrier + real-cubic source |
| ramified correction | TBD | TBD | exact P7 exponent 1 / one lambda extracted |
| normalized ideal p-th power | TBD | TBD | proved for all current phases |
| unit / phase class | TBD | TBD | retained as u; new class not yet closed |
| additive landing | TBD | TBD | not reconstructed from beta |
| strict descent / contradiction | TBD | TBD | not reached |
| first unresolved obstruction | TBD | TBD | current normalized unit class, then successor landing |

## Candidate invariant / common schema

None accepted yet.

Working probe only:

```text
A_p = lambda_p^r * u_p * beta_p^p
```

possibly refined into a tuple of discrete obstruction coordinates.  This must be
validated against the actual p=3 and p=5 production routes.

## Evidence that may indicate stripe / sector behavior

Initial known architecture to re-audit:

- generic odd-prime summary branches unit behavior by `p % 4`;
- p=3 has a recorded carrier/API boundary in that facade;
- p=5 historically uses GoldenInt while generic work also uses TraceOne-style
  carriers;
- p=7 now exposes a mandatory ramified correction in the current degree-six
  carrier.

These are starting questions, not final conclusions.

## Failed / blocked unifications

None yet.

## p=11 / p=13 forecast

Not started.  Do not speculate until the 3/5/7 matrix is source-grounded.

## Next action

Inventory the production FLT3 and FLT5 proof spines and map their actual
carrier, ramification, ideal-power, unit, landing, and descent endpoints.
Then compare them with the current FLT7 stack before proposing an abstraction.

## Checkpoint history

### 2026-10-04 checkpoint 00 — workspace seed

- New branch created from the FLT7 Ultra PR #111 head so the p=7 ramified
  correction is available to the cross-exponent audit.
- This run is intentionally bounded by the current usage window.
- Durable findings take priority over implementation and full builds.
