# FLT3/5/7 Cross-Invariant Ultra — Findings 001

Branch: **research/FLT357-CrossInvariant-Ultra-261004-v0**

Base: FLT7 Ultra PR #111 head
`3c1930be8a911591f364d2adcbc62b4165e1948d`.

This file is the durable incremental result of a bounded pre-audit.  Update it
during research; do not reserve discoveries for a final report.

## Current status

- Requested branch verified at initial HEAD `69d44fa3e`; initial tree clean.
- Lean/Mathlib `v4.34.1`. Initial source inventory complete; no production edits.
- A/B/C assessment remains open until exact completed p=3/p=5 spines are mapped.
- Starting observation from p=7:
  `(A)=P7*J^7`, `A=lambda*u*beta^7`;
  the unit/additive-descent layers remain open.
- Goal: project that layer decomposition backward onto the completed p=3 and
  p=5 proofs without forcing false carrier equivalences.

## Cross-exponent matrix

| Layer | p=3 | p=5 | p=7 |
| --- | --- | --- | --- |
| production carrier | `EisensteinInt := TraceOneInt (-1)` | real quadratic `GoldenInt` | current degree-six cyclotomic carrier + real-cubic source |
| ramified correction | `alpha=(1+tau)*beta` | `alpha=(2+phi)*beta` | exact P7 exponent 1 / one lambda extracted |
| normalized ideal p-th power | element cube via conjugate coprimality and Euclidean GCD; ideal form not stored | element fifth power via conjugate coprimality and Euclidean GCD; ideal form not stored | proved for all current phases |
| unit / phase class | three cube sectors, then coefficient exclusion | five Golden fifth-power sectors, then coefficient exclusion | retained as u; new class not yet closed |
| additive landing | TBD | TBD | not reconstructed from beta |
| strict descent / contradiction | positive primitive cubic packet; product a*b*c | Golden zero-sector packet; absolute second coordinate | not reached |
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

- Complete exact p=3/p=5 closure maps and the p=7 layer comparison.
- Test whether the corrected algebraic power/unit class is a real common
  invariant, while retaining carrier, coordinate landing, and descent-state differences.
- Checkpoint before any focused Lean validation; keep all changes within this
  pre-audit documentation and optional scratch files.

## Checkpoint history

### 2026-10-04 checkpoint 00 — workspace seed

- New branch created from the FLT7 Ultra PR #111 head so the p=7 ramified
  correction is available to the cross-exponent audit.
- This run is intentionally bounded by the current usage window.
- Durable findings take priority over implementation and full builds.

### 2026-10-04 checkpoint 01 — Initial live inventory

- Verified requested branch and clean initial tree. Baseline `69d44fa3e`.
- Current p=7 source endpoints found in `CurrentCarrierNormalizedPower` and
  `CurrentSupportObstruction`: corrected `(A)=P7*J^7`, `A=lambda*u*beta^7`,
  raw ramified exponent1 and all other exponents seventh-multiple.
- Current `DkMath.FLT.Prime` facade is explicitly bounded: ramified packets,
  away simultaneous powers, conditional quadratic TraceOne extraction,
  class-group/unit/sector interfaces. It is not the full degree-six p=7 closure.
- Initial source mapping from parallel audits: p=3 and p=5 both use direct
  element GCD/UFD power extraction in norm-Euclidean quadratic orders, rather
  than exposing a normalized ideal-power packet. Do not infer that a missing
  ideal declaration is missing mathematical power extraction.
- p=3 descent returns a positive primitive cubic packet and decreases a*b*c.
  p=5 descent instead reconstructs a Golden zero-sector packet and decreases
  |second coordinate|. They are completed through different invariant states.
- Candidate common algebraic stage: chosen-order ramifier correction plus
  unit class modulo p-th powers and exact integral coefficient constraints.
  This is a candidate observation, not a new theorem with encoded conclusions.
- Next: complete each source map, then record candidate state coordinates and
  run small centralized axiom/provenance probes after a dedicated checkpoint.
  No full build or production refactor is planned.
