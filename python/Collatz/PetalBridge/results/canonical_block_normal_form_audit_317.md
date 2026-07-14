# Canonical Block Normal-Form Audit (cp-317)

This is finite computational evidence, not a Lean theorem.

## Range

- exhaustive odd roots: `1..131071` (65536 roots)
- deterministic random roots: 1280 over widths (64, 128, 256, 512, 1024)
- random seed: `54039`
- per-root block limit: `4096`
- exact normal-form trace roots: `9472`

## Results

- every audited block passed the exact normal-form transition assertions
- first `queue > initial bitWidth` counterexample: none observed
- largest observed queue: `15` at root `13007082825098195174285279455291089318240773657547195000348700458518007247903840970390548671397537876859751635784391081095674028805451362190390027793449173` (initial width `512`)

## Finite Signature Diagnostics

| w | signatures | drift collisions | max drift spread | nondeterministic successors | realized positive repeated segments |
| --- | --- | --- | --- | --- | --- |
| 5 | 2562 | 514 | 18 | 2477 | 419 |
| 6 | 9785 | 363 | 17 | 8411 | 103 |
| 7 | 31053 | 369 | 15 | 24807 | 10 |
| 8 | 90457 | 476 | 15 | 65724 | 5 |

The candidate signatures use capped length, capped terminal valuation, capped claim count,
the low `w` core bits, and the high `w` start-state bits.  A collision or nondeterministic
successor is evidence that this projection is not an exact automaton state.  Absence of an
observed collision would still not establish projection soundness.
