# Codex Start — ABC/GN Balance Calibration

Work only on:

```text
repository: Deskuma/dkmath
branch: research/ABC-GN-balance-calibration-260915-v0
```

Accepted checkpoints:

```text
BCAL-000 — Outcome A
commit: 39022f480db874c91432f4c114bb7e1c3661fa5b

BCAL-001 — Outcome A
commit: 748adca6ee93715ecf5d30c90ed2352f7e0d23c2

BCAL-002 — Outcome A
commit: 670acf204798d7965f32faffb0e1ab5ac1102282

BCAL-003 — Outcome A
commit: d083a6a2b9752baa1524ceab80dfd5ddc58966a8

BCAL-004 — Outcome B / PARTIAL BRIDGE
commit: e211e0472280515ff0adca8f2b287a387fa1e2c1

BCAL-005 — Outcome A / EXACT EXCEPTIONAL COMPLETION
commit: 7aa08d384b8c6b21c5da095e73964cc5ba15d8b2
```

Read in this order:

```text
lean/dk_math/docs/dev/ABC-GN-balance-calibration-260915-v0/README.md
lean/dk_math/docs/dev/ABC-GN-balance-calibration-260915-v0/report-005.md
lean/dk_math/docs/dev/ABC-GN-balance-calibration-260915-v0/instruction-006.md
```

Then execute `instruction-006.md` repository-first.

Current core rule:

```text
BCAL-005 completed the full cubic exceptional bookkeeping exactly.
The next task is a bounded depth-step / finite Hensel transport audit.
Do not infer Hensel lift existence from Hensel uniqueness.
Do not identify q^k divisibility with exact valuation k.
Do not return to exponent optimization.
Do not construct a new ABC contract.
```

Established exact structure:

```text
localMass(q)    = v_q(GN) * log q
localBalance(q) = (2 - v_q(GN)) * log q

exact valuation +1
  should algebraically imply:
    localMass    + log q
    localBalance - log q
```

Existing finite Hensel infrastructure already provides, in the non-exceptional simple-root channel:

```text
GNDeepLiftCongruenceUnique_of_simpleRoot
GNDeepLiftReductionInjective_of_simpleRoot
GNDeepLiftResidues_card_le_of_simpleRoot
```

but these are uniqueness/counting statements, not lift-existence statements.

Checkpoint 006 should distinguish and formalize, where valid:

```text
A. explicit exact-valuation successor law
B. canonical downward reduction: depth k+1 -> depth k
C. simple-root injectivity of that successor reduction
D. card R_(k+1) <= card R_k
```

Do not strengthen the final inequality to equality without a separately audited existence theorem.

Write results and build/audit evidence to:

```text
lean/dk_math/docs/dev/ABC-GN-balance-calibration-260915-v0/report-006.md
```
