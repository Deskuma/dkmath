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
```

Read in this order:

```text
lean/dk_math/docs/dev/ABC-GN-balance-calibration-260915-v0/README.md
lean/dk_math/docs/dev/ABC-GN-balance-calibration-260915-v0/report-004.md
lean/dk_math/docs/dev/ABC-GN-balance-calibration-260915-v0/instruction-005.md
```

Then execute `instruction-005.md` repository-first.

Current core rule:

```text
BCAL-004 already found the exact non-exceptional shell bridge.
Do not hide the cubic exceptional prime 3 behind a side condition.
Expose its exact single-layer contribution and recover an unconditional full-shell identity.
Reuse the BCAL-002 exceptional gauge coordinate.
Do not return to exponent optimization.
Do not prove Hensel transport yet.
Do not construct a new ABC contract.
```

Established exact structure:

```text
local balance(q) = (2 - v_q(GN)) * log q

GNChannelBalance
  = log(nonExceptionalSingleLayer)
    - log(twoTail(nonExceptionalPart))
```

In the cubic family `GN 3 a 1`, prime `3` has valuation at most one.  Therefore it never enters the repeated part / `twoTail`, but it may remain in the full cubic squarefree complement while the BCAL non-exceptional channel omits it.

Checkpoint 005 should test and, if valid, formalize the exact completion:

```text
full cubic complement
  = exceptional support product
    * non-exceptional single layer
```

and hence an unconditional identity of the form

```text
GNChannelBalance
  = log(full cubic complement)
    - log(full twoTail)
    - log(exceptional support product).
```

Then rewrite the exceptional-support term through

```text
GNExceptionalGaugeSlack
  = log(rad 3) - log(exceptional support product).
```

The goal is to show that the BCAL-004 mismatch is exactly the already-known exceptional gauge coordinate, not a new error term.

Write results and build/audit evidence to:

```text
lean/dk_math/docs/dev/ABC-GN-balance-calibration-260915-v0/report-005.md
```
