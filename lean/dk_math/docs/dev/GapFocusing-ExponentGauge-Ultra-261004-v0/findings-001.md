# Gap Focusing / Exponent Gauge Ultra — Findings 001

Branch: **research/GapFocusing-ExponentGauge-Ultra-261004-v0**

Base: current `develop` after merged PR #112.

This file is the durable incremental state of the Ultra exploration.

## Current status

- Workspace initialized.
- No A/B/C outcome selected.
- No production theorem changes have been made.

## Starting picture

General power-difference coordinates:

```text
a = x + u
b = u
a - b = x
```

Focused power difference:

```text
(x+u)^d - u^d = x * GN_d(x,u).
```

Unfocused comparison anchor:

```text
(x+u)^d - v^d
  = x * GN_d(x,u) + (u^d-v^d).
```

Working interpretation only:

```text
u^d-v^d = focus defect.
```

This interpretation must be tested rather than assumed.

## Candidate structural chain

```text
general power difference
-> Gap focus
-> trivial/nontrivial cyclotomic phase split
-> composite/prime degree behavior
-> possible residual exponent/unit gauge.
```

No theorem currently asserts the whole chain.

## Questions to resolve

| Question | Status |
| --- | --- |
| Is the x-factorization canonical after fixing the anchor u? | TBD |
| Is x-divisibility equivalent to zero focus defect in a useful generic setting? | TBD |
| Is the zeta=1 phase uniquely u-free? | TBD |
| Does GN product-degree decomposition characterize composite degree structurally? | TBD |
| Is there an honest Prime Degree Rigidity theorem? | TBD |
| Does focused phase freedom explain the FLT unit-power class? | TBD |
| What does 2p=p*2 encode before any geometric interpretation? | TBD |

## Prior result to preserve

Merged PR #112 established:

```text
fixed order/source/ramifier
A = lambda * u * beta^p
[u] in R^×/(R^×)^p
```

with root-choice independence and normalization dependence on the actual p=3,
p=5, and p=7 production rings.

This run must not silently strengthen that result.

## Next action

Inventory current GN, cyclotomic, DRC, and power-difference APIs, then decide
the smallest neutral Lean probe needed to distinguish structural focusing from
mere coordinate substitution.

## Checkpoint history

### 2026-10-04 checkpoint 00 — workspace seed

- PR #112 verified merged to `develop`.
- New research branch created from current `develop`.
- Exploration intentionally separates algebraic facts from the Gap-focusing
  interpretation.
- Magic-square / planar 2p remains a downstream calibration question only.
