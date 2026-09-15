# ABC–GN Balance / Calibration Roadmap

This roadmap is intentionally structure-first.

Numerical exponents and uniform bounds are postponed until the balance law and calibration mechanism are explicit.

## BCAL-000 — Coordinate extraction

Goal:

```text
S = fresh support mass
E = repeated valuation-depth mass
M = S + E
Q = S - E
Cal = M - ρR
```

Production target:

```text
joint pressure iff Cal <= C
```

No new arithmetic bound.

Status: **complete / Outcome A** at commit `39022f480db874c91432f4c114bb7e1c3661fa5b`.

## BCAL-001 — Outer ABC balance bridge / pointwise calibration

Place the GN calibration coordinate and the already-existing outer ABC coordinate in one bridge layer:

```text
outer imbalance:
  abcGap
  = valuationExcess(c) - log(rad(ab))
  = abcEpsilon * radLog

inner GN calibration:
  Cal = S + E - ρ*radLog
```

The key refinement after BCAL-000 is to remove the arbitrary allowance `C` from the pointwise view and expose the actual correction attached to one triple:

```text
pointwiseCorrection(T,p,ρ)
  = (Cal(T,p,ρ) + log(rad p))
      / ((p-1) * radLog(T)).
```

Re-express the existing epsilon bridge directly from this pointwise residual, then show that a uniform allowance `Cal <= C` envelopes the pointwise correction when clean.

This checkpoint must distinguish exactly:

```text
slope term       GNEpsilon(p,ρ)
pointwise residual Cal(T,p,ρ)
uniform allowance C
fixed-p term     log(rad p)
scale            (p-1)*radLog(T)
```

Also expose the outer ABC support/depth mass coordinates and the exact outer balance `ABCOuterBalance = abcGap`.

No attempt to bound `Cal` uniformly.

Status: **active via `instruction-001.md`**.

## BCAL-002 — Calibration-source decomposition audit

Inventory every place where the existing derivation loses equality or adds an affine allowance.

Classify each contribution as one of:

```text
exact structural mass
exceptional-support correction
fixed-exponent gauge correction
transport inequality slack
positivity/safe-envelope slack
uniformization allowance
```

The main question is whether the present field `C` can be replaced by an exact sum of named residual components before any uniform bound is attempted.

Expected output may be documentation-only if no new exact theorem is justified.

## BCAL-003 — Balance transport under local arithmetic operations

Study the signed coordinate

```text
Q = S - E
```

under already-formalized operations only:

```text
fresh-prime return
Hensel / repeated-depth growth
exceptional vs non-exceptional split
orientation changes when available
prime-exponent specialization
```

Targets should be exact transformation identities or one-step inequalities derived from existing theorems.

Do not state global monotonicity without proof.

## BCAL-004 — Cubic shell coordinate bridge

For the cubic specialization, compare the GN balance coordinates with the shell decomposition

```text
F(a) = M_shell * S_shell
```

where `M_shell` is the complete repeated/square-full part and `S_shell` is the squarefree complement.

Introduce logarithmic shell coordinates only after exact production identities have been inventoried:

```text
shellMass    = log(M_shell) + log(S_shell)
shellBalance = log(M_shell) - log(S_shell)
```

Research question:

```text
Does an exact or monotone transport exist between
  GNChannelBalance
and
  shellBalance ?
```

A negative result is acceptable and should be recorded precisely.

## BCAL-005 — PowerSwap / contour abstraction audit

Only if BCAL-000 through BCAL-004 reveal genuine reuse, audit whether the common pattern belongs in a generic module rather than ABC:

```text
two nonnegative/real components U,V
mass    M = U + V
balance Q = U - V
reconstruction U=(M+Q)/2, V=(M-Q)/2
zero contour Q=0
```

Do not force an abstraction merely for aesthetic symmetry. A generic layer is justified only if it has at least two real consumers, e.g. `PowerSwap` and `ABC`.

## BCAL-006 — Quantitative calibration frontier

Only after the structural checkpoints are stable should the project return to numerical estimates.

At that point reinterpret previous numbers as measurements of the calibrated balance region:

```text
old radical/support slopes
shell-count exponents
square-full counting exponents
moment exponents
```

The first quantitative question is not "what is the best exponent?" but:

```text
Which supporting line / contour / residual component is that exponent measuring?
```

Only then decide whether a sharper bound is mathematically meaningful.

## Global stop rule

If a checkpoint merely renames a statement equivalent to `ABCGNOddPrimeJointContract` without revealing an exact internal component, stop and report it as structural normalization.

The branch succeeds if it makes the calibration mechanism more explicit even if no new ABC-strength bound is proved.
