# completion-report — Legendre gnomon firewall campaign

## Status

**COMPLETE — exact adjacent-shell support turnover recovered.**

Branch:

```text
wip/number-theory-legendre-gnomon-firewall-260915-v0
```

This campaign consumes the merged GNIP successor firewall and upgrades it to exact prime-support intersection identities across adjacent square shells.

## Completed result

The canonical threshold-skipping reindex now has exact support turnover laws.

Lower region:

```text
old support ∩ successor support
=
old support filtered by divisors of oddGnomon n.
```

Upper region:

```text
old support ∩ successor support
=
old support filtered by divisors of 2*(n+1).
```

At a prime threshold `n+1`, the upper persistent old-prime channel collapses to `2`.

Conditional disjointness corollaries and the `30 -> 31` regressions are kernel-checked.

## What was not obtained

No theorem proves Legendre's conjecture, full-cover failure, full-cover propagation, or a global turnover/capacity contradiction.

The current exact local law does not by itself imply a quantitative lower bound on the number of support changes under simultaneous full cover.

Therefore no LGF-001 ledger is opened.

## Legendre frontier after this campaign

The formal endpoint remains

```text
LegendreConjecture
↔
∀ n > 0, ¬ SquareOffsetsFullyCovered n.
```

The new information is orthogonal to the old single-shell capacity stack:

```text
single-shell structure:
  support / gcd / collision / capacity

new adjacent-shell structure:
  exact support turnover under canonical reindex
```

A future Legendre campaign should only resume from the turnover law if a concrete charging principle is found that turns simultaneous full cover into a nontrivial lower bound on forced support changes or fresh incidences.

## Merge recommendation

The branch is suitable for merge after normal CI validation.  The exact turnover theorems are independently useful and do not overclaim a Legendre advance.

## Handoff

After merge, the current Legendre route may be considered paused at a sharper frontier rather than unresolved by implementation work.

The next project-level task may return to ABC as planned.  If Legendre is reopened later, start from `GnomonSupportTurnover.lean` plus the existing collision/capacity frontier; do not rebuild another generic gnomon layer.
