# FLT3 / FLT5 essence documentation closure report

- Date: 2026-07-22
- Checkpoint: F35-009
- Outcome: **B**
- Final feature status: **completed**

## Result

The feature README has been converted from an implementation roadmap into the
completed technical record. Outcome B is used because multiple roadmap-era
statements were stale after F35-006 through F35-008A; they were corrected
without finding any implementation or audit contradiction.

## Status transition

```text
before: Status: implementation roadmap
after:  Status: completed
completion checkpoint: F35-009
```

The opening now summarizes the neutral `TraceOneInt s` API, the `s = -1` and
`s = 1` bridges, their observational role, the fixed full FLT5 standalone,
the v4.29 statement/trust audit, the external v4.33 / Lean4Web milestone, and
the separately deferred Comparator-minimal packaging task.

## Outdated statements corrected

The README no longer says or implies that:

- the full FLT5 standalone is unfinished;
- F35-006, F35-007, F35-008A, or F35-009 is future work;
- the completed certificate is the small `DkMath.FLT.Five.Standalone` seed;
- public/standalone statement comparison or axiom audit is pending.

The seed/generated-artifact distinction remains explicit.

## Completed technical documentation

The final README records:

- the four-module completed module map and dependency direction;
- the exact neutral, FLT3 bridge, and FLT5 bridge theorem surfaces;
- `GN3 / S0 -> N_{-1}` and `GN5 -> N_1` as Lean-proved bridges;
- unchanged public FLT3 and FLT5 endpoints;
- the unconditional Mathlib FLT3 control route versus the conditional
  DkMath-native valuation route with `Nat.Coprime` and `hS0_not_sq`;
- the fixed FLT5 artifact identity, size, SHA-256, 33-source manifest, v4.29
  runtime boundary, build, checksum, provenance, and audit evidence;
- F35-008A Outcome A / PASS, exact endpoint axiom set, and absent unsafe tokens;
- the external v4.33 build and Lean4Web PASS separately from the v4.29
  provenance certificate;
- the Comparator Live initialization observation and deferred minimal bundle;
- the completed checkpoint table and exact non-goals.

## Trust boundary documented

The endpoints are not called axiom-free. Their exact checked set is:

```text
{propext, Classical.choice, Quot.sound}
```

The README records absence of `sorryAx`, DkMath-defined axioms, and active
`native_decide`, `admit`, and `sorry`. For the quadratic essence, it makes only
the checked claim that `sorryAx` and DkMath-defined axioms are absent and links
the per-theorem details.

## Files changed

```text
docs/feature/FLT35-essence-260722/README.md
docs/feature/FLT35-essence-260722/report-flt35-009.md
```

No Lean source, test, generated artifact, checksum, provenance, build log, or
audit log was modified.

## Verification

The closure verification requires and records:

```text
python scripts/audit-flt5-public-standalone.py --check
sha256sum --check DkMath/FLT/docs/StandAlone/FLT5#StandAlone-v0.lean.txt.sha256
lake build DkMath.FLT.QuadraticEssence
lake build DkMath.FLT.Five
git diff --check
```

The final README is also searched for stale roadmap assertions. Historical
phrases occur only where explicitly negated or shown as a before/after status,
not as current claims.

## Final feature status and next feature

FLT35 quadratic essence is complete:

```text
GN3 -> N_{-1}
GN5 -> N_1
```

Recommended next feature: investigate the `GN7 -> N_{-2}` quadratic prediction
as a new, separately scoped design and experiment. This report makes no FLT7 or
general odd-prime theorem claim.
