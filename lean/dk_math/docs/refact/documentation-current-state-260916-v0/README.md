# Documentation current-state reset — 2026-09-16

Branch:

```text
refact/documentation-current-state-260916-v0
```

## 1. Purpose

The repository documentation had accumulated several generations of FLT architecture at once. In particular, global/current documents still described the old conditional FLT3 `DkMath.FLT.Main` / `FLT_d3_by_padicValNat` / `NoSqOnS0` route as the main public story after an independent unconditional `DkMath.FLT.Three` tower had already been completed.

This refactor resets the current-state documentation around what the repository can support most clearly today:

1. completed unconditional positive-natural FLT3;
2. completed unconditional positive-natural FLT5;
3. the Cosmic Formula boundary proof route for infinitely many primes;
4. reusable theorems promoted into `DkMath.Lib.*`;
5. active research described separately from completed results.

## 2. Source of truth used for this audit

Supplied snapshot:

### create snapshot file

baseline commit hash: `defafa474285bab64c004b5fd98822e44a646116`

project root:

```sh
cd lean/
./snapshot-dk_math.sh
```

```text
__snapshot-dk_math-lean-code-260916-1826.tar.gz
```

Supplied and independently rechecked SHA-256:

```text
1f0b8ee3dd0a9a5f829447eba7656060c1d2e19f085153a19e5040fa63f0dde7
```

The snapshot contains the Lean source and associated Markdown records used to construct the rewritten status documents.

## 3. Current facts promoted to headline status

### FLT3

Canonical current surface:

```text
DkMath.FLT.Three
DkMath.FLT.Three.fermatThree_no_positive_solution
```

The final FLT3 report states that this tower is independent of the legacy conditional `DkMath.FLT.Main` surface and records the endpoint axiom set

```text
{propext, Classical.choice, Quot.sound}
```

with no `sorryAx` or project-specific axiom at the audited endpoint.

### FLT5

Canonical current surface:

```text
DkMath.FLT.Five
DkMath.FLT.Five.flt5Target
DkMath.FLT.Five.fermatFive_no_positive_solution
```

The completed trust audit records the same standard Lean axiom set for the endpoint and absence of `sorryAx` / DkMath-defined axioms in the checked certificate.

### Infinitely many primes

Current sample route:

```text
DkMath.CosmicFormula.euclid_from_cosmic_boundary
InfinitudeOfPrimes
```

### `DkMath.Lib`

Current promoted public development entrance:

```lean
import DkMath.Lib
```

The documentation now treats GN5 as an important origin/test case and `DkMath.Lib.*` as the durable abstraction layer.

## 4. Current FLT generalization statement

The documentation now uses

```text
docs/refact/FLT-Prime-Generalization-260911-v0/summary-026.md
```

as the bounded current record for the odd-prime integration architecture.

It reaches a residual ideal $p$-th power and conditional element-level sector normalization. It explicitly does **not** claim general FLT.

Open frontier retained verbatim in substance:

- class-group $p$-torsion / principalization;
- real-branch nonzero unit-sector elimination;
- `p=3` carrier/API boundary if generic unification is desired.

## 5. Documentation authority after this refactor

```text
root README.md
  public overview / headline completed results

root docs/PROJECT_STATUS.md
  authoritative dated current technical status

lean/dk_math/README.md
  implementation and build navigation

lean/dk_math/INDEX.md
  current navigation map across completed results, DkMath.Lib, active research, and history

DkMath/FLT/README.md
  FLT current surfaces / generalization / legacy map

DkMath/Lib/README.md
  promoted reusable-library map

docs/dev, docs/feature, docs/refact
  dated checkpoint and history records
```

## 6. Historical-document policy

This refactor does not mass-edit old work logs to make them read as though later results already existed.

Old files that call `FLT_d3_by_padicValNat` the main theorem remain valid records of their checkpoint. New current-state documents explicitly classify them as historical/alternate routes.

A later cleanup may add a short standardized historical notice to selected high-traffic legacy documents, but their mathematical record should not be silently rewritten.

## 7. Files intentionally rewritten

```text
README.md
docs/PROJECT_STATUS.md
lean/dk_math/README.md
lean/dk_math/INDEX.md
lean/dk_math/DkMath/FLT/README.md
lean/dk_math/DkMath/Lib/README.md
```

This directory records the rationale and provenance of that rewrite.
