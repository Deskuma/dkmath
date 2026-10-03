# FLT3/5/7 Cross-Invariant Ultra — pre-audit workspace

cid: `6ac0a596-64f0-83ee-bca3-723e780ff66d`
cdl: `codex://threads/01a101ab-fa58-7ac3-9bdb-d864215f6ad2`

Branch: **research/FLT357-CrossInvariant-Ultra-261004-v0**

Base provenance:

- forked from `research/FLT7-CompleteSupport-Ultra-261004-v0`
- starting commit: `3c1930be8a911591f364d2adcbc62b4165e1948d`
- therefore includes the checked FLT7 ramified correction:
  `(A)=P7*J^7` and `A=lambda*u*beta^7`.

## Purpose

This is a bounded **cross-exponent pre-audit**, not a new FLT proof campaign.

The question is whether the unconditional FLT3 and FLT5 developments, and the
current incomplete FLT7 development, can be read through one common structural
schema rather than as unrelated exponent-specific proofs.

The FLT7 observation to project backwards is:

```text
raw carrier
  -> exact ramified correction
  -> normalized principal ideal p-th power
  -> unit / phase class
  -> additive coordinate landing
  -> strict descent
```

The primary research goal is to decide whether FLT3 and FLT5 already realize
the same layers in compressed / degenerate form.

## Working hypothesis

For a prime exponent `p`, a useful common normal form may look schematically like

```text
A_p = lambda_p^r * u_p * beta_p^p
```

where `lambda_p = 1-zeta_p`, and the remaining obstruction is carried by some
combination of

- ramified exponent / correction,
- normalized ideal p-th-power class,
- unit class modulo p-th powers,
- cyclotomic phase / Galois compatibility,
- integral/additive landing,
- strict descent measure.

This is a **hypothesis to test**, not a theorem to force.

A second possibility is that no single literal formula is universal, but one
common invariant has values in finitely many residue/sector states.  In that
case the visible exponent-by-exponent proof branches may be a moire-like
sampling pattern of one underlying discrete invariant.

## Scope

Primary source families:

- `DkMath.FLT.Three.*` — unconditional FLT3 route.
- `DkMath.FLT.Five.*` — unconditional FLT5 route.
- `DkMath.FLT.Seven.*` — current FLT7 route, especially the new ramified
  correction / normalized carrier modules.
- `DkMath.FLT.Prime.*` and
  `docs/refact/FLT-Prime-Generalization-260911-v0/*` — existing generic
  odd-prime architecture and its known p-dependent sectors.
- relevant promoted neutral APIs under `DkMath.Lib.*`.

Secondary forecasting targets:

- p=11 and p=13 only to identify what the candidate schema would require.
- No unconditional FLT11/13 implementation is requested.

## Budget discipline

This workspace is intentionally cheap.

Do not start a large implementation, refactor, or full-build campaign merely to
make the comparison look uniform.  Prefer source audit, exact theorem mapping,
small kernel-checkable probes, and durable notes.

The current five-hour usage window may end before a final answer.  Therefore
`findings-001.md` is the primary deliverable and must be updated continuously.

A partial but precise cross-exponent map is a successful result.

## Completed pre-audit artifacts

- [Report 001](report-001.md): limited Outcome B, production matrix,
  reverse projections, normalization and p=11/13 forecast.
- [Findings 001](findings-001.md): continuous checkpoint history.
- Detailed source maps: [FLT3](flt3-audit-001.md), [FLT5](flt5-audit-001.md),
  [FLT7](flt7-audit-001.md), [generic architecture](generic-state-audit-001.md).
- [Focused validation](logs/validation-summary.md): exact commands, axiom
  output and compiled dependency counts, with saved logs.
