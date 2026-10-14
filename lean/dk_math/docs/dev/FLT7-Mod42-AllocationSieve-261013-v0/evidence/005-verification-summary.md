# Gate 005 diagnostic verification

Provenance: **Codex-reported**, locally executed 2026-10-13; not independently reproduced.
Base revision: `f4f23b99e03b7eaa7cc5099eff2c0fc138b4c864`.
Environment: Lean 4.34.1 / Lake 5.0.0-src+5045d00. Cwd: `lean/dk_math`.

- `lake env lean DkMathTest/FLT/Seven/SevenRamifiedFusionSourceAllocationChartAudit.lean`: exit **0**.
- `lake build DkMathTest.FLT.Seven.SevenRamifiedFusionSourceAllocationChartAudit`: exit **0**.

Decisive build excerpt:

```text
Build completed successfully (9091 jobs).
```

Actual test / axiom output:

```text
file: DkMathTest.FLT.Seven.SevenRamifiedFusionSourceAllocationChartAudit
'DkMathTest.FLT.Seven.abstractLedger_cheap_not_force_perfectSixth' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

The checked model `(M,N,V,C)=(631,1,631,1)` satisfies positive/seven-unit M,N, bare product ledger, coprimality, cheap divisor-one allocation and the modulus-one sixth-power condition, but M/1 is not a literal sixth power. An example negates the corresponding universal implication. Prime-divides-one impossibility is checked separately.

**Scope:** no actual packet, real-pair coordinates, polynomial complementary-root identity or exact chart witness is supplied. This is not a new source-coupled restriction, nor a source-packet counterexample. Inventory statements in the source map were inspected, not all freshly rebuilt here.

Checked diagnostic source SHA-256:

```text
c436539ee82c01054255aaa9924f6d08d895eddcaef9725c1d098952e9baf032  DkMathTest/FLT/Seven/SevenRamifiedFusionSourceAllocationChartAudit.lean
```

Full interpretation: [report-005.md](../report-005.md). Raw logs remain ignored and disposable. No production module or Git mutation.
