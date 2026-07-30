# FLT5 public / standalone statement and trust audit

- Date: 2026-07-22
- Checkpoint: F35-008A
- Outcome: **A**
- Final audit result: **PASS**

## Pinned verification boundary

This audit ran in the repository-pinned environment:

```text
Lean: 4.29.0
lean-toolchain: leanprover/lean4:v4.29.0
Mathlib input revision: v4.29.0
Mathlib Git revision: 8a178386ffc0f5fef0b77738bb5449d50efeea95
```

The fixed artifact was verified before any other audit work:

```text
DkMath/FLT/docs/StandAlone/FLT5#StandAlone-v0.lean.txt
SHA-256: 400935756c2468577582e6e9b87db2e5a2194a127855e3eb9bea312ff79b8dbd
```

The artifact and its checksum were not modified.

## Declaration statement comparison

The script extracted actual declarations from current production source and
the fixed standalone artifact. It retained definition bodies for
`Fermat5Equation` and `FLT5Target`, retained theorem types but excluded proof
bodies for both endpoints, normalized only ordinary whitespace, and compared
the resulting bytes.

| Declaration | Public SHA-256 | Standalone SHA-256 | Result |
|---|---|---|---|
| `Fermat5Equation` | `e0d06367d60ee6e46611f92a24cb410d9714f6d11d99437025058a220ece8fa4` | `e0d06367d60ee6e46611f92a24cb410d9714f6d11d99437025058a220ece8fa4` | equal |
| `FLT5Target` | `551c0c54250fefc36dc4fc4549fec98907eccdf62ef961b7cff672aedc647909` | `551c0c54250fefc36dc4fc4549fec98907eccdf62ef961b7cff672aedc647909` | equal |
| `flt5Target` | `91bb3d3ad40f573ea51cd1fac2a29e70dd32f49a628e6fe274717768bf8a7c0f` | `91bb3d3ad40f573ea51cd1fac2a29e70dd32f49a628e6fe274717768bf8a7c0f` | equal |
| `fermatFive_no_positive_solution` | `a5b96af9f90ca593007ec34f731eacf69075310005eff59f2d25c64f3217a1b4` | `a5b96af9f90ca593007ec34f731eacf69075310005eff59f2d25c64f3217a1b4` | equal |

Statement comparison result: **PASS**.

## Lean type-output comparison

Public and standalone were checked in separate Lean processes because they
define declarations in the same namespace. After normalizing diagnostic
positions and ordinary output whitespace, all `#check` outputs agreed exactly:

```text
@DkMath.FLT.Five.Fermat5Equation: equal
@DkMath.FLT.Five.flt5Target: equal
@DkMath.FLT.Five.fermatFive_no_positive_solution: equal
```

Both temporary audit files also typechecked an ordinary-argument example using
`fermatFive_no_positive_solution`. Public and standalone Lean exit statuses
were both 0.

Type-output comparison result: **PASS**.

## Endpoint axiom sets

The exact reported axiom set for both public endpoints was:

```text
{propext, Classical.choice, Quot.sound}
```

The fixed standalone reported exactly the same set for each endpoint:

| Endpoint | Public | Standalone | Result |
|---|---|---|---|
| `DkMath.FLT.Five.flt5Target` | `propext`, `Classical.choice`, `Quot.sound` | `propext`, `Classical.choice`, `Quot.sound` | equal |
| `DkMath.FLT.Five.fermatFive_no_positive_solution` | `propext`, `Classical.choice`, `Quot.sound` | `propext`, `Classical.choice`, `Quot.sound` | equal |

No endpoint report contains `sorryAx` or a DkMath-defined axiom. These theorems
are therefore not described as axiom-free: they depend on the three standard
Lean axioms listed above.

Axiom-set comparison result: **PASS**.

## Active-token audit

Comments and string literals were removed before scanning executable source.
Active occurrences of `native_decide`, `admit`, and `sorry`:

```text
DkMath/FLT/Five/Basic.lean: none
DkMath/FLT/Five/Main.lean: none
fixed standalone artifact: none
```

Active-token result: **PASS**.

## Quadratic-essence axiom audit

`lake env lean DkMathTest/FLT/QuadraticEssence.lean` exited with status 0.
The exact reported sets were:

| Declaration | Reported axioms |
|---|---|
| `DkMath.NumberTheory.TraceOneQuadratic.traceOne_norm_mul` | `propext`, `Quot.sound` |
| `DkMath.NumberTheory.TraceOneQuadratic.four_mul_traceOneNorm_eq_discriminant` | `propext`, `Quot.sound` |
| `DkMath.FLT.S0_nat_eq_traceOneNorm_negOne` | `propext`, `Classical.choice`, `Quot.sound` |
| `DkMath.FLT.GN_three_sub_eq_traceOneNorm_negOne` | `propext`, `Classical.choice`, `Quot.sound` |
| `DkMath.FLT.Five.goldenNorm_eq_traceOneNorm_one` | `propext` |
| `DkMath.FLT.Five.GN5_eq_traceOneNorm_squareLink` | `propext`, `Quot.sound` |

No report contains `sorryAx` or a DkMath-defined axiom. This audit concerns the
quadratic essence only and does not make the conditional DkMath-native FLT3
valuation route unconditional.

## Saved evidence

Deterministic standard-library-only audit tool:

```text
scripts/audit-flt5-public-standalone.py
```

Complete saved log:

```text
DkMath/FLT/docs/StandAlone/FLT5#StandAlone-v0.audit-v429.log
```

The log includes normalized declaration hashes, raw public and standalone Lean
output, normalized type comparisons, endpoint axiom sets, active-token results,
quadratic audit output, exit statuses, and `final result: PASS`.
Two complete `--log` runs were compared byte-for-byte with `cmp`; the saved log
is deterministic.

## Files changed

```text
scripts/audit-flt5-public-standalone.py
DkMath/FLT/docs/StandAlone/FLT5#StandAlone-v0.audit-v429.log
docs/feature/FLT35-essence-260722/report-flt35-008a.md
```

## Explicit non-goals

This checkpoint did not run Comparator Live, create a Comparator-minimal
bundle, edit the v4.33 derivative, alter the fixed v4.29 artifact or checksum,
change any proof or theorem statement, add a general-prime theorem or p=7
experiment, mark the feature README completed, or perform F35-009.

The external v4.33 / Lean4Web milestone remains distinct from this local v4.29
trust audit. Comparator Live bundle reduction remains deferred.

## Recommendation

F35-008A is closed with Outcome A. Proceed to F35-009 documentation closure,
while retaining Comparator-minimal bundle work as the separately deferred
standalone compatibility task recorded by the v4.33 milestone note.
