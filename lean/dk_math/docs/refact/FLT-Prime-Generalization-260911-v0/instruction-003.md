# FLT prime-generalization Phase 3 — collapse the FLT7 adic front half onto the generic prime kernel

## Goal

Make the existing FLT7 ramified arithmetic front half a thin `p = 7` specialization of the production generic odd-prime kernel introduced in Phase 1, while preserving the public FLT7 API used downstream.

The target architectural boundary is:

```text
CounterexampleRouting / SevenAdicPowerSplit
        ↓  generic arithmetic specialization at p = 7
DkMath.FLT.Prime.AdicPowerSplit
        ↓
SevenQuadraticResidualPacket
        ↓  first explicit seven-specific algebraic layer
TraceOneInt (-2), sevenAxis, cyclotomicSevenToTraceOne, ...
```

This phase is a refactor/generalization boundary audit. It does not attempt to generalize the discriminant `-7` quadratic layer, real cubic layer, degree-six cyclotomic layer, or prove FLT7/general FLT.

## Non-goals

- Do not change theorem statements in downstream FLT7 modules unless strictly needed for import cleanup.
- Do not replace `SevenAdicPowerSplit` with an `abbrev` if that breaks field names or downstream elaboration.
- Do not generalize `SevenQuadraticResidualPacket` in this phase.
- Do not touch the separated heavy theta-jet existence branch except for regression builds if needed.
- Do not add `sorry`, `axiom`, or unchecked assumptions.

## Part A — production Seven-to-Prime bridge

Add a production bridge in the smallest suitable FLT7 module, preferably `DkMath.FLT.Seven.SevenAdicPowerSplit` unless a lower dependency location is clearly better.

Construct:

```lean
PrimeAdicFactorPacket 7 (z - y) y x
```

from an existing:

```lean
SevenAdicCounterexamplePacket x y z
```

using only already-proved packet fields / generic production lemmas.

Suggested theorem shape:

```lean
theorem SevenAdicCounterexamplePacket.toPrimeAdicFactorPacket
    {x y z : ℕ} (s : SevenAdicCounterexamplePacket x y z) :
    DkMath.FLT.Prime.PrimeAdicFactorPacket 7 (z - y) y x := by
  ...
```

Audit which fields of `SevenAdicCounterexamplePacket` are actually needed. Do not enlarge the generic packet.

Classify the bridge as:

- `PGEN-SPECIALIZATION` if it is a direct `p=7` instance;
- `P7-EXTRA` only for any genuinely Seven-only input still required.

The expectation is `PGEN-SPECIALIZATION`.

## Part B — rebuild `SevenAdicPowerSplit` from generic output

Keep the existing public structure if this is the lowest-risk compatibility surface:

```lean
structure SevenAdicPowerSplit (x y z : ℕ) : Type where
  sevenAdic : SevenAdicCounterexamplePacket x y z
  a : ℕ
  b : ℕ
  a_pos : 0 < a
  b_pos : 0 < b
  coprime_a_b : Nat.Coprime a b
  gap_eq : z - y = 7 ^ 6 * a ^ 7
  residual_eq : GTail 7 1 (z - y) y = 7 * b ^ 7
  distinguished_eq : x = 7 * a * b
```

Preserve legacy `GN 7 ...` presentation if downstream source compatibility requires it; otherwise use the canonical `GTail` theorem internally and let definitional/simp compatibility handle the old spelling.

Rewrite:

```lean
nonempty_sevenAdicPowerSplit_of_packet
```

so that its mathematical source is:

```lean
DkMath.FLT.Prime.nonempty_primeAdicPowerSplit_of_packet
  s.toPrimeAdicFactorPacket
```

and the returned generic witnesses are repackaged into the existing Seven structure.

The old hand-built chain involving:

- stripped `c`, `r`, `d`;
- `sevenAdicPacket_coprime_scaledGap_residual`;
- `sevenAdicPacket_normalized_product`;
- `seventh_power_factor_split`;
- manual extraction of the `7^6` carrier factor;

should no longer be needed to construct the public Seven split.

Do not delete legacy theorem names if downstream clients use them. Prefer replacing their proofs with generic production theorems or retaining them as thin compatibility wrappers.

## Part C — collapse legacy helpers onto promoted generic API

Audit the following existing Seven helpers and rewrite their proofs as direct specializations wherever possible:

```text
sevenAdicPacket_residual_not_fortyNine_dvd
sevenAdicPacket_seven_not_dvd_strippedResidual
sevenAdicPacket_coprime_div_seven
sevenAdicPacket_coprime_scaledGap_residual
sevenAdicPacket_normalized_product
seventh_power_factor_split
SevenAdicPowerSplit.seven_not_dvd_b
```

Expected sources include:

```text
DkMath.CosmicFormula.not_prime_sq_dvd_GN_of_dvd_gap
DkMath.CosmicFormula.gcd_GN_prime_eq_prime_of_dvd
DkMath.Lib.NumberTheory.power_factor_split
DkMath.FLT.Prime.PrimeAdicPowerSplit
```

For every helper, record one of:

- `PGEN-SPECIALIZATION` — proof collapses to generic theorem;
- `PGEN-COMPAT` — retained only for old API shape / Nat division interface;
- `P7-STRUCTURAL` — genuinely still needs Seven-specific data;
- `PGEN-REDUNDANT` — no production consumer remains after migration.

Do not remove a `PGEN-REDUNDANT` declaration in this phase unless repository search proves there are no production/test/doc consumers that require source compatibility. Marking it is enough.

## Part D — simplify `CounterexampleRouting` only where justified

`CounterexampleRouting.lean` predates the promoted GTail core and contains hand-built degree-seven arithmetic such as:

```text
gcd_gap_GN_seven_dvd_seven
gcd_gap_GN_seven_eq_one_of_not_seven_dvd
gcd_gap_GN_seven_eq_seven_of_seven_dvd
seventh_power_factor_split
padicValNat_carrier_shape_of_mul_eq_seventh
seven_pow_six_dvd_gap_of_counterexample
```

Audit each against the new generic API.

Do not redesign `CounterexampleRoute` in this phase. Preserve the existing route packet and theorem names, but replace duplicated proofs with generic specializations when this reduces code and imports without changing semantics.

Particularly verify that:

```lean
Nat.gcd g (GTail 7 1 g u) = Nat.gcd g 7
```

and the exact residual-depth theorem now account for the old hand-expanded Pascal-row proofs.

## Part E — establish the first Seven-specific frontier

After Parts A–D compile, inspect the immediate downstream module:

```text
DkMath.FLT.Seven.QuadraticResidualPacket
```

Record whether its first nontrivial construction already requires:

```text
TraceOneInt (-2)
sevenAxis
cyclotomicSevenToTraceOne
exists_cyclotomicSeven_terminal_core
```

If yes, classify:

```text
SevenAdicPowerSplit              = PGEN-SPECIALIZATION FRONTIER OUTPUT
SevenQuadraticResidualPacket     = P7-FIRST-ALGEBRAIC-FRONTIER
```

Do not attempt to generalize that quadratic packet yet. The purpose is to identify and certify the exact boundary.

## Part F — compatibility and regression

Required builds:

```bash
lake build DkMath.FLT.Prime.AdicPowerSplit
lake build DkMath.FLT.Seven.CounterexampleRouting
lake build DkMath.FLT.Seven.SevenAdicPowerSplit
lake build DkMath.FLT.Seven.QuadraticResidualPacket
lake build DkMathTest.FLT.Prime.AdicPowerSplitCompatibility
lake build DkMath.FLT.Seven
```

The ordinary `DkMath.FLT.Seven` build should continue to exclude the dormant heavy theta-jet existence chain established in Phase 2.

Also run the relevant existing Seven adic split test if present:

```bash
lake build DkMathTest.FLT.SevenAdicPowerSplit
```

and `git diff --check`.

## Part G — axiom audit

Print axioms for at least:

```text
SevenAdicCounterexamplePacket.toPrimeAdicFactorPacket
nonempty_sevenAdicPowerSplit_of_packet
sevenAdicPowerSplit_of_packet
sevenAdicPowerSplit_of_counterexample
SevenQuadraticResidualPacket.norm_is_seventh_power
```

No `sorryAx`, no new `axiom`.

## Report

Write:

```text
docs/refact/FLT-Prime-Generalization-260911-v0/report-003.md
```

Include:

1. exact declarations migrated to generic specializations;
2. old duplicated proof volume removed or bypassed;
3. compatibility declarations intentionally retained;
4. build and axiom results;
5. whether `QuadraticResidualPacket` is confirmed as the first explicit Seven-specific algebraic frontier;
6. any remaining Seven-specific arithmetic before that frontier.

## Decision criterion

Phase 3 is `Outcome A` if the existing FLT7 ramified power split is rebuilt from `PrimeAdicPowerSplit p=7` without weakening its public output and all downstream focused builds remain green.

A successful Outcome A establishes the architectural theorem-level boundary:

```text
odd-prime GTail / adic normal form      -- generic
-----------------------------------------------
TraceOne(-2) / discriminant -7 residual -- Seven-specific
```

That boundary becomes the starting point for Phase 4 generalization research.