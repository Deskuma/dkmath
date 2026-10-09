# Instruction 008 — focused GTail seven-adic conservation calibration

Date: 2026-10-09
Branch: `feature/GTail-SelectiveGap-FLT7-261009-v0` (until owner directs branch/merge change)
Working directory: `lean/dk_math`
Prerequisites: `review-007.md`, `report-006.md`, `constraint-ledger-006.md`.
**Scope:** one narrowly checkable valuation experiment, NOT FLT7 closure, Norm/UnitGauge, general q-order, or Legendre performance work.

## Phase 0 — close the reporting gap without a costly blind rerun

1. Read `report-007.md`. The owner separately reports the full build passes. Ask the owner for a reproducible exact command/log only if not available in existing local history; if sufficient evidence exists, append a brief `validation-addendum-007.md` with command, exit status, git commit, coverage (production entry vs test driver vs all 683 test submodules), and date. Do **not** mark all-test gate complete without command-specific evidence. Do not initiate a fresh 20+ minute all-test run merely to generate this addendum.
2. Keep `LegendreMergedCRT.lean` unchanged. Its `maxHeartbeats 20000000` declarations bound a finite `decide +kernel` elaboration workload; they are not themselves measurements. If any profiling observation is worth recording, describe it separately and do not mix performance changes into this arithmetic instruction.
3. Confirm branch, worktree and actual published `DkMath.Lib` / `DkMath.FLT.Seven` entries. Do not merge or open a PR.

## Phase 1 — exact source inventory for valuation

Read actual theorem signatures and overlap with:
- `DkMath/FLT/Seven/GTailBridge.lean`;
- `DkMath/FLT/Seven/GTailConstraintAudit.lean`;
- `DkMath/Lib/Cosmic/GTailSevenArithmetic.lean`, particularly `gtail_seven_exact_seven_layer`;
- `DkMath/Lib/Cosmic/GTailPadic.lean`, `GTailCongruence.lean`;
- `DkMath/Lib/NumberTheory/PadicValNat.lean` (including its multiplicativity and power support);
- Mathlib `padicValNat.mul` and `padicValNat.pow` with their exact nonzero and typeclass premises;
- `report-006.md` and `constraint-ledger-006.md` for deferred, NOT-yet-proved propositions.

Write `source-inventory-008.md`. Avoid importing existing FLT7 descent/closure owners or creating a circular proof route.

## Phase 2 — satisfiable, neutral exact layer and product-valuation check

Use the **already proved** statement:

```text
7 ∣ g, ¬7 ∣ c
  -> 7 ∣ GTail 7 1 g c ∧ ¬49 ∣ GTail 7 1 g c
```

For `g ≠ 0` under these hypotheses, prove as a neutral natural-number theorem:

```text
padicValNat 7 (GTail 7 1 g c) = 1

padicValNat 7 (g * GTail 7 1 g c)
  = padicValNat 7 g + 1
```

Choose the narrowest appropriate owner: a reusable `DkMath.Lib.Cosmic.GTailSevenValuation.lean` **only if** the needed statements are neutral. Reuse existing valuation lemmas rather than re-proving the general prime-power definitions. Document how `¬49∣T` also implies `T≠0`; zero has all powers as divisors.

**Nonvacuous regressions are mandatory:** `(g,c)=(7,2)` and `(14,2)` satisfy these neutral hypotheses. Include a counterexample when `7∤c` is dropped (e.g. `g=c=7`) to verify that exact valuation 1 is not unconditional.

## Phase 3 — conditional exact FLT7 focused-gap valuation balance

Only after Phase 2 passes, use:
- `gtail_seven_eq_of_fermat7Equation`;
- `exists_positive_focused_gap` or explicit `0<g`;
- `gtail_seven_exact_seven_layer` / the new neutral `v7(T)=1`;
- proper nonzero factors and `padicValNat.mul` / `pow`.

Target the explicit theorem, with honest hypotheses `0<a`, `0<b`, `hEq : Fermat7Equation a b c`, `hsum : a+b=c+g` and **`hend : ¬7∣c`**:

```text
let Q = a^2+a*b+b^2
padicValNat 7 g
  = padicValNat 7 a
    + padicValNat 7 b
    + padicValNat 7 (a+b)
    + 2*padicValNat 7 Q
```

Key proof: first derive `7∣g` from `seven_dvd_focused_gap`; use positivity of g (from the focused-height bounds and hsum), positivity of a,b,a+b,Q,T; apply valuation multiplicativity to the Step 005 product equation, substitute `v7(T)=1` and `v7(7)=1`, then cancel exactly one natural valuation layer with no unjustified subtraction.

Keep the conditional theorem in a small FLT owner, suggested `DkMath/FLT/Seven/GTailValuationAudit.lean`, importing only `GTailConstraintAudit` and the narrow neutral valuation module. The source must not reference unconditional FLT7 impossibility endpoints or use `exfalso`/`False.elim` to derive candidate consequences.

This conditional identity alone may be an algebraic necessary condition and **not** an independent obstruction. Mark classification against the existing FLT7/GTail p-adic canon.

## Phase 4 — additional unit branch, only if feasible and correct

Optionally, under `Nat.Coprime a b` and `7∤a*b*c`, examine the stronger local consequence `49 ∣ g`, using the conservation equality and explicit 7-divisibility information. **First verify the statement algebraically and compare existing mod-49 necessary-condition theorems.** Do not silently assert `7∤a+b` (it may fail), and do not infer `v7(a+b)=0` from `7∤a*b*c` alone.

Important arithmetic caution:
`7∤a*b*c` and the Fermat congruence imply `7∤a+b`? The Fermat linear mod-7 relation gives `a+b ≡ c (mod 7)`, so combined with `7∤c` it does indeed follow, but this implication must be proved using the actual equation rather than guessed from unit coordinates. Any full unit-branch proof must make that argument explicit. Then the conditional formula reduces to `v7(g)=2*v7(Q)`. The unit branch is optional and must not expand into a 49-power unit class or new descent provider.

Do NOT pursue the proposed q² distribution or the order-21 statement in this instruction.

## Phase 5 — focused tests, reports and boundaries

Create if needed:
- `DkMath/Lib/Cosmic/GTailSevenValuation.lean` (neutral, recommended)
- `DkMath/FLT/Seven/GTailValuationAudit.lean` (conditional)
- `DkMathTest/FLT/Seven/GTailValuationAudit.lean` and a separate neutral test if that fits the current convention.
- `source-inventory-008.md`
- `report-008.md`
- project `ROADMAP.md` update indicating a post-integration valuation experiment, without rewriting Step 007's historical validation results.

Build only actual new focused targets sequentially, e.g.:

```text
lake build DkMath.Lib.Cosmic.GTailSevenValuation
lake build DkMath.FLT.Seven.GTailValuationAudit
lake build DkMathTest.FLT.Seven.GTailValuationAudit
```

Re-run relevant prior small test targets and `#print axioms` for all newly public endpoints; maintain no `sorry` / `admit` / extra `axiom` / `unsafe` or FLT theorem import into the neutral module. Avoid full DkMathTest and avoid extra heavy FLT façade builds merely to evaluate this single conjecture.

Document exact theorem signatures, hypotheses, actual build commands and exit codes, axiom lists, overlap with existing valuation/FLT7 results, and at least two satisfiable neutral examples plus a missing-premise counterexample. Label proof status honestly:

- **Outcome B:** neutral valuation calibration and a correct conditional equality, but no genuinely new contradiction/descent.
- **Outcome A:** a genuinely additional noncircular FLT7 necessary restriction, with an explicit proof and comparison to prior named theorems (still not FLT7 closure).
- **Outcome C:** proposed valuation inference false, ill-typed, unavailable under its premises, or blocked by an identified missing lemma; record smallest counterexample or correction.

**STOP after this valuation calibration**. Do not start unrelated Legendre optimization, q-order 21, cyclotomic Norm/unit class, next-packet construction, heavy all-workspace build, PR or merge without new owner direction.
