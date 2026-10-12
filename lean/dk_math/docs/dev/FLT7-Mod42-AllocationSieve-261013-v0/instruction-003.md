# Codex instruction-003 — independent allocation prefilter and discrimination audit

Research branch: `research/FLT7-Mod42-AllocationSieve-261013-v0`
Prerequisites: gate 001 + gate 002 reviewed and accepted.
Implementer: GPT-6.1 Sol (light).
**Scope: one small mathematical experiment. Stop after reporting.**

## Purpose

We have a valid necessary condition

`r ∣ M ∧ (NestedGNAllocationCondition M r ∨ NestedRHSAllocationCondition M r) → Nat.ModEq 42 (M / r) 1`.

The next task is **not** to add mod 42 to a predicate which already contains the exact receiver and merely prove a tautological equivalence. Instead construct a **pre-endpoint arithmetic candidate filter**, which does **not** reference either `NestedGNAllocationCondition` or `NestedRHSAllocationCondition` in its definition. Show that an actual reconstruction must pass this filter. Investigate whether it rejects examples which pass the older cheap allocation guards.

## A. Source audit first

Read the actual declarations and hypotheses before editing:

- `DkMath.FLT.Seven.SevenRamifiedFusionModFortyTwoAllocationSieve`
- `DkMath.FLT.Seven.SevenRamifiedFusionSixthPowerAllocationSieve`
- `DkMath.FLT.Seven.SevenRamifiedFusionAllocationThreshold`
- `DkMath.FLT.Seven.SevenRamifiedFusionAllocationResidueSieve`
- `DkMath.FLT.Seven.SevenRamifiedFusionDepthFourReconstructionAudit`

Check the current source index and Mathlib for an equivalent prefilter. Reuse existing results rather than recreating them.

## B. Suggested small theorem contract

Choose clear names consistent with the repository. The following is a proposed shape, not a demand to duplicate definitions:

```lean
def ModFortyTwoCheapAllocation (M r : ℕ) : Prop :=
  r ∈ M.divisors ∧
    Nat.Coprime r (M / r) ∧
    7 ^ 3 * r ^ 7 < M ∧
    Nat.ModEq 42 (M / r) 1 ∧
    ((7 ^ 161 * r ^ 343 < M ^ 49) ∨
     (M ^ 49 < 7 ^ 161 * r ^ 343 ∧
      7 ^ 161 * r ^ 343 ≤ 64 * M ^ 49))

def HasModFortyTwoCheapAllocation (M : ℕ) : Prop :=
  ∃ r : ℕ, ModFortyTwoCheapAllocation M r
```

This definition contains **no exact endpoint variable `u` or residual polynomial equality**, and no gratuitous existence assumptions. The six-power sieve may be investigated as a **separate** prefilter, but do not entangle it with a supposedly cheaply decidable numerical filter unless justified.

Target theorem:

```lean
theorem sixthPowerSieved_implies_mod42Cheap (M : ℕ)
    (h : SixthPowerSievedNestedCondition M) :
    HasModFortyTwoCheapAllocation M
```

Use only the already-proved exact-to-congruence transport and the necessary threshold inequalities. A second consumer from the existing `InternalDepthFourCounterexampleReconstructionObligation` is useful **if** it is a thin use of an existing `..._iff_sixth_power_sieved` theorem, without introducing new assumptions; do not force it if the connection is more complicated.

## C. Is the sieve genuinely discriminating before endpoint equations?

Test a clean finite example:

- `r = 1`, `M = 554`, hence `s = M/r = 554`;
- `s ≡ 1 (mod 7)` but `s ≢ 1 (mod 42)`;
- `7^3 < 554`;
- `554^49 < 7^161 ≤ 64 * 554^49` (the RHS branch's cheap size band);
- `SixthPowerAllocationSieve 1 554` is trivial, since its modulus is 1.

If these facts check in Lean, write a **minimal** test showing that the old cheap constraints can permit this arithmetic candidate while the new mod-42 filter excludes it. Be rigorous: this does **not** show `SixthPowerSievedNestedCondition 554` is true, because that predicate also contains an exact receiver. The purpose is to exhibit strict screening power relative to **necessary-only guards**.

Optionally test `r=1, M=589` as an example that passes mod 42, while noting that a passing candidate **does not imply** an endpoint witness.

If the demonstration fails, record why. Revise the conceptual conclusion rather than weakening the mathematical standards.

## D. Verification and stop condition

Implement only the minimum production declaration(s) and focused tests needed for the contract above. An appropriate new module can live alongside the existing Seven fusion sieve family; the local implementer decides filenames/imports/proof tactics and build strategy according to the actual environment.

Validate the focused source and tests with Lean. Audit newly exported theorems with `#print axioms`, explicitly distinguishing standard axioms from `sorryAx`. No `sorry`, `admit`, new axioms, disguised hypotheses, unsupported FLT7-closure assertions or broad refactoring.

Write:

- `findings-003.md`: confirmed source facts, candidate comparisons, failed approaches and remaining obligations;
- `report-003.md`: exact APIs, arithmetic meaning, proof / test status, limitations, next research proposal;
- `evidence/003-verification-summary.md` **only if** there is compact, decisive information worth preserving.

`logs/` is disposable and never part of durable evidence. **Codex handles implementation, verification and reporting only. Do not run `git add`, `git commit`, `git push`, create PRs, or merge branches.** Wise Wolf (ChatGPT) reviews the reports and publishes reviewed instruction/review documents to GitHub. The user retains integration decisions.

Do not proceed to gate 004 without review.

## Success standard

**A:** kernel-checked pre-endpoint filter with a correct exact-to-cheap implication, plus a valid example demonstrating independent arithmetic screening relative to the former necessary-only filters.
**B:** a narrower correct result or a rigorous diagnosis that the proposed comparison is redundant.
**C:** a failed route recorded with precise missing assumptions / counterexample.

The gate is successful research only if it honestly distinguishes **necessary arithmetic screening** from proving the **absence of reconstruction witnesses**.
