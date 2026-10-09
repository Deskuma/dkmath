# Review 001 — Selective GTail balance kernel

Date: 2026-10-09  
Branch: `feature/GTail-SelectiveGap-FLT7-261009-v0`  
Review result: **APPROVED / Outcome B (neutral algebraic instrument)**

## Review basis and limitations

Reviewed the pushed GitHub branch, not an uncommitted local worktree:

- `DkMath/Lib/Cosmic/GTailSelection.lean` (129 lines)
- `DkMathTest/CosmicFormula/GTailSelection.lean` (96 lines)
- `source-inventory-001.md`, `report-001.md`, `ROADMAP.md`
- Canonical `DkMath/Lib/Cosmic/GTail.lean` and `GTailPascal.lean` from `develop`.

This is **static source/statement/proof review** plus examination of Codex's recorded local build and axiom results, **not an independent Lean execution**. No unobserved build success is claimed.

## Findings

1. The definitions `selectedTerm`, `selectedBody` and `selectedGap` are internally consistent with the canonical term index `x^k * u^(d-k)`. Finite range filtering gives correct handling of out-of-range indices.
2. `selectedGap_add_selectedBody` uses the valid finite partition of the binomial sum over a general `CommSemiring`; no subtraction or cancellation assumptions are smuggled in.
3. Empty/full/complement/within-range singleton APIs have appropriate typing and cover critical degenerate cases.
4. The `Finset.Ico r (d+1)` adapters align correctly with the existing `GTail d r x u` definition. The direct sum reindexing avoids incorrectly cancelling a prefix in a non-cancellative commutative semiring.
5. The tests correctly exercise degree 3, degree 7, `d = 0`, `r = 0/d` and zero coordinates, and audit ten public theorems.
6. Codex's `report-001.md` records successful focused builds `lake build DkMath.Lib.Cosmic.GTailSelection` and `lake build DkMathTest.CosmicFormula.GTailSelection`, with only the three standard Lean foundation axioms shown for all public theorems. Full-workspace build was neither requested nor performed.
7. Scope boundary is respected: no `DkMath.FLT.*` production import and no unsupported claim of FLT7 closure.

## Non-blocking follow-ups for Instruction 002

- Extrema must be computed from the **active selected set** `(Finset.range (d+1)).filter (· ∈ S)`, not raw `S`, because the input may contain out-of-range indices.
- Distinguish a provable monomial factor from an **exact maximal** multiplicity: equality of exponents needs nonzero/coefficient assumptions and a polynomial context, not just arbitrary semiring evaluation.
- Coefficient content `gcd {choose d k | k active}` is not the gcd of evaluated terms for arbitrary `x,u`. Prove only legitimately supported divisibility assertions.
- Keep index conventions visible. In Step 002, selected term number `k` is the **power of x**. For an active set bounded by `i ≤ k ≤ j`, the forced factor is `x^i * u^(d-j)`.
- All/extreme boundary and empty selections need explicit tests; do not use integer subtraction from a semiring without a ring hypothesis.

## Acceptance

**No blocking issues found.** Authorize Instruction 002, focusing on coefficient/monomial factorization and prime-interior support. Defer transport, norm-square degree-seven factorization, and FLT7 hypothesis-level statements to the roadmap's later stages.
