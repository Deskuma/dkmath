# Instruction 001 — Selective GTail balance kernel

Target branch: `feature/GTail-SelectiveGap-FLT7-261009-v0`  
Baseline: `develop`  
Worktree root: `lean/dk_math`  
Project docs: `docs/dev/GTail-SelectiveGap-FLT7-261009-v0/`

## Mission

Implement **only the first neutral layer** for choosing the Gap terms of a binomial Big, and make that layer reusable by the existing canonical GTail family. Do not attempt to prove FLT7 here. The long-term goal is a GN/GTail "reasoned subtraction" instrument: select a Gap to expose precise divisibility/factor structure in the remaining Body, while the balance `Big=Gap+Body` stays exact.

The design target in this first instruction is **`DkMath.Lib.Cosmic.GTailSelection`**. Next instructions will cover factor/content, transport, degree-seven calibration, and the FLT7 research bridge.

## Phase 0 — repo and theorem inventory (before edits)

1. Confirm the worktree is on the requested branch; do not change `develop`.
2. Inspect ```text
DkMath/Lib/Cosmic/GTail.lean
DkMath/Lib/Cosmic/GTailPascal.lean
DkMath/Lib/Cosmic/GTailBoundary.lean
DkMath/Lib/Cosmic/GTailNat.lean
DkMath/Lib.lean
DkMath/Lib/README.md
```
and any relevant Mathlib `Finset.sum_filter` / `add_pow` theorems.
3. Record exact existing signatures. In particular, `GTail d r x u` removes the first `r` terms of `(x+u)^d` **indexed by powers of x**, not by descending powers of x.
4. Reuse existing definitions and kernels. If equivalent selection APIs already exist elsewhere, write an adapter instead of duplicating them.
5. Write `source-inventory-001.md` in the project docs with paths, existing theorems, and planned new signatures.

## Phase 1 — define a genuinely selective Big/Gap/Body

For `R` a commutative semiring, `d : ℕ`, `x u : R`, and a finite set `S : Finset ℕ`, define:

```text
term(d,k,x,u) = (Nat.choose d k : R) * x^k * u^(d-k)
Body(d,S) = sum over k in range(d+1) with k∈S of term
Gap(d,S)  = sum over k in range(d+1) with k∉S of term
```

This automatically ignores out-of-range indices. You may choose better Lean names/types after examining Mathlib; preserve this exact documented semantics. Avoid using infinite set complements. Consider a single `selectedTerm` def plus two `Finset.filter` definitions; avoid constructing `Decidable` proof fields as the mathematical core.

Prove:
- `selectedGap_add_selectedBody`: `(x+u)^d = Gap + Body`.
- `selectedBody_empty`, `selectedGap_empty`, `selectedBody_full`, `selectedGap_full`.
- Complement swap within the bounded range (if the API uses bounded `S`, prove this explicitly).
- Singleton term extraction as a useful upcoming transport lemma (optional if it substantially complicates proof).

Use `CommSemiring` for balancing identities; if providing a subtraction corollary, use `CommRing` separately and explicitly.

## Phase 2 — bridge existing GTail

Show the general selection agrees with the current `GTail` prefix/tail decomposition for `r ≤ d`. For example with S = `Finset.Ico r (d+1)`:

```text
Body(d,S) = x^r * GTail d r x u
Gap(d,S)  = sum over j in range r of choose(d,j)*x^j*u^(d-j)
```

Use the existing `add_pow_eq_prefix_add_xpow_mul_GTail` / `higher_tail_eq_pow_mul_GTail`, and existing `Finset` partition lemmas; **do not reprove or replace the canonical GTail recursion**. If chosen S = range r is more ergonomic, prove the analogous prefix selection first, then connect the complement.

Be meticulous about `r = 0`, `r = d`, `x = 0`, `u = 0` and the `d = 0` boundary; do not strengthen hypotheses without documenting why.

## Phase 3 — small local regression targets

Create a focused test module under `DkMathTest` if useful, following repository conventions. Test:
1. degree-three cut corresponding to `(x+u)^3 = (u^3 + 3*x*u^2) + x^2*(x+3*u)`;
2. degree-seven both-endpoints selection `S={1,2,3,4,5,6}` to ensure the semantic API selects exactly the six interior terms (the full factorization is **Step 004**, not a Phase 3 obligation);
3. all/empty selection in degree zero;
4. Lean type-checking for a general commutative semiring rather than only `ℕ`.

## Phase 4 — proof and audit

- Focused build: `lake build DkMath.Lib.Cosmic.GTailSelection`.
- Build any new focused test module.
- `#print axioms` on exported theorems; record results.
- No `sorry` / `admit` / nonstandard `axiom` / new unsound axioms.
- No imports of `DkMath.FLT.*` into `DkMath.Lib.*`.
- Do not trigger a huge clean/parallel full build merely to confirm this first change.
- Do not edit existing FLT7 theorem owners during instruction 001.
- If a requested theorem has a false or ill-typed statement, **report and repair the specification** with a minimal counterexample or a corrected hypothesis, not a hidden assumption.

## Deliverables

1. `DkMath/Lib/Cosmic/GTailSelection.lean` with definitions, general balance and existing GTail adapter.
2. `DkMathTest/...` focused test if appropriate.
3. `docs/dev/GTail-SelectiveGap-FLT7-261009-v0/source-inventory-001.md`.
4. `docs/dev/GTail-SelectiveGap-FLT7-261009-v0/report-001.md` with theorem names/types, changed files, exact validation commands and outputs, axiom audit, conclusions and open questions.
5. Update `ROADMAP.md` with actual state, leaving downstream milestones unclaimed.

**Stop at instruction 001** once the focused proofs and report are complete; do not proceed to factors, transport or FLT7 closure until the next reviewed instruction.
