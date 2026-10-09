# Instruction 002 — Selective GTail factorization and coefficient-content boundary

Date: 2026-10-09  
Branch: `feature/GTail-SelectiveGap-FLT7-261009-v0`  
Worktree: `lean/dk_math`  
Previous checkpoint: `report-001.md`, **APPROVED / Outcome B**  
Current instruction: **Step 002 only. Stop before Step 003.**

## Mission

Create `DkMath.Lib.Cosmic.GTailFactor`, a reusable neutral layer that extracts **provable common monomial factors** and **Pascal coefficient-content factors** from the selected Body obtained by "reasoned Gap subtraction." Reuse the `GTailSelection` and canonical `GTail` APIs; do not restate a pre-existing theorem as a new proof endpoint.

This is a stronger observation instrument, not a proof of FLT7. Always distinguish:

```text
Big = Gap(S) + Body(S)
Body(S) = x^i * u^(d-j) * Residual(d,S,i,j,x,u)
```

from a claim about an *exact maximal* exponent or a gcd of evaluated integer values.

## Phase 0 — source and API audit (before editing)

Read:

- `DkMath/Lib/Cosmic/GTailSelection.lean` and its test file.
- `DkMath/Lib/Cosmic/GTail.lean` / `GTailPascal.lean` / `GTailBoundary.lean` / `GTailNat.lean`.
- Relevant Mathlib `Finset.gcd`, `Nat.Prime`/`Nat.choose` divisibility results, finite sums and polynomial content lemmas.

Write `source-inventory-002.md` listing exact existing declaration names and types, module placement, and minimal missing interfaces. No duplicate `GTail` recursion, no general FLT imports.

## Phase 1 — factorization determined by the selected index range

Retain Step 001 indexing:

```text
t_k(d,x,u) = (choose d k : R) * x^k * u^(d-k)
A(d,S) = (Finset.range (d+1)).filter (fun k => k ∈ S)
Body(d,S) = Σ_{k∈A} t_k
```

**Required theorem schema** (all in a general `CommSemiring R`):

For natural `i,j,d` with `i ≤ j ≤ d`, and every *active* selected index satisfying `i ≤ k ≤ j`, define a residual:

```text
selectedResidual(d,S,i,j,x,u)
  = Σ_{k∈A(d,S)} (choose d k : R) * x^(k-i) * u^(j-k)
```

Prove without division/cancellation:

```text
Body(d,S,x,u) =
  x^i * u^(d-j) * selectedResidual(d,S,i,j,x,u)
```

A flexible bound theorem is preferable to a theorem needing to compute `min/max`; afterwards supply a corollary when `A` is nonempty with `i=min A` and `j=max A` (only if a clean and robust Finset API is available). The flexible bound theorem must also handle empty A as a zero identity.

Important: all bounds are about `k ∈ A(d,S)` rather than the unbounded raw input `S`. Using `S = {0, d+20}` as though `j=d+20` were active is a specification error.

For `R=ℕ`, additionally derive `x^i * u^(d-j) ∣ selectedBody ...`. Optional `CommRing` subtraction reading `Big - Gap = Body` may be added **only if** it gives a genuinely reusable API and does not distract from the factor.

## Phase 2 — coefficient content and distinct meanings of gcd

Define, or adapt an existing definition of, the **natural gcd of active Pascal coefficients**:

```text
coeffGCD(d,S) = gcd { choose d k : k∈A(d,S) }
```

Use Mathlib's existing finite gcd API where possible; empty-set convention and the presence of `d=0` must be documented.

Prove:

- `coeffGCD(d,S) ∣ choose d k` for every `k∈A(d,S)`;
- `coeffGCD(d,S) ∣ selectedBody d S x u` for `x,u : ℕ`;
- `coeffGCD(d,S)=1` whenever an active endpoint `k=0` or `k=d` is retained (its coefficient is 1);
- coefficient-content evaluation examples in degrees 3 and 7.

Do **not** claim `coeffGCD(d,S)=gcd(Body(d,S,x,u),...)` for arbitrary coordinates. Do **not** assert a *maximal* power of `x` or `u` in the semiring without hypotheses preventing vanishing.

If proving the gcd API turns out to require a disproportionate implementation or changes the intended carrier, record the obstacle and provide a **generic common-coefficient-divisor lemma** as a checkable fallback. Do not declare the content milestone complete without either a correct gcd theorem or a clearly documented Outcome C / deferred subgoal.

## Phase 3 — prime-degree interior, independent of FLT

For prime `p≥2`, take the active interior set `I=Finset.Ico 1 p`: remove both endpoints `k=0` and `k=p` from the degree-p binomial Big.

Target reusable results over natural numbers:

```text
p ∣ coeffGCD(p,I)    (and ideally coeffGCD(p,I) = p)
p * x * u ∣ selectedBody p I x u
```

Explain the proof path: all interior `choose p k` are divisible by `p`, each interior monomial has a factor `x*u`, and `choose p 1 = p` forces coefficient-gcd exactness when the active interior contains 1.

The second result can alternatively be expressed as an exact factorization `selectedBody = (p*x*u) * Q` with an explicitly defined neutral residual. Ensure `p=2` is not accidentally excluded. No general claims about a nonprime exponent.

For degrees 3 and 7, add direct regression:
- `selectedBody 3 (Finset.Ico 1 3) x u = 3*x*u*(x+u)`;
- `selectedBody 7 (Finset.Ico 1 7) x u` is divisible by `7*x*u`, but the explicit Eisenstein norm-square factor is reserved for Step 004.

## Phase 4 — independent regression set

Add `DkMathTest/CosmicFormula/GTailFactor.lean` (or standard project's nearest convention). Tests must cover:

1. Sparse degree-five selection `S={1,3}` with forced factor `x*u^2` and residual `5*u^2 + 10*x^2`. Show the actual exact equality via factor theorem, not merely `ring` directly on an expanded sum.
2. Endpoint-selection cases `{0}`, `{d}` and `{0,d}`; contrast content gcd = 1 with missing-endpoint interior content.
3. Degree-zero and empty selected set. Also a selection containing out-of-range index (e.g. `S={1,100}` at `d=3`).
4. Prime interiors at `p=2,3,7` (including coefficient gcd / divisibility).
5. General `CommSemiring` factor identity, including `x=0` and `u=0`.
6. `#print axioms` for all newly promoted theorem endpoints.

## Phase 5 — validation, reports, stop condition

- Focused build `lake build DkMath.Lib.Cosmic.GTailFactor`.
- Focused test build `lake build DkMathTest.CosmicFormula.GTailFactor`.
- Confirm Step 001 targets still compile if imports/theorems are touched.
- No `sorry`, `admit`, unauthorized `axiom`, `unsafe` or circular FLT claims.
- No imports from `DkMath.FLT.*` into the neutral Cosmic library.
- Keep work small and sequential on memory-constrained environments.
- Record exact theorem signatures, proofs' dependencies, build outputs/exit codes and `#print axioms` in `report-002.md`.
- Update this study's `ROADMAP.md` with actual checked progress and an honest outcome A/B/C. If any specification is false or unavailable under current hypotheses, show a counterexample or smallest corrected statement.
- **Do not** implement Step 003 `GTailTransport`, Step 004 `GTailSeven`, any FLT7 bridge, or façade promotion during this instruction.

## Review acceptance criterion

Instruction 002 is accepted only when the new reusable factor theorem has a kernel-checked proof, coefficient-content assertions are typed and accurately bounded (or honestly scoped with a documented obstacle), focused tests cover end cases, and no statement depends on importing a future FLT7 conclusion.

The priority is **structural correctness and reusability, not code volume**. Expected result is Outcome B; an unexpected new arithmetic fact must be stated separately and checked, not inferred from algebraic balance.
