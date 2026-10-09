# Instruction 004 — Degree-seven GTail calibration and norm-shaped factorization

Date: 2026-10-09  
Target branch: `feature/GTail-SelectiveGap-FLT7-261009-v0`  
Working directory: `lean/dk_math`  
Approved prerequisites: `review-001.md`, `review-002.md`, `review-003.md`  
Scope: **Step 004 only — stop before FLT7 bridge and arithmetic-constraint audit.**

## Mission

Implement `DkMath.Lib.Cosmic.GTailSeven` as a kernel-checked **degree-seven calibration of the generic selection, factor and transport machinery**. Confirm that deliberate removal of the coefficient-one endpoints isolates an exact interior Body with a common `7*x*u` factor and a square of the quadratic form `x²+x*u+u²`.

The mission is not simply to have Lean prove a degree-seven `ring` identity. Verify that existing `GTailSelection` (`Big=Gap+Body`), `GTailFactor` (forced monomial and coefficient factors), and `GTailTransport` (controlled term movement) are **actually used to obtain observational decompositions**. Plain `ring` / `norm_num` are appropriate for the final small finite-degree residual polynomial equality, not as a substitute for all three reusable layers.

No FLT7 hypothesis or terminal contradiction appears in this instruction.

## Phase 0 — current APIs and existing degree-seven code

Before editing:

1. Verify branch and a clean worktree.
2. Read source and test modules for `GTailSelection`, `GTailFactor`, `GTailTransport`, the canonical `GTail`, `GTailPascal` and relevant named degree-seven identities elsewhere in `DkMath`.
3. Search for existing identical ring equalities/number-field Norm definitions. Avoid importing heavyweight FLT owners or duplicating theorem endpoints; use an adapter when possible.
4. Record exact original declarations, rings/carriers, and intended new statements in `source-inventory-004.md`.

Keep `DkMath.CosmicFormula` as the principal namespace and the existing `GTail d r x u` convention: term index k is the exponent of x, **not** the exponent of u.

## Phase 1 — explicit cut kernels (generic CommSemiring)

Create `DkMath/Lib/Cosmic/GTailSeven.lean`, importing `DkMath.Lib.Cosmic.GTailTransport`.

Prove, for any `{R : Type*} [CommSemiring R]`:

```text
GTail 7 6 x u = x + 7*u
GTail 7 5 x u = x^2 + 7*x*u + 21*u^2

selectedBody 7 (Finset.Ico 6 8) x u = x^6*(x+7*u)
selectedBody 7 (Finset.Ico 5 8) x u = x^5*(x^2+7*x*u+21*u^2)
```

Prefer derive selected Body facts using `selectedBody_Ico` + the two evaluated GTail kernels. Reuse `GTail_rec` as appropriate. These cuts expose different factor degree and coefficient boundaries, not a claim of automatic FLT descent.

Additionally explicitly bridge the interior selection:

```text
I := Finset.Ico 1 7   -- active k=1,...,6, both endpoints removed
selectedGap 7 I x u = u^7 + x^7
selectedBody 7 I x u = x*u * selectedResidual 7 I 1 6 x u
coeffGCD 7 I = 7
7*x*u ∣ selectedBody 7 I x u   -- for x,u : ℕ
```

Use **existing** factor/content lemmas for the latter three instead of re-proving them through a direct 7th-power expansion. Avoid redefining the semiring balance or selection.

## Phase 2 — resolve the interior residual square

Define a small readable *neutral* quadratic-form helper only if worthwhile, e.g.:

```text
eisensteinQuadratic(x,u) = x^2 + x*u + u^2
```

The principal equation to prove over **every CommSemiring** is:

```text
selectedResidual 7 (Finset.Ico 1 7) 1 6 x u
  = 7 * (x+u) * (x^2 + x*u + u^2)^2
```

Deduce through the Step 002 factor theorem:

```text
selectedBody 7 (Finset.Ico 1 7) x u
  = 7*x*u*(x+u)*(x^2 + x*u + u^2)^2
```

It is acceptable to evaluate the finite residual via `norm_num`/`simp` and finish with `ring`, while demonstrating that the **Body factorization itself** uses the Step 002 general factor. Keep the actual new theorem statements visibly tied to `selectedBody`/`selectedResidual`.

Proof/check consistency: the interior terms are

```text
7*x*u^6 + 21*x^2*u^5 + 35*x^3*u^4
 + 35*x^4*u^3 + 21*x^5*u^2 + 7*x^6*u.
```

Do not silently replace a selected polynomial identity by an integer divisibility statement. For general semirings the *equality*, not a divisibility relation, is the canonical result.

## Phase 3 — balanced Big reconstruction and transport viewpoints

Use `selectedGap_add_selectedBody` and the established exact Gap/Body factors to prove the **semiring** identity:

```text
(x+u)^7
  = (u^7 + x^7) + 7*x*u*(x+u)*(x^2+x*u+u^2)^2
```

Then give the **separate commutative-ring subtraction corollary**:

```text
(x+u)^7 - x^7 - u^7
  = 7*x*u*(x+u)*(x^2+x*u+u^2)^2
```

Only CommRing supports this subtraction reading; no negative arithmetic is needed in the CommSemiring core.

Use Step 003 transport explicitly at least once in a *public* theorem or meaningful focused test: for example, moving the k=0 endpoint from Gap to Body gives

```text
selectedBody 7 (insert 0 I) x u
  = selectedBody 7 I x u + u^7

selectedGap 7 I x u
  = selectedGap 7 (insert 0 I) x u + u^7
```

The `insert` lemma and its complementary `Gap` version already exist: give a degree-seven observation theorem/test using them, not an independent expanded-polynomial proof. Derive the content change from `coeffGCD_prime_interior` versus `coeffGCD_eq_one_of_zero_mem`, using existing lemmas (the generic pattern is tested in Step 003).

Optional symmetry: moving the k=7 endpoint transfers `x^7`, and after moving both endpoints Body becomes the entire Big. Show both endpoints if it adds value without expanding scope.

## Phase 4 — quadratic norm-shaped calibration (no untyped field claims)

The quadratic form `x^2 + x*u + u^2` is Eisenstein norm-shaped. To exhibit a lightweight arithmetic check, optionally prove the polynomial identity:

```text
(2*x+u)^2 + 3*u^2 = 4*(x^2+x*u+u^2)
```

over a CommSemiring, where multiplication by natural numerals is interpreted in R. This is **not** itself an algebraic number-field norm theorem. Do **not** assert a genuine norm map equality or identify it with an FLT7 cyclotomic/unit class unless all carriers and maps are explicitly built and verified. Such a bridge belongs to Step 006 or later.

## Phase 5 — regressions and audit

Create `DkMathTest/CosmicFormula/GTailSeven.lean`.

Required coverage:

1. The two evaluated GTail cuts at r=5,6, and their selected Body forms.
2. Exact interior selected Gap/Body and coefficient-gcd/`7*x*u` factor, with x=u=1 and asymmetric numeric x,u values.
3. Verify `(1+1)^7 - 1 - 1 = 126`, and compare both exact sides without relying solely on `decide`.
4. Boundary x=0, u=0, and general CommSemiring type-checking.
5. Endpoint insertion: Big conservation and change of coefficient gcd from 7 to 1, using Step 003 transport.
6. Independent `ring` check of the degree-seven identity, plus at least one derivation through selection + factor (not just expansion).
7. `#print axioms` of all new public endpoints. Standard Lean foundations permitted; no `sorryAx`, no extra axioms.

Run focused builds sequentially:

```text
lake build DkMath.Lib.Cosmic.GTailSeven
lake build DkMathTest.CosmicFormula.GTailSeven
lake build DkMath.Lib.Cosmic.GTailTransport DkMathTest.CosmicFormula.GTailTransport
```

Log exact commands, counts, exit codes, axiom lists, changed file paths and limitations. No large clean/full-workspace build merely for Step 004.

## Deliverables and stop boundary

- `DkMath/Lib/Cosmic/GTailSeven.lean`
- `DkMathTest/CosmicFormula/GTailSeven.lean`
- `docs/dev/GTail-SelectiveGap-FLT7-261009-v0/source-inventory-004.md`
- `docs/dev/GTail-SelectiveGap-FLT7-261009-v0/report-004.md`
- Update `ROADMAP.md` with the actual checked state; do not mark future stages completed.

Outcome B is expected: exact degree-seven algebraic instrumentation. If an anticipated factorization or carrier bridge is invalid, report Outcome C with a precise counterexample/repair rather than adding false hypotheses. Outcome A needs a **new, noncircular arithmetic obstruction under actual FLT7 hypotheses**, which is **out of scope here**.

**Stop after Instruction 004. Do not edit `DkMath.FLT.Seven.*`, import a terminal FLT result, invoke cyclotomic unit-power extraction as a proved conclusion, or claim FLT7 closure.** Step 005 will be a separately reviewed bridge from the calibrated degree-seven identity to a hypothetical positive FLT7 counterexample.
