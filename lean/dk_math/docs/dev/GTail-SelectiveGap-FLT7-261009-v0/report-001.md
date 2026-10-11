# Report 001 — selective GTail balance kernel

Date: 2026-10-09. Branch: `feature/GTail-SelectiveGap-FLT7-261009-v0`.
Outcome **B — algebraic instrument only**. Instruction 001 is complete.

## Changed files

- `DkMath/Lib/Cosmic/GTailSelection.lean`: new neutral definitions and ten theorems.
- `DkMathTest/CosmicFormula/GTailSelection.lean`: semiring regression examples and public theorem axiom audit.
- `docs/dev/GTail-SelectiveGap-FLT7-261009-v0/source-inventory-001.md`: pre-edit inventory and planned signatures.
- This report and the adjacent `ROADMAP.md`.

Paths are relative to `lean/dk_math`. Existing GTail and FLT7 owners are unchanged.
The API is available by direct import; façade/README promotion stays at Step 007.

## Exact public contracts

Namespace: `DkMath.CosmicFormula`. All declarations below have implicit
`{R : Type*} [CommSemiring R]`. Write `T = Finset.range (d+1)`.

Definitions:

```lean
selectedTerm (d k : ℕ) (x u : R) : R := (Nat.choose d k : R)*x^k*u^(d-k)
selectedBody (d : ℕ) (S : Finset ℕ) (x u : R) : R
selectedGap (d : ℕ) (S : Finset ℕ) (x u : R) : R
```

Body sums `selectedTerm` over `T.filter (fun k => k ∈ S)`;
Gap sums it over `T.filter (fun k => k ∉ S)`. Out-of-range members of S
have no effect. No infinite complement, ring subtraction, cancellation,
nonzero hypothesis, or mathematical Decidable fields are introduced.

| Theorem | Explicit arguments | Conclusion |
| --- | --- | --- |
| `selectedGap_add_selectedBody` | `(d : ℕ) (S : Finset ℕ) (x u : R)` | `(x+u)^d = selectedGap d S x u + selectedBody d S x u` |
| `selectedBody_empty` | `(d : ℕ) (x u : R)` | `selectedBody d ∅ x u = 0` |
| `selectedGap_empty` | same | `selectedGap d ∅ x u = (x+u)^d` |
| `selectedBody_full` | same | `selectedBody d T x u = (x+u)^d` |
| `selectedGap_full` | same | `selectedGap d T x u = 0` |
| `selectedBody_complement` | `(d : ℕ) (S : Finset ℕ) (x u : R)` | `selectedBody d (T \ S) x u = selectedGap d S x u` |
| `selectedGap_complement` | same | `selectedGap d (T \ S) x u = selectedBody d S x u` |
| `selectedBody_singleton` | `(d k : ℕ) (x u : R) (hk : k ≤ d)` | `selectedBody d {k} x u = selectedTerm d k x u` |
| `selectedBody_Ico` | `(d r : ℕ) (x u : R) (hr : r ≤ d)` | `selectedBody d (Finset.Ico r (d+1)) x u = x^r*GTail d r x u` |
| `selectedGap_Ico` | same | `selectedGap d (Finset.Ico r (d+1)) x u = ∑ j ∈ Finset.range r, (Nat.choose d j : R)*x^j*u^(d-j)` |

Balance uses Mathlib `add_pow` and `Finset.sum_filter_add_sum_filter_not`.
The interval adapter reindexes the finite sum with `Finset.sum_Ico_add'`
and factors `x^r` using `pow_add` and `Finset.mul_sum`. This direct adapter
is needed because cancelling the common prefix from the existing balance
would require additive cancellation unavailable in a general CommSemiring.
It reuses the canonical GTail definition and never reimplements recursion.
The degree-three balance regression directly uses
`add_pow_eq_prefix_add_xpow_mul_GTail`. The ring subtraction theorem is
not needed for the semiring adapter and no new subtraction corollary is added.

## Validation performed

Working directory: `lean/dk_math`.

```text
lake build DkMath.Lib.Cosmic.GTailSelection
✔ [1046/1046] Built DkMath.Lib.Cosmic.GTailSelection (2.5s)
Build completed successfully (1046 jobs).
exit 0

lake build DkMathTest.CosmicFormula.GTailSelection
ℹ [1047/1047] Built DkMathTest.CosmicFormula.GTailSelection (3.7s)
Build completed successfully (1047 jobs).
exit 0
```

These are focused incremental builds, not a clean or full-project validation.
Initial iterations failed on rewrite shapes, lemma names and simplification;
those elaboration errors were repaired without changing the contracts.
An initial shell write also used a repository-relative path from the nested
Lake directory and failed before creating a source file; the path was corrected.
Final focused builds have no warnings or errors.

Regressions cover degree-three cut and canonical balance; degree-seven
selection `{1,2,3,4,5,6}` explicitly expands to exactly six interior terms
and Gap equals `u^7+x^7`; all/empty degree zero; `r=0`, `r=d`, zero `x`,
zero `u`, and an out-of-range selection `{42}` at degree zero. Every example
is quantified over a general CommSemiring. Degree-seven factorization is deferred.

The test module runs `#print axioms DkMath.CosmicFormula.<name>` for each
of the ten theorem names in the table. Each output is exactly:

```text
'DkMath.CosmicFormula.<name>' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Thus all ten use only these standard Lean foundations, with no `sorryAx`
or extra axiom dependency.

From repository root:

```text
rg -n '\b(sorry|admit|axiom)\b|^import DkMath\.FLT\.' \
  lean/dk_math/DkMath/Lib/Cosmic/GTailSelection.lean \
  lean/dk_math/DkMathTest/CosmicFormula/GTailSelection.lean
(no matches; exit 1)

git diff --check
(no output; exit 0)
```

Both new source files were also read back for review. The production module
imports only `DkMath.Lib.Cosmic.GTail`; no FLT owner dependency is added.

## Conclusions and open questions

The requested statements are well typed and true with the specified hypotheses;
no specification repair or stronger assumption was necessary. Boundary cases
remain supported, including `d=r=0`. Arbitrary finite selection and canonical
prefix/tail selection now share an exact semiring balance API.

Steps 002–007 remain open: factor/content, transport, degree-seven
factorization, FLT7 bridge and arithmetic constraint audit, and façade promotion.
This checkpoint proves no FLT7 contradiction, descent, valuation preservation,
or global arithmetic closure. Work stops at instruction 001.
