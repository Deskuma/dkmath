# GTail Selective-Gap / FLT7 Bridge

Branch: `feature/GTail-SelectiveGap-FLT7-261009-v0`  
Base: `develop` (dedicated implementation branch)  
Status: **Steps 001–041 Outcome B; Step 042 source audit COMPLETE / STOP; Step043 release validation COMPLETE / READY for review; FLT7 still open**  
cid: `6ac80570-9ebc-83ee-ad09-e39c11197056`

## Current closure status (2026-10-12)

The original Step007 milestone and its interrupted full-test gate remain historically true;
subsequent focused tests and research stages extend the result through Step041.
Step042 corrected the stale Row-Z terminal frontier: the signed `TraceOneInt(-2)`
root extraction and common primitive ramified summit are **already implemented** in
the old FLT7 tower. There is still **no unconditional exponent-seven theorem**.

The dedicated `import DkMath.FLT.Seven.GTail` facade and its public API smoke
are locally validated at HEAD `caebaf0ec98c12e1e570b6e2e9aefb2aa2362f7e`.
All five entrance builds, all 49 added test targets and the full default
`LEAN_NUM_THREADS=2 lake test` passed. Cache reuse and existing unrelated
`sorry` warnings are recorded in [report-043.md](report-043.md); no new Lean
source or proof was added during this release step. The dedicated entrance
imports 30 specialized owners without importing the historical FLT7 facade.
Research remains **Outcome B / STOP042**. Integration with develop and PR
publication are separate decisions; after fetch, the branch is ahead136/behind1.

Read [PR-CLOSEOUT.md](PR-CLOSEOUT.md) and [PR-DRAFT.md](PR-DRAFT.md) for the
correct full-scope account rather than this document's old Step007 narrative.

## Research purpose

Build a reusable GN/GTail observation layer inside `DkMath.Lib.Cosmic.*`.

The objective is not to restate the Cosmic Formula with different notation. Regard an existing theorem or power expansion as a complete **Big**, select a mathematically justified **Gap**, and expose the resulting **Body**, its **Core / Beam** decomposition, exact divisibility, valuation, and the invariants preserved while the Gap changes.

```text
Big = Gap + Body
Body = Core + Beam
Core can be a smaller Big' for another structurally justified decomposition
```

A deliberate Gap selection ("reasoned subtraction") is a source of new observable constraints. Equalities alone must not be mistaken for new arithmetic obstructions.

## Existing canonical basis

Implementation is under `lean/dk_math`. Inspect and reuse:

- `DkMath.Lib.Cosmic.GTail`: `GTail`, `add_pow_eq_prefix_add_xpow_mul_GTail`, `higher_tail_eq_pow_mul_GTail`, `GTail_rec`.
- `DkMath.Lib.Cosmic.GTailPascal`: `GTail_split_at`.
- `DkMath.Lib.Cosmic.GTailBoundary`: `gcd_GTail_eq_gcd_choose`.
- `DkMath.Lib.Cosmic.GTailNat`, `GTailCongruence`, `GTailPadic`, `GTailCyclotomic`.
- `DkMath.Lib.lean`: promoted public imports.

**Indexing warning:** the existing `GTail d r x u` removes the **first r layers counted by powers of x** (j=0,...,r-1) and returns an `x^r`-divisible Body. Thus the cubic example

```text
(x+y)^3 - (y^3+3*x*y^2) = x^2*(x+3*y)
```

is `GTail 3 2 x y`. Keep this indexing; do not silently reverse it.

## Mathematical construction

For `t_k = choose(d,k) * x^k * y^(d-k)`, define a selection `S` of indices within `0..d`:

```text
Big       = sum of all t_k = (x+y)^d
Body(S)   = sum of selected t_k
Gap(S)    = sum of unselected t_k
Big       = Gap(S) + Body(S)
```

Prove the balanced decomposition over a commutative semiring first (no subtraction needed). Subtraction-shaped identities belong to a commutative-ring corollary.

Recover the ordinary prefix/suffix GTail from interval selections rather than redefining the existing canonical `GTail`. For nonempty S, the smallest and largest selected indices control mandatory monomial factors; the gcd of the selected Pascal coefficients controls the integer polynomial content. Removing both endpoints for prime degree exposes an additional degree-prime coefficient factor and an `xy` factor. These are separate mechanisms.

When changing selection `S -> T`, track exactly which terms move and prove the equality, not preservation of divisibility without its hypotheses.

## Degree-seven calibration

The following identities are kernel checked without any FLT assumption; the subtraction reading requires a CommRing:

```text
GTail 7 6 x y = x + 7*y
GTail 7 5 x y = x^2 + 7*x*y + 21*y^2
(x+y)^7 - x^7 - y^7
  = 7*x*y*(x+y)*(x^2+x*y+y^2)^2
```

The degree-seven endpoint-removal identity is a polynomial identity; it does **not** imply Fermat's Last Theorem on its own.

## Checked conditional boundary to FLT7

Assume `a^7 + b^7 = c^7` and independently `c + g = a + b` in naturals (or use a typed integer coordinate with explicit positivity). Derive, without importing an existing FLT7 impossibility endpoint:

```text
g * GTail 7 1 g c
  = 7*a*b*(a+b)*(a^2+a*b+b^2)^2
```

Step 005 first proves an independent shell from only `a+b=c+g` in a
CommSemiring. The Fermat corollary rewrites the equation and cancels the same
`c^7`. Step 006 proves the positive focused-gap certificate, recovers the
known condition `7 ∣ g`, and checks neutral Q-coprimality and exact residual
seven-layer facts. These are Outcome B instruments and necessary conditions;
no constructive descent or FLT7 closure follows.

## Public API and tests

`import DkMath.Lib` now explicitly exposes the neutral family:

- `GTailSelection`: selective Body/Gap balance; k is the exponent of x and Gap contains the unselected active terms.
- `GTailFactor`: forced monomial residual, coefficient content and prime interior divisor.
- `GTailTransport`: exact term movement and modular conservation with moved-term divisibility premises.
- `GTailSeven`: degree-seven cuts, polynomial square factor and calibrated endpoint transport.
- `GTailSevenArithmetic`: Q-coprimality from `Nat.Coprime a b`; exact tail layer from `7 ∣ g` and `¬ 7 ∣ c`.

These paths are under `DkMath.Lib.Cosmic`. The hypothesis-bearing
`DkMath.FLT.Seven.GTailBridge` and `GTailConstraintAudit` are exposed separately
by `import DkMath.FLT.Seven`. There is no reverse import into Lib; neither
owner is an unconditional nonexistence theorem.

The later (Steps008–041) FLT7 conditional research family is validated through
`import DkMath.FLT.Seven.GTail`. It directly imports all 30 dedicated GTail
owners, so use the targeted leaf module when only one theorem is needed.
The dedicated facade and `DkMathTest.FLT.Seven.GTailResearchFacade` passed
local Lean validation; this public import exports conditional research results.

Existing focused tests plus separate `DkMathTest.CosmicFormula.GTailLibFacade`
and `DkMathTest.FLT.Seven.GTailFacade` smoke tests are explicitly listed in
`DkMathTest.lean`. Lake's `DkMathTest.+` glob also discovers the individual
modules. All smoke proofs apply existing APIs; Step 007 adds no arithmetic
theorem. The exact build coverage and any broader-build blocker are recorded
in [report-007.md](report-007.md).

## Arithmetic frontier (corrected post-Step042)

The initial Step006 ledger is historical, not the current terminal list.
Steps008–038 now prove conditional q-adic square allocation, typed quadratic
and cyclotomic root evaluations, separate injections into a genuine common
quadratic receiving ring, actual prime-kernel contractions and joint ideal
sums, and the total conditional Gap/Tail split. These **do not** create the
old signed primitive next-triple or global contradiction.

Steps039–041 prove that the local square-divisibility routing survives a
**nonzero signed Fermat defect**. A finite prime-square modulus plus a
**separately assumed strict defect-size upper bound** can certify an exact
Fermat equation, not FLT7 impossibility. Positive primitive focused non-Fermat
witnesses separately satisfy only one of those two missing hypotheses.

Step042 traces the actual older terminal owners: the Row-Z signed root
extraction and Y/Z ramified summit are **complete**, despite older intermediate
reports. A terminal exponent-one away seed is **provably impossible**, while
the lifted next-primitive-triple and the original CRT independent-size/row
obstruction remain open. No scientifically justified new Step043 FLT7 proof
was selected. See [research-decision-042.md](research-decision-042.md),
[review-042.md](review-042.md), and [PR-CLOSEOUT.md](PR-CLOSEOUT.md).

## Scope discipline

1. `DkMath.Lib.Cosmic.*` contains neutral, reusable kernels and degree-seven algebraic calibration, not FLT-specific assumptions.
2. The FLT7 research bridge stays under `DkMath.FLT.Seven.*` and must import the library layer, never the reverse.
3. Lean proofs are the source of truth. No `sorry`, `admit`, added `axiom`, `unsafe`, proof by vacuous reliance on a known FLT7 theorem, or unjustified mathematics.
4. Record proof dependencies, executable focused builds, and `#print axioms` audits.
5. Prefer isolated tests and low-memory builds; only widen to façade/whole-library builds after focused checks.
6. Do not claim the GTail approach closes FLT7 until an independent, non-circular terminal contradiction is kernel checked.

## Documents

- [ROADMAP.md](ROADMAP.md): incremental implementation plan and acceptance gates.
- [instruction-007.md](instruction-007.md): bounded integration acceptance contract.
- [source-inventory-007.md](source-inventory-007.md): original Step007 source/export/dependency inventory.
- [report-043.md](report-043.md): final release validation and integration handoff.
- [source-inventory-043.md](source-inventory-043.md): complete source/test and dependency matrix.
- [PR-CLOSEOUT.md](PR-CLOSEOUT.md): final full-branch mathematical and Facade audit.
- [PR-DRAFT.md](PR-DRAFT.md): prepared PR description, truth claims and completed local validation.
- [research-decision-042.md](research-decision-042.md): source-backed STOP042 decision.
- [report-007.md](report-007.md): integration evidence, theorem family counts and engineering decision.
- [report-006.md](report-006.md): checked arithmetic, exploratory examples and unproved proposals.
- [constraint-ledger-006.md](constraint-ledger-006.md): exact premises and remaining reconstruction frontier.
- `report-001.md` through `report-005.md`, with corresponding reviews: earlier staged proof evidence.

The broad external 13-million-line proof corpus is explicitly **deferred** until this local GTail instrument has been implemented and measured.
