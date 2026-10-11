# PR draft — GTail selective-gap algebra and conditional FLT7 research interfaces

**Suggested title:** `feat(math): package GTail selective-gap kernels and FLT7 conditional research APIs`

**Base:** `develop`
**Head:** `feature/GTail-SelectiveGap-FLT7-261009-v0`
**Status:** DRAFT ONLY — **DO NOT SUBMIT** until local closeout build, regression, and branch sync are verified.
**Research classification:** Outcome B / STOP042. **Not a proof of FLT7.**

## Summary

This PR formalizes a reusable GTail term-selection/transport kernel and makes the degree-seven selected-Gap arithmetic interfaces explicit. It preserves source ownership between neutral `DkMath.Lib.*` and hypothesis-bearing `DkMath.FLT.Seven.*`.

The FLT7 study proves conditional q-adic Gap/Tail prime allocation, typed quadratic norms and seventh-cyclotomic ideal addresses, an actual common receiving ring with compatible source embeddings and maximal-ideal joins, a generic q-prime source-linked receiver, and explicit signed-defect / finite-prime-support thresholds. Lean countermodels demonstrate that local congruences, individual valuation budgets, source ideal joins and either half of the global defect-size certificate **do not suffice** to derive the Fermat equation or a primitive descent.

The existing historical FLT7 terminal Row-Z `TraceOneInt(-2)` root extraction **is already complete** (TERM-010). This branch does not redo it or close FLT7.

## User-facing imports

```lean
import DkMath.Lib
-- General selected-Gap semiring, forced residual factor and exact transport.

import DkMath.FLT.Seven.GTail
-- Specialized exponent-seven conditional theory and finite-field/common-ring APIs.
```

The dedicated `DkMath.FLT.Seven.GTail` facade is a new staged import aggregator. It exposes 30 added `GTail*.lean` FLT modules, without importing the massive historical `DkMath.FLT.Seven` facade. The older `DkMath.FLT.Seven` still explicitly lists the first two GTail modules and remains otherwise unchanged for this PR. All new source and test imports must be built before publication.

## Representative proved results

- `selectedGap_add_selectedBody` and exact selection transport over a commutative semiring.
- `fermat7Equation_iff_focused_scalar_balance`: under focus, exact balance **iff** Fermat7Equation; not an independent contradiction.
- Nonexistence of direct unital E↔R RingHoms for `E=TraceOneInt(-1)`, `R=SevenCyclotomicDegreeSixInt.Ring`.
- Genuine embeddings E→C and R→C with `C=QuadraticAlgebra R (-1) 1`, typed q43 prime-grid contractions and `M_(e,j)=A_e⊔B_j`.
- Generic q-prime native Q/T paired kernel; only the nontrivial Tail branch has the canonical cyclotomic root needed for it.
- Signed `Δ=a⁷+b⁷−c⁷` and **hEq-free** q² defect Gap/Tail routing.
- Finite pairwise-prime-square modulus `M_S=∏p∈S p²`; **conditional** `M_S|Δ ∧ |Δ|<M_S → Δ=0`.
- Two actual positive primitive focused **non-Fermat** countermodels separate all-Q-prime-square support from `|Δ|<M_Q`; a new actual q43 source tuple selects the grid ideal `M(1,4)`.

## Explicit non-goals and caveats

- No `fermatSeven_no_positive_solution`, unconditional FLT7 theorem, signed primitive next-triple construction, global contradiction or verified away descent.
- The Step040 `Δ=0` certificate concludes **Fermat equality**, not the impossibility of a Fermat solution.
- The old discriminant−7 signed ramified source ring is distinct from the new discriminant−3 Eisenstein common receiver.
- Distinct source elements may share a residue; mapped source ideals can be strictly smaller than a common prime; no exact valuation synchronization or complete prime spectrum is claimed.
- Step042 corrected an earlier reviewer mistake: Row-Z signed extraction is complete already; actual unresolved FLT7 frontier is downstream.
- This PR is deliberately large: optional split of neutral Lib and FLT7 research may improve reviewability; such a split has **not** been performed.

## Validation — fill from ACTUAL final HEAD, not old reports

- [ ] `LEAN_NUM_THREADS=2 lake build DkMath.FLT.Seven.GTail` (new dedicated facade)
- [ ] `LEAN_NUM_THREADS=2 lake build DkMathTest.FLT.Seven.GTailResearchFacade` (new public API smoke / axiom outputs)
- [ ] `LEAN_NUM_THREADS=2 lake build DkMath.Lib`
- [ ] Final production/test module matrix: record commands, number of targets, success/failure, warnings
- [ ] Representative and new-public theorem `#print axioms`; no `sorry`, `admit`, added axiom, `unsafe`
- [ ] Import DAG and neutral Lib→FLT direction check; review transitive dependency/compile time
- [ ] Actual default Lake test suite or documented limited-coverage explanation with specific passing targets
- [ ] `git diff --check`, whitespace, source-ownership and docs links
- [ ] Inspect `develop` one-commit divergence and choose an approved sync approach
- [ ] Update current research README and PR closeout from final build results; confirm PR scope

**Old milestone evidence:** Step001–041 focused builds and axiom audits are recorded in their individual `report-00N.md`; Step042 is **docs-only with no new build**. The new facade and smoke were not present during those milestone builds. Do not label any current-HEAD validation PASS until Codex actually executes it.

## Suggested review order

1. Read `PR-CLOSEOUT.md` for honest scientific conclusion and `research-decision-042.md` for the corrected FLT7 frontier.
2. Audit reusable `DkMath.Lib.Cosmic.GTailSelection/Factor/Transport/GTailSeven`.
3. Inspect FLT7 bridge and exact scalar-balance iff.
4. Inspect cross-ring no-direct-hom, common receiver and actual ideal join.
5. Inspect hEq-free signed defect, conditional capacity and two independence countermodels.
6. Verify new `DkMath.FLT.Seven.GTail` public facade, smoke/axiom audit and source/test matrix.

Do not open or merge this PR until its checked validation block is filled. 
