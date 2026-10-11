# PR draft — GTail selective-gap algebra and conditional FLT7 research interfaces

**Suggested title:** `feat(math): package GTail selective-gap kernels and FLT7 conditional research APIs`

**Base:** `develop`  
**Head:** `feature/GTail-SelectiveGap-FLT7-261009-v0`  
**Status:** Focused validation complete / full default suite PASS / READY for review. Branch integration remains a separate authorized action.  
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

The dedicated `DkMath.FLT.Seven.GTail` facade is a locally validated import aggregator. It exposes 30 added `GTail*.lean` FLT modules, without importing the massive historical `DkMath.FLT.Seven` facade. The older `DkMath.FLT.Seven` still explicitly lists the first two GTail modules and remains otherwise unchanged for this PR. All 49 added test imports passed the focused matrix and the default suite. The new smoke target is `DkMathTest.FLT.Seven.GTailResearchFacade`.

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

## Final local validation (2026-10-12)

Validated Lean sources at HEAD `caebaf0ec98c12e1e570b6e2e9aefb2aa2362f7e`, Lean 4.34.1, using process-local `LEAN_NUM_THREADS=2`. No Lean source or test repair was necessary. All five entrance builds and all 49 added test targets exited 0. The new research smoke was actually **Built**; other focused targets reused existing artifacts (**Replayed**). This is a current invocation with cache reuse, not a clean rebuild.

The complete `LEAN_NUM_THREADS=2 lake test` exited 0 in 9.75 s within a 180 s bound. Its `DkMathTest.+` library glob discovered all 49 added tests, including the new research smoke. The root driver needs no extra imports. Full-suite and old broad-facade success includes existing unrelated `sorry` warnings: 5 in the full suite, four in the old broad smoke. The dedicated GTail, neutral Lib and new-test regressions have warnings 0; scanned added Lean sources have no forbidden placeholders or shortcuts. Selected public axiom outputs use only `propext`, `Classical.choice`, `Quot.sound`.

The source inventory distinguishes 30 specialized owners + one scoped facade, 17 neutral owners and 49 tests. `DkMath.Lib` promotes only five of the 17 added neutral owners. The scoped facade imports all 30 specialized owners exactly once, has no dependency on the old `DkMath.FLT.Seven` aggregator, and introduces no mathematical declaration. The local dependency DAG has 473 vertices and no cycles; neutral owners and Lib have no FLT reachability.

See [source-inventory-043.md](source-inventory-043.md) for complete ownership/test coverage, and [report-043.md](report-043.md) for exact commands, timings, warnings, axiom names and audit exceptions. Local logs live under `.lake/build/gtail-step043/`; these ignored artifacts are not a committed evidence archive.

## Branch and integration handoff

After a successful `git fetch origin`, HEAD is `caebaf0ec98c12e1e570b6e2e9aefb2aa2362f7e` on `feature/GTail-SelectiveGap-FLT7-261009-v0`: **ahead 136 / behind 1** versus `origin/develop`. The HEAD merge-base comparison changes **287 files: 283 added / 4 modified**. Additions comprise 48 production Lean files (30 FLT owners + facade + 17 neutral owners), 49 tests and 186 documents. The four modified existing files are `DkMath/FLT/Seven.lean`, `DkMath/Lib.lean`, `DkMath/Lib/README.md`, `DkMathTest.lean` (paths relative to `lean/dk_math`). These counts exclude the subsequent release-document working changes.

The develop-only commit is `ad8526451` (`docs: propose CF2D multiplicative quadratic norm generalization`), adding only `docs/not_implements/261010-CF2D-Multiplicative-Quadratic-Norm-Generalization.md`. Recommend an ordinary develop merge after separate authorization, then rerun validation against the resulting HEAD; current integration risk appears limited to that independent document, but a merge has not been tested. A split between neutral Lib and FLT7 research could make this large PR easier to review; it has not been performed. Base: `develop`; head: `feature/GTail-SelectiveGap-FLT7-261009-v0`. The final title and body are [PR-DRAFT.md](PR-DRAFT.md).

The preparation verdict is **READY for review**, with existing broad-suite placeholder warnings and branch integration explicitly recorded. Research remains **Outcome B / STOP042**. No PR opening or Git integration is part of this handoff.

## Suggested review order

1. Read `PR-CLOSEOUT.md` for honest scientific conclusion and `research-decision-042.md` for the corrected FLT7 frontier.
2. Audit reusable `DkMath.Lib.Cosmic.GTailSelection/Factor/Transport/GTailSeven`.
3. Inspect FLT7 bridge and exact scalar-balance iff.
4. Inspect cross-ring no-direct-hom, common receiver and actual ideal join.
5. Inspect hEq-free signed defect, conditional capacity and two independence countermodels.
6. Verify new `DkMath.FLT.Seven.GTail` public facade, smoke/axiom audit and source/test matrix.

The checked handoff is prepared; opening or merging requires a separate user instruction.
