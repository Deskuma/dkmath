# GTail Selective-Gap / FLT7 — research closeout and PR-readiness ledger

Date: 2026-10-12  
Research branch: `feature/GTail-SelectiveGap-FLT7-261009-v0`  
Research status: **STOP042 / Outcomes B**. The implementation results are conditional or structural; **FLT7 remains unproved**.  
Release status: **Focused validation complete / full default suite PASS / READY for review**.  
Evidence: `ROADMAP.md`, `report-001.md`–`report-042.md`, `research-decision-042.md`, `review-041.md`, `review-042.md`, the checked Lean source and focused Codex test reports.

## Decision in one paragraph

The branch is **not a mathematical failure**, but it did not obtain an unconditional FLT7 impossibility or recursive descent. It formalized a genuinely reusable selective-Gap semiring theory, explicit degree-seven factorization/prime-support and valuation interfaces, ring-specific norm and cyclotomic residue maps, a novel actual common quadratic receiver and typed prime ideal joins, and non-Fermat countermodels showing exactly why those local conditions cannot force the global equation. The investigation over-invested in incrementally refined local depth/address interfaces after the noncircular descent obstruction stopped moving, and source frontier review missed the already-completed Row-Z signed seventh-root extraction until Step042. **Both the accomplishments and that corrective history should be public.** This PR should be presented as **a proven research API and limitations**, never as a proof of FLT7.

## Research output, in mathematical layers

### Layer 1 — neutral selection and conservation (Steps001–007)

- `DkMath.Lib.Cosmic.GTailSelection`: finite selected Body/Gap with exact semiring identity `(x+u)^d=Gap+Body`, including empty/full subsets and index-order precision.
- `GTailFactor`: forced monomial extraction from active term boundaries and **coefficient gcd** (not confused with evaluated-value gcd).
- `GTailTransport`: exact change-of-selection and conditional modular conservation without false blanket valuation preservation.
- `GTailSeven`, `GTailSevenArithmetic`: degree-seven interior
  `(x+y)^7=x^7+y^7+7xy(x+y)(x²+xy+y²)²` and primitive quadratic arithmetic.
- This layer was genuinely promoted into the preexisting `DkMath.Lib` facade at Step007, already protected by `DkMathTest.CosmicFormula.GTailLibFacade`.

**Mathematical classification:** reusable general algebra, not an FLT obstruction.

### Layer 2 — focused arithmetic and prime-address bookkeeping (Steps008–031)

- Under a **hypothetical** positive primitive Fermat7 equation and additive focus `a+b=c+g`, the exact scalar balance, 7-adic and non-seven q-adic divisibility budgets, exclusive Gap/Tail support, and Tail-side prime-order restrictions are proved with explicit guards.
- `TraceOneInt(-1)` realizes `Q=a²+ab+b²` as an Eisenstein norm, with distinct oriented residue ideals where the prime splits.
- The actual degree-six seventh-cyclotomic carrier is used with `RingHom` evaluations, six real root slots, actual selected-factor ideals and bounded `K²/K³/K⁴` depth contracts. Source types, inverse slot permutations, and local scalar-vs-element distinctions are retained.
- **What this does not do:** produce the original signed primitive packet, prove a global numerical balance without hEq, identify the Eisenstein and cyclotomic elements, or supply a smaller primitive Fermat7 triple.

**Mathematical classification:** useful conditional local certificates; none is an unconditional obstruction to a primitive positive Fermat solution.

### Layer 3 — a common ring instead of a nonexistent direct map (Steps032–038)

- `fermat7Equation_iff_focused_scalar_balance`: under additive focus the exact global balance is **equivalent to** the Fermat7 equation. This means the equality **cannot be used as an independent new obstruction when hEq is an input**.
- Step033 proves **there is no direct unital RingHom in either direction** between actual Eisenstein E=`TraceOneInt(-1)` and seventh-cyclotomic R, via q29 and q13 finite-field obstructions.
- Steps034–036 construct actual `C=QuadraticAlgebra R (-1) 1` with **injective** unital embeddings E→C and R→C. At q43 there are twelve distinct maximal prime kernels, with **separate typed contractions** and exact joint ideal generation
  `M_(e,j) = Ideal.map iE P_e ⊔ Ideal.map iR K_j`.
  The source ideals separately extend to **proper** subideals of M; mixed source products have **lower** M-adic power support but no proved exact M-adic valuations.
- Step037 generalizes this to a **supplied admissible prime q and native Q/T source roots**, including a genuinely joint kernel with typed contractions and ideal join. Step038 keeps a **total Gap/Tail branch**: the Gap canonical ratio is **1**, so only the Tail branch feeds the native nonidentity seventh-root receiver.
- `Ideal.map_pow` is valid. The unsupported step is to **replace a proper mapped source ideal with the larger common maximal ideal before asserting equality of powers**.
- The q43 native numerical controls `(1166,1857,1858,1165)`, `(5,8,9,4)` both satisfy additive focus but not Fermat; **do not repeat the old incorrect claim that (5,8,9,4) lacks focus**. Step041's `(13,35,46,2)` selects a **different** actual common kernel, `M(1,4)`.

**Mathematical classification:** genuinely typed cross-ring local geometry and correct non-existence of direct maps; not a prime-classification of all of C, nor an FLT7 descent.

### Layer 4 — signed defect, finite supports and insufficiency controls (Steps039–041)

Define a signed integer `Δ=a^7+b^7-c^7`. The true hEq-free focused identity is
`Δ=g*T - 7ab(a+b)Q²`.
- q|Q gives `q²|Δ ↔ q²|g*T`, **without** hEq, and from primitive q|Q plus q|Δ one can show `q∤c` without assuming the Fermat equation or even additive focus.
- Under q²|Δ, the Gap/Tail **square** routing can hold with Δ≠0; actual positive primitive focused **Gap q13 and Tail q43** non-Fermat witnesses demonstrate both possibilities, sometimes even with a selected-prime valuation-budget equality.
- For a finite set S of **distinct primes**, `M_S=∏p∈S p²` divides the signed defect exactly when every p² does. A further **independent** condition `|Δ|<M_S` yields Δ=0 and hence **Fermat7Equation**. This is a conditional **zero certificate, not an FLT impossibility theorem**. The full-support Q modulus is `rad(Q)²≤Q²`, but neither all-source support nor the size upper bound was proved from the weaker input.
- Step041 kernel-checks two real non-Fermat *existence* theorems in positive primitive strict focused geometry, separating the two hypotheses:
  A=(13,35,46,2), `Q=43²`: full support **true**, magnitude **false**;
  B=(1497,2797,2802,1492), `Q=37*385171`: magnitude **true**, full support **false**.
  These results refute the idea that either condition follows merely from focus/primitivity, **not** the valid conditional certificate.

**Mathematical classification:** rigorous non-sufficiency and independent-premise diagnosis; the global inequality still lacks a proof and the zero certificate runs in the **opposite direction** to FLT7 nonexistence.

### Layer 5 — source-corrected proof frontier (Step042)

Step042 is **documentation-only**. It identifies important already existing old FLT7 facts:
- At **terminal pivot exponent one**, `AwayDescentReconstructionSeed` and `AwayDescentClosureProvider` are proved **uninhabited**. Do not propose constructing one on that branch.
- Terminal Row-Sum is false; Row-Y reaches the natural ramified chart; terminal Row-Z's **signed discriminant−7 seventh-root extraction is ALREADY PROVED** in `SevenBaseTerminalRowZSignedResidualCore` (TERM-010) and the surviving terminal rows already reach a `PrimitiveRamifiedSummitPacket`. Historical `review-041.md`/`instruction-042.md` said Row-Z was open; `review-042.md` and Step042 report explicitly **correct** that outdated claim without rewriting history.
- Lifted-away descent still lacks **explicit new positive primitive nextX/Y/Z** and exact carrier matching, despite existing seed ↔ provider and strict-depth-drop contracts.
- Internal ramified depth5→4 is genuine but not a reconstructed primitive counterexample. The direct visible signed-root Fermat chart is already **ruled out** by an exact 7-adic obstruction.
- CRT's **original integer** residual is divisible by the combined modulus, but needs *independent* original-coordinate magnitude bounds and a final row mismatch; individually centered weighted representatives are a **different** object.

**Research decision:** No viable noncircular Step043 theorem was selected at STOP042. The PR closeout / Facade / tests should **not reopen proof exploration** or smuggle in a fictional descent constructor.

## Facade and import ownership

**Already present before PR closeout:**
- `import DkMath.Lib`: explicitly promotes the initial neutral `GTailSelection/GTailFactor/GTailTransport/GTailSeven/GTailSevenArithmetic` subset; neutral later research owners under `DkMath.Lib.*` can still be consumed by targeted imports and are not automatically promoted as stable just because a name starts with `Lib`.
- `import DkMath.FLT.Seven`: broad historical FLT7 facade, explicitly imports only `GTailBridge` and `GTailConstraintAudit` from this research family; **not** a convenient explicit public API for the later GTail sequence.
- Existing Step007 `DkMathTest.FLT.Seven.GTailFacade`: older broad-facade smoke covering only initial API.

**Added in the checked PR scope:**
- `DkMath/FLT/Seven/GTail.lean`: separate, scoped public `import DkMath.FLT.Seven.GTail` facade, importing the **30 added GTail-specific FLT modules**. This is an aggregator only; no proof, axiom, contrary E↔R hom or FLT7 result is introduced.
- `DkMathTest/FLT/Seven/GTailResearchFacade.lean`: public smoke with `#check` and selected `#print axioms`, importing ONLY the new scoped facade.

## Final local validation (2026-10-12)

Validated Lean sources at HEAD `caebaf0ec98c12e1e570b6e2e9aefb2aa2362f7e`, Lean 4.34.1, using process-local `LEAN_NUM_THREADS=2`. No Lean source or test repair was necessary. All five entrance builds and all 49 added test targets exited 0. The new research smoke was actually **Built**; other focused targets reused existing artifacts (**Replayed**). This is a current invocation with cache reuse, not a clean rebuild.

The complete `LEAN_NUM_THREADS=2 lake test` exited 0 in 9.75 s within a 180 s bound. Its `DkMathTest.+` library glob discovered all 49 added tests, including the new research smoke. The root driver needs no extra imports. Full-suite and old broad-facade success includes existing unrelated `sorry` warnings: 5 in the full suite, four in the old broad smoke. The dedicated GTail, neutral Lib and new-test regressions have warnings 0; scanned added Lean sources have no forbidden placeholders or shortcuts. Selected public axiom outputs use only `propext`, `Classical.choice`, `Quot.sound`.

The source inventory distinguishes 30 specialized owners + one scoped facade, 17 neutral owners and 49 tests. `DkMath.Lib` promotes only five of the 17 added neutral owners. The scoped facade imports all 30 specialized owners exactly once, has no dependency on the old `DkMath.FLT.Seven` aggregator, and introduces no mathematical declaration. The local dependency DAG has 473 vertices and no cycles; neutral owners and Lib have no FLT reachability.

See [source-inventory-043.md](source-inventory-043.md) for complete ownership/test coverage, and [report-043.md](report-043.md) for exact commands, timings, warnings, axiom names and audit exceptions. Local logs live under `.lake/build/gtail-step043/`; these ignored artifacts are not a committed evidence archive.

## Branch and integration handoff

After a successful `git fetch origin`, HEAD is `caebaf0ec98c12e1e570b6e2e9aefb2aa2362f7e` on `feature/GTail-SelectiveGap-FLT7-261009-v0`: **ahead 136 / behind 1** versus `origin/develop`. The HEAD merge-base comparison changes **287 files: 283 added / 4 modified**. Additions comprise 48 production Lean files (30 FLT owners + facade + 17 neutral owners), 49 tests and 186 documents. The four modified existing files are `DkMath/FLT/Seven.lean`, `DkMath/Lib.lean`, `DkMath/Lib/README.md`, `DkMathTest.lean` (paths relative to `lean/dk_math`). These counts exclude the subsequent release-document working changes.

The develop-only commit is `ad8526451` (`docs: propose CF2D multiplicative quadratic norm generalization`), adding only `docs/not_implements/261010-CF2D-Multiplicative-Quadratic-Norm-Generalization.md`. Recommend an ordinary develop merge after separate authorization, then rerun validation against the resulting HEAD; current integration risk appears limited to that independent document, but a merge has not been tested. A split between neutral Lib and FLT7 research could make this large PR easier to review; it has not been performed. Base: `develop`; head: `feature/GTail-SelectiveGap-FLT7-261009-v0`. The final title and body are [PR-DRAFT.md](PR-DRAFT.md).

The preparation verdict is **READY for review**, with existing broad-suite placeholder warnings and branch integration explicitly recorded. Research remains **Outcome B / STOP042**. No PR opening or Git integration is part of this handoff.

## Reviewer's bottom line

The lasting new deliverables are: (i) a reusable selection/conservation algebra; (ii) correct explicit primitive q-valuation and seventh-root routing; (iii) a genuine common receiver with prime-ideal intersections/joins and clear no-direct-map theorem; (iv) proof-level countermodels to local sufficiency; (v) an exact index of the remaining global hypotheses, with the old Row-Z terminal extraction **corrected to COMPLETE**. The work is partially exploratory and sizeable, but neither mathematically vacuous nor an FLT7 proof. The local release gates are complete; Git integration and review remain separate decisions.
