# ROADMAP — GTail Selective-Gap / FLT7

Branch: **feature/GTail-SelectiveGap-FLT7-261009-v0**  
Status: **Step 000–006 COMPLETE; Step 007 PARTIAL — Outcome B** (public integration checked; all-test-submodule gate interrupted for cost)

## Proof-oriented stages

| Step | Owner | Deliverable | Acceptance gate |
| --- | --- | --- | --- |
| 000 | Codex | Current `develop` theorem/API inventory; exact names, carriers, overlap, plan | Source-indexed report; no duplicate definitions |
| 001 | Codex | `DkMath/Lib/Cosmic/GTailSelection.lean` — selective index sets, Body/Gap, balance, select-all/none, interval-to-GTail | Focused build; semiring kernel proof |
| 002 | Codex | `DkMath/Lib/Cosmic/GTailFactor.lean` — extremal-index monomial factor, coefficient gcd/content, endpoint presence/absence | Typed ring/Nat hypotheses; tests for zero/empty selections |
| 003 | Codex | `DkMath/Lib/Cosmic/GTailTransport.lean` — move one selected term; general symmetric-difference transport; exact balance | No unsupported gcd/valuation preservation claims |
| 004 | Codex | `DkMath/Lib/Cosmic/GTailSeven.lean` — degree-seven cut kernels and both-endpoints-removed norm-square identity | Ring/semiring proof; independent evaluation regression |
| 005 | Codex | `DkMath/FLT/Seven/GTailBridge.lean` — connect FLT7 hypothetical equation to `g * GTail 7 1 g c` | No circular FLT7 imports; characterize genuine new obstructions |
| 006 | Codex + researcher | Constraint audit: primitive, boundary gcd, valuation, norm/unit-gauge transport, possible descent | Clear A/B/C outcome; smallest honest theorem |
| 007 | Codex | façade export, `DkMath.Lib` README updates, focused and broader build, axioms, final report | All touched targets kernel checked; diff reviewed |

## Algebraic contracts

### Selection and balance

Use the existing `GTail` convention: term index `k` denotes the power of `x` in
`t_k = (choose d k : R) * x^k * u^(d-k)`.
Define `selectedBody d S x u` and `selectedGap d S x u` using `Finset.range (d+1)` and a bounded membership predicate. Full identity:

```text
(x+u)^d = selectedGap d S x u + selectedBody d S x u
```

Use `CommSemiring` where possible; no synthetic subtraction assumptions.

### Factor extraction

For a nonempty finite subset S of `0..d` with extremal indices `i=min S` and `j=max S`, demand the explicit polynomial factor

```text
selectedBody d S x u = x^i * u^(d-j) * residual(d,S,x,u)
```

(Notice the existing `GTail` indexes `x^k`, not `x^(d-k)`.) Separately analyze the gcd/content of binomial coefficients `choose d k` for k in S over naturals/integers. Avoid claiming the exact integer-value gcd equals polynomial content for arbitrary x,u.

For prime p > 1, removing k=0 and k=p gives the interior sum, which is divisible by `p*x*u` as a polynomial over integers; degrees 7 and 3 are regression cases.

### Selection transport

For toggling a single index k, prove that the moved `t_k` appears with opposite effects on Gap and Body, so Big stays fixed. Any preserved support/gcd statement must carry its exact hypotheses.

### Degree-seven test surface

```text
GTail 7 6 x u = x + 7*u
GTail 7 5 x u = x^2 + 7*x*u + 21*u^2
(x+u)^7 = x^7 + u^7 + 7*x*u*(x+u)*(x^2+x*u+u^2)^2
```

The last equality is semiring-friendly and keeps the Big/Gap/Body balance visible. The bracket `x^2+x*u+u^2` admits an Eisenstein-norm interpretation but no unproved identification with a FLT7 cyclotomic-unit carrier is permitted.

### FLT7 bridge

Given `a^7+b^7=c^7` and `a+b=c+g`, derive:

```text
g * GTail 7 1 g c
  = 7*a*b*(a+b)*(a^2+a*b+b^2)^2
```

Proof route: exact degree-seven selection identity plus the existing `r=1` GN/GTail factorization. Do not derive a contradiction merely by importing an independently completed FLT7 theorem. The small positive-gap inequality is optional and must have honest hypotheses.

## Validation protocol

Working directory: `lean/dk_math`.

- `lake build DkMath.Lib.Cosmic.GTailSelection` after Step 001.
- Analogous focused `lake build` for each new module, then relevant `DkMathTest` targets.
- `#print axioms` for each publicly promoted theorem; standard Lean foundations permitted, no nonstandard extra axioms.
- Check forbidden placeholders and undeclared assumptions; record exact command and exit status.
- Avoid massive parallel clean builds on memory-limited environments; prefer focused sequential builds.
- Maintain `report-00N.md` after each stage: changed paths, theorem signatures, reusable vs domain-specific content, build and axiom evidence, limitations.

## Outcome classifications

- **A — genuine new obstruction:** from the hypothetical FLT7 packet, a new noncircular arithmetic restriction is obtained.
- **B — algebraic instrument only:** GTail selection/factor/transport is kernel checked, but arithmetic closure is not reached.
- **C — obstruction / counterexample to proposed transport:** a hoped-for invariant fails or needs stronger hypotheses, documented precisely.

Outcome B or C is scientifically useful; never disguise it as A.

## Non-goals

- No import of existing unconditional FLT7 closure as a premise.
- No assumption that an exact polynomial identity forces a contradiction.
- No rewrite of the full GN/FLT packages while building neutral API.
- No external large-corpus proof search yet.
- No Mathlib upstream submission during this exploratory branch.

## Current progress

- [x] Develop-based branch created.
- [x] README / ROADMAP / first Codex instruction drafted.
- [x] Step 000 source inventory and Step 001 implementation (Codex): exact semiring balance, empty/full/complement/singleton APIs, interval-to-GTail adapters, focused regressions and axiom audit.
- Direct import: `DkMath.Lib.Cosmic.GTailSelection`; façade promotion remains Step 007.
- Evidence: `source-inventory-001.md` and `report-001.md`.
- [x] Step 002: bounded monomial factor and active min/max adapter, natural coefficient gcd and endpoint content, exact prime interior gcd and `p*x*u` divisor; focused regressions and all 16 axiom checks.
- Direct import: `DkMath.Lib.Cosmic.GTailFactor`; no façade promotion in Step 002.
- Evidence: `source-inventory-002.md` and `report-002.md`.
- [x] Step 003: single-term and arbitrary active-set movement, no-op boundaries, exact Big conservation, interval/GTail adapter and generic guarded modular conservation; coefficient-content/nonpreservation regressions and all 12 public axiom checks.
- Direct import: `DkMath.Lib.Cosmic.GTailTransport`; façade promotion remains deferred.
- Evidence: `source-inventory-003.md` and `report-003.md`.
- [x] Step 004: degree-seven GTail cuts, selected interior residual square and Body factor, balanced reconstruction, separate ring subtraction and calibrated endpoint transport; independent ring/numeric regressions and all 15 public axiom checks.
- Direct import: `DkMath.Lib.Cosmic.GTailSeven`; no genuine norm-map or FLT7 claim.
- Evidence: `source-inventory-004.md` and `report-004.md`.
- [x] Step 005: general CommSemiring shell with only the additive coordinate relation, separate CommRing defect, natural Fermat adapter by same-endpoint cancellation, and equation-only candidate-packet adapter; satisfiable numeric and zero-boundary regressions, all 4 public axiom checks.
- Direct imports: `DkMath.Lib.Cosmic.GTailSeven` and `DkMath.FLT.Seven.Basic`; no façade promotion or closure endpoint.
- Evidence: `source-inventory-005.md` and `report-005.md`.
- [x] Step 006: positive focused-gap certificate, known mod-seven condition recovered through GTail, four neutral quadratic coprimality endpoints and explicit endpoint-unit seven-layer receiver; nine axiom checks, missing-premise counterexamples and reconstruction/unit-normalization ledger.
- Direct imports: `DkMath.FLT.Seven.GTailConstraintAudit` and narrow `DkMath.Lib.Cosmic.GTailSevenArithmetic`; no heavy FLT7 owner or façade promotion.
- Evidence: `source-inventory-006.md`, `constraint-ledger-006.md`, `report-006.md` (including checked examples, exploratory observations and deferred implementation targets).
- [x] Step 007 public imports: five neutral modules explicitly exposed by `DkMath.Lib`; two conditional owners exposed by `DkMath.FLT.Seven`; eight direct test-driver additions and separate public-import smoke tests.
- [x] Step 007 focused regressions, Lib/Seven entrances, both public smoke tests, the DkMath root/import-closure build, and `lake lean DkMathTest.lean` for the edited root file; all 66 public endpoint axiom lists use only standard foundations.
- [ ] Step 007 overall/full-test gate: `lake build DkMathTest` was interrupted after >15 minutes (runner session 130; remaining Lake child terminated during cleanup) of existing unrelated test/calibration work; 400 of 683 test module names logged as completed/replayed. No full-test success is claimed. Edited root-driver file elaboration passed separately; command repair and cleanup are recorded in report-007.
- Evidence: `source-inventory-007.md`, `report-007.md`; `constraint-ledger-006.md` remains unchanged.
- At Step 007 closeout the arithmetic frontier remained Outcome B: no new valuation/order-21/Norm-unit transport theorem, next packet, descent or FLT7 closure.

## Post-integration Step 008 — seven-adic calibration

- [x] Step 008 COMPLETE / Outcome B: endpoint-unit residual valuation one, nonzero gap-product valuation, and conditional exact focused-gap balance; three public axiom checks on standard foundations.
- [x] Separate direct-import tests: (7,2), (14,2), zero-gap boundary, and the missing-endpoint-unit counterexample (7,7); relevant prior focused regressions pass.
- Evidence: [source-inventory-008.md](source-inventory-008.md), [report-008.md](report-008.md). No facade promotion or broad build in Step 008.
- Subsequent owner all-test success: `./lb -T` (routes to `lake test`), recorded separately in [validation-addendum-007.md](validation-addendum-007.md). The historical Step 007 interrupted run is unchanged; runtime commit identity was not captured in that owner log.
- Deferred v7(g) conservation is now proved under the stated endpoint-unit/positive-equation hypotheses. Optional unit-branch 49∣g, q² allocation, order-21, Norm/unit-class transfer and next-packet construction remain open in this checkpoint. The historical [constraint-ledger-006.md](constraint-ledger-006.md) remains intact.
