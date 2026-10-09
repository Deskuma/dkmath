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

## Step 009 — exact seven-unit branch

- [x] Step 009 COMPLETE / Outcome B: proved endpoint-to-sum unit transfer, v7(g)=2*v7(Q), 7∣Q and 49∣g under the positive exact equation and three coordinate-unit hypotheses.
- [x] Neutral abstract-product allocation and positive-even valuation conversion; satisfiable (g,T,A,B,C,Q)=(49,7,1,1,1,7) calibration.
- [x] Kernel-checked (a,b,c,g)=(8,9,10,7) mod49-only example, explicit exact-equation failure, 49∤g and failure of doubled valuation; all six new public axiom checks, direct test builds and both Step 008 regressions pass.
- Evidence: [source-inventory-009.md](source-inventory-009.md), [report-009.md](report-009.md). Prior local constraints compared by name/hypotheses; no independent new obstruction claimed.
- Step 008's then-deferred unit-branch item is now proved under exact hypotheses. Separate q-square allocation, order-21, Norm/unit-class transport and constructive next packet remain open. The historical constraint ledger and earlier reports are unchanged. No facade promotion or full-suite build.

## Step 010 — q-local square budget and exclusive allocation

- [x] Step 010 COMPLETE / Outcome B: head-unit prime exclusion, ordinary-factor q-units, derived local endpoint q-unit and exclusive focused support at prime q≠7 dividing Q.
- [x] Exact doubled q-budget and exclusive square allocation under positive primitive exact equation/focus hypotheses; no hidden endpoint-unit or global gap-coprimality premise.
- [x] Actual GTail addresses (13,13,2) and (43,3,1); satisfiable exclusive and mixed abstract products; all eight new public axiom checks, direct tests and Step 009 regressions pass.
- Evidence: [source-inventory-010.md](source-inventory-010.md), [report-010.md](report-010.md). Existing typed prime-support/cyclotomic interfaces compared by path and hypotheses; no independent new obstruction claimed.
- The previously deferred q-budget and unsplit-square allocation are now checked under the full exact premises plus proved local exclusion. No universal choice of the left/right branch. Historical ledger remains intact. Order-21, Norm/unit carrier transport and constructive descent remain open. No facade promotion or all-suite build.

## Step 011 — tail-side finite-field order intersection

- [x] Step 011 COMPLETE / Outcome B: independent nontrivial order-seven and order-three neutral mechanisms; derive q≠3 on the tail side; combine coprime orders to prove 21∣q-1.
- [x] Exact branch-guarded receiver derives all units and q∤g from Step 010 support. Optional non-order-21 routing allocates q² to the gap under positive exact hypotheses.
- [x] Complete q=43 modular calibration (5,8,9,4), q=13 gap contrast (14,29,30,13), characteristic-three/seven boundaries; all six new public axiom checks, direct builds and Step 010 regressions pass.
- Evidence: [source-inventory-011.md](source-inventory-011.md), [report-011.md](report-011.md). No exact Fermat solution, universal order-21 restriction or independent new obstruction claimed.
- The order-21 candidate is now checked specifically on the tail branch. Historical ledger is unchanged. Typed Norm/unit carrier conversion, constructive next packet and descent remain open. No facade promotion or broad build.

## Step 012 — typed quadratic norm readout

- [x] Step 012 COMPLETE / Outcome B: existing TraceOneInt(-1) coordinate with corrected Eisenstein sign, norm Q, multiplicative norm-square Q², natural/integer norm-value divisor iff and selected Body norm-square identity.
- [x] Conditional focused product cast to integers preserves the natural GTail term; no stronger element-factorization premise or conclusion.
- [x] Sign/cast boundaries, Q(5,8)=129, Q²=16641, Body=60573240, signed square coordinate and distinct norm-one pair; all six new public axiom checks, four direct builds and both Step 011 regressions pass.
- Evidence: [source-inventory-012.md](source-inventory-012.md), [report-012.md](report-012.md). No facade promotion or broad build.
- Typed quadratic norm-value readout is now checked. Cyclotomic/other-carrier conversion, prime ideals, unit-power extraction, next packet and descent remain open. Historical frontier entries and ledger remain unchanged.

## Step 013 — oriented Eisenstein residue slots

- [x] Step 013 COMPLETE / Outcome B: existing element conjugation at α, scalar ring q divisibility iff both natural coordinates, and the norm-only scalar-divisibility countercheck.
- [x] Canonical t=-a/b in prime ZMod q under q∤b, both quadratic root relations, zero first slot, conjugate trace slot, and nonzero/distinct conjugate orientation under q≠3. Evaluation addition/multiplication/conjugation proved.
- [x] Actual q=43 slots 37/7 with evaluations 0/18, q=3 repeated-root boundary, b=0 conjugation, signed-coordinate checks; all 15 public definition/theorem axiom checks, two new builds and both Step 012 regressions pass.
- Evidence: [source-inventory-013.md](source-inventory-013.md), [report-013.md](report-013.md). Neutral direct imports only; no optional FLT adapter or facade promotion.
- Residue orientation is checked without Fermat premises. Prime ideals, other cyclotomic carriers, unit classes, norm-to-element reconstruction, next packet and descent remain open. Historical ledger and prior owners remain unchanged.

## Step 014 — bundled residue kernels

- [x] Step 014 COMPLETE / Outcome B: Step 013 evaluation laws packaged as root-guarded RingHom and actual kernel ideals, with ofInt/tau/conjugation readouts.
- [x] Arbitrary integral-element residue norm-product and prime-q norm-divisor iff membership in one conjugate kernel. Root existence remains an explicit premise.
- [x] Scalar modulus membership, surjectivity and optional prime-field kernel maximality checked; q=43 prime consequence tested. Canonical oriented membership/exclusion proves distinct ideals away from q=3.
- [x] Twenty examples include q=43 scalar-vs-ideal boundary, conjugate orientation, q=3 coincident kernels and a nonroot multiplication countercheck. All16 public axiom checks, two focused targets and Step013 regression pass.
- Evidence: [source-inventory-014.md](source-inventory-014.md), [report-014.md](report-014.md). No facade promotion or FLT owner adapter.
- These are actual ideals in TraceOneInt(-1). Principal scalar ideal product, comaximality, cyclotomic ideal/unit transfer, element-square reconstruction and descent remain unproved in this checkpoint. Historical owners/ledger remain unchanged.

## Step 015 — split scalar-prime ideal factorization

- [x] Step015 COMPLETE / Outcome B, product gate PASSED: arbitrary integral two-slot coordinate reconstruction, general scalar coordinate-divisibility iff, and exact ideal intersection with the scalar principal ideal.
- [x] Supplied-root separation from prime q≠3, a lifted integral membership witness for distinct kernels, checked comaximality, and product=scalar ideal in TraceOneInt(-1).
- [x] Nineteen examples: q=43 inf/product/sup, natural α versus scalar membership, signed coordinates, q=3 failed intersection without separation, q=5 no-root boundary. All10 public axiom checks, two focused targets and Step014 regression pass.
- Evidence: [source-inventory-015.md](source-inventory-015.md), [report-015.md](report-015.md). Root existence/separation remain explicit; no public facade or FLT owner addition.
- The previously open split intersection/comaximal product is now checked in the degree-two ring. The q=3 counterexample concerns intersection; its product decomposition is unproved here. Cyclotomic transport, class/unit claims, element-square reconstruction, primitive next packet and descent remain open. Historical owners and ledger remain unchanged.

## Step 016 — ramified three principal kernel

- [x] Step016 COMPLETE / Outcome B: π=1+τ in TraceOneInt(-1), normπ=3, π²=3τ and the explicit inverse τ(1-τ)=1 checked.
- [x] Arbitrary signed kernel membership iff π-divisibility uses the existing nonzero-norm lattice criterion. The full kernel P=span{π}, and principal-product/generator comparisons prove P*P=(3).
- [x] Twenty-six examples include P∩P=P≠(3) alongside P²=(3), noncomaximality with itself, signed quotient witnesses and direct ring computations. All17 public axiom checks, two new focused targets and unchanged Step015 regression pass.
- Evidence: [source-inventory-016.md](source-inventory-016.md), [report-016.md](report-016.md). No facade or FLT owner addition.
- The formerly unproved ramified product now holds by a separate principal-generator proof; historical intersection failure remains true. General ideal valuations, cyclotomic/unit transport, norm-square inversion, next primitive packet and descent remain open.

## Step 017 — selected-element ideal-square support

- [x] Step017 COMPLETE / Outcome B: arbitrary integral norm3 support iff repeated-root membership, hence embedded scalar3 divides z² via the checked ramified ideal product. Natural selected-element adapter added.
- [x] Oriented split-square support: square lies in the chosen ideal square, not in its conjugate prime kernel or scalar(q), with explicit root/separation/base orientation. Canonical natural α adapter checked.
- [x] Twenty-two examples compare ramified π/signed z and split q43 α²=⟨-39,144⟩, where norm has43² support but embedded43 does not divide the square. All7 public axiom checks, two new targets and unchanged Step016/015 regressions pass.
- Evidence: [source-inventory-017.md](source-inventory-017.md), [report-017.md](report-017.md). No optional FLT owner/facade addition.
- These are actual element/ideal-square support facts, not exact ideal-adic exponents or principal-square equality. GTail-to-cyclotomic carrier maps, normalized unit classes, next primitive tuple and descent remain open. Historical owners/ledger remain unchanged.

## Step 018 — paired roots in a shared finite field

- [x] Step018 COMPLETE / Outcome B: neutral t=−a/b and r=(c+g)/c in the same ZMod q; quadratic relation, seventh power, nontriviality/nonzero and guarded seven-term sum checked.
- [x] Existing Step014/017 oriented Eisenstein addresses combined in a general test example, without a new ideal wrapper or carrier transfer.
- [x] Twenty examples cover satisfiable q43 t37/r11 with false Fermat equation, q13 Gap support, q3/q5/q7 boundaries and r1 geometric-sum failure. All6 public axiom checks, two new targets and Step017 plus both Step011 regressions pass.
- Evidence: [source-inventory-018.md](source-inventory-018.md), [report-018.md](report-018.md). Existing degree-six localEval requires a signed-depth quotient-prime address; this checkpoint does not construct it from natural Q/T hypotheses.
- Integral carrier maps, cyclotomic ideal/unit identification, next primitive packet and descent remain open. No optional FLT owner or facade promotion; historical ledger and prior owners remain unchanged.
