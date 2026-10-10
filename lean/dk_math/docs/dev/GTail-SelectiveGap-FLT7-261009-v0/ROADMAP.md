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

## Step 019 — packet-free seventh-cyclotomic evaluation

- [x] Step019 COMPLETE / Outcome B: neutral beta=1+r+r⁻¹ cubic relation and actual signed real-cubic / degree-six RingHoms from a bare nontrivial seventh root, using the existing carriers.
- [x] Natural Tail ratio evaluation sends the specifically oriented factor ofReal(c+g)−zeta*ofReal(c) to zero and proves actual degree-six kernel membership, without a signed-depth packet.
- [x] Eight neutral and twenty-two carrier examples check q43 inverse4/beta16/zeta11/zero factor with false Fermat equation, signed coordinates, separate Eisenstein evaluation, q13 Gap and q3/q5/q7 controls. All14 public axiom checks, four final focused targets and Step018/017 regressions pass.
- Evidence: [source-inventory-019.md](source-inventory-019.md), [report-019.md](report-019.md). Existing packet-indexed APIs remain unchanged; no packet reconstruction or equality with their canonical inputs is claimed.
- Bare-root evaluation is now checked from the existing degree-six carrier into ZMod q. Eisenstein→cyclotomic integral maps, ideal identification, principalization, unit/class lifting, next primitive packet and descent remain open. No facade promotion or broad build; stop after Step019.

## Step 020 — packet-free maximal kernels and unique Tail root address

- [x] Step020 COMPLETE / Outcome B: actual bare-seventh-root kernels in the existing degree-six ring, surjective evaluation, maximality/primality, integer and real-cubic contractions, and quotient cardinality q.
- [x] Tail factor zero iff its admissible root equals (c+g)/c under the c-unit premise alone; canonical Tail membership and exclusion of every distinct supplied admissible root checked.
- [x] Explicit integral witness zeta−ofReal(r.val) separates distinct kernels. Twenty-three examples include q43 K11≠K35, F in K11 but not K35, q13/q7 controls, c=g=0 failure without endpoint unit, and a supplied-old-address evaluation equality example without constructing a packet.
- [x] All12 public axiom checks, two new focused targets, both Step019 tests and Step018 regression pass.
- Evidence: [source-inventory-020.md](source-inventory-020.md), [report-020.md](report-020.md). Existing packet owners, ring definitions and historical ledger remain unchanged; no facade promotion or broad build.
- Uniqueness concerns the supplied nontrivial root kernels, not all prime ideals. Six-kernel products, source-ring embedding/ideal transfer, exact valuations, unit/class extraction, next primitive tuple and descent remain open. Stop after Step020.

## Step 021 — six explicit root slots and selective Tail support

- [x] Step021 COMPLETE / Outcome B: supplied nontrivial seventh root has order7; its positive proper powers give six genuine distinct/nonzero/nonidentity seventh roots in ascending Fin6 slots.
- [x] Existing packet-free kernels specialized to six maximal/prime ideals with integer contraction(q), cardinal q, pairwise distinctness and comaximality.
- [x] Natural Tail factor membership iff slot0, with separate first-slot membership and five-slot exclusion. No Q or Fermat premise.
- [x] Twenty-four examples check q43 roots[11,35,41,21,16,4], factor values[0,42,31,39,41,20], all six ideal receivers and selective support, q13/q7 and separate degree-two boundaries, and F(0,0) in all slots without the c-unit guard. All18 public axiom checks, two new targets and Step020/019 regressions pass.
- Evidence: [source-inventory-021.md](source-inventory-021.md), [report-021.md](report-021.md). Optional admissible-root completeness and whole-map Galois covariance deferred; no old global factorization import or facade promotion.
- Intersection=(q) and six-ideal product remain unproved here. Exact valuations, source-ring transport, class/unit extraction, primitive next tuple and descent remain open. Historical owners/ledger preserved; stop after Step021.

## Step 022 — six-coordinate interpolation and exact scalar ideal recovery

- [x] Step022 COMPLETE / Outcome B: actual signed six-coordinate basis change and both integral inverses checked over arbitrary CommRing; degree≤5 evaluation polynomial agrees with the existing actual RingHoms.
- [x] Six distinct supplied-root evaluations force all integral coordinate residues to vanish. Arbitrary-element scalar ideal membership iff coordinate divisibility checked using an actual quotient-coordinate element, hence all-six intersection=(q).
- [x] Optional product gate PASSED after the mandatory intersection build: genuine finite pairwise-IsCoprime product theorem plus Step021 comaximality proves six-ideal product=(q) in the same degree-six ring.
- [x] Twenty-four examples include signed coordinates and all six values, embedded43 and signed −43+86ζ in every kernel, F(9,4) selective membership but exclusion from intersection/scalar/product, and q13/q7 guards. All15 public axiom checks, two focused new targets and Step021/020 regressions pass.
- Evidence: [source-inventory-022.md](source-inventory-022.md), [report-022.md](report-022.md). Conditional classical splitting only; supplied nontrivial seventh root remains explicit. No facade promotion or broad build.
- The historical Step021 intersection/product gap is now closed. Exact valuations, individual-kernel principalization, integral source-ring transport, unit/class extraction, signed-depth packet construction, next primitive tuple and FLT7 descent remain open. Historical owners/ledger preserved; stop after Step022.

## Step 023 — exact source-element GTail six-factor reconstruction

- [x] Step023 COMPLETE / Outcome B: actual degree-six factors F_i=(c+g)−ζ^(i+1)c, with F0 equal to the existing linear factor. The six-factor product equals the original natural GTail 7 1 g c for arbitrary c,g, including zero gap and endpoints.
- [x] Homogeneous identity for arbitrary X,Y in the source ring follows from the actual quadratic/cubic relations via explicit polynomial certificates. No cancellation of ζ−1 or g, and no additional Domain/field import.
- [x] Optional incidence gate PASSED after the element-product build: generic q-local membership iff (i+1)(j+1)%7=1; unique receiver permutation [0,3,4,1,2,5] and its involutivity checked.
- [x] Thirty-one examples include the full36 actual residue evaluations at q43, scalar GTail=14491387 in all kernels while F0 is outside scalar(43), zero-gap product=7c^6, endpoint products1/7/0, q13/q7 guards and the false Fermat equation. All12 public axiom checks, two new focused targets and Step022/021 regressions pass.
- Evidence: [source-inventory-023.md](source-inventory-023.md), [report-023.md](report-023.md). Element product and ideal product remain separate typed statements; no facade promotion or broad build.
- Individual factor/kernel principalization, exact ideal valuations, integral Eisenstein transport, unit/class extraction, signed packet reconstruction, next primitive tuple and FLT7 descent remain open. Historical owners/ledger preserved; stop after Step023.

## Step 024 — guarded native Tail depth-one cutoff

- [x] Step024 COMPLETE / Outcome B: nonzero natural scalar multiplication is injective in the actual signed six-coordinate carrier; scalar n belongs to (q)*K_j iff q² divides n. This is scalar contraction, not equality of (q)*K_j and (q²).
- [x] Genuine finite-family excess-copy membership and explicit inverse-slot reindexing combine Step023 element reconstruction with Step022 six-kernel splitting. Selected factor square membership forces scalar GTail into (q)*assigned K.
- [x] With prime q, q∤c,g, q|GTail and the explicit q²∤GTail guard, every factor belongs to its assigned kernel and is excluded from its square. No unconditional cutoff or valuation function is introduced.
- [x] Thirty examples include q43,c9,g4 six-factor cutoffs, all wrong-slot exclusions, scalar1849 membership versus scalar43 nonmembership in (43)*K, and the valid c9,g1165 Tail case with 43² support where the new guard fails. All7 public axiom checks, new focused source/test and Step023/022 regressions pass.
- Evidence: [source-inventory-024.md](source-inventory-024.md), [report-024.md](report-024.md). The preexisting July2026 signed-packet exact valuation owner has a different typed contract; no heavy import or packet identification is added.
- Individual-factor principalization, deeper exact valuations, integral Eisenstein transport, unit/class extraction, signed packet reconstruction, primitive next tuple and FLT7 descent remain open. Historical owners/ledger preserved; stop after Step024.

## Step 025 — exact selected second-power membership

- [x] Step025 COMPLETE / Outcome B: generic maximal-ideal square saturation in a CommRing, using actual Mathlib Bézout power witnesses; no domain or principal-ideal hypothesis.
- [x] All five other factors lie outside the selected prime kernel, so the cofactor also lies outside. Its product with the selected factor is the actual scalar natural GTail.
- [x] Under the canonical Tail prime/unit/support contract, q²|GTail implies selected factor square membership. Combined with Step024, F_i∈assigned K² iff q²|GTail; the previous depth-one guard remains unchanged.
- [x] Twenty-seven examples include all six positive square memberships at q43,c9,g1165, all six negative squares at g4, wrong-slot exclusion, scalar1849 square membership, and selected cofactor residue28 in both cases. All7 public axiom checks, new source/test and Step024/023 regressions pass.
- Evidence: [source-inventory-025.md](source-inventory-025.md), [report-025.md](report-025.md). The historical Step024 positive sample's unresolved square membership is now closed by the new generic reverse theorem.
- Membership in cubes and higher powers, individual-factor principalization, signed-packet identification, integral Eisenstein transport, unit/class extraction, smaller primitive tuple and FLT7 descent remain open. No facade promotion; historical owners/ledger preserved; stop after Step025.

## Step 026 — formal shell derivative and uniform selected cofactor

- [x] Step026 COMPLETE / Outcome B: the original seven-term homogeneous GTail shell is an actual polynomial over an arbitrary CommRing; its formal derivative satisfies G+(X-Cc)G′=7X⁶.
- [x] A genuine polynomial factorization and derivative-of-product proof identify the selected actual five-factor source cofactor evaluation with G′(c+g), using the inverse receiving slot.
- [x] Under canonical Tail guards, every selected cofactor has the same value 7(c+g)⁶/g≠0. Characteristic q≠7 is proved from the nonidentity seventh root, not assumed.
- [x] Thirty-three examples verify both q43 derivative/readout values28, with all selected factors outside K² at g4 and inside K² at g1165. q7 and endpoint guards are checked. All17 public axiom checks, new source/test and Step025/024 regressions pass.
- Evidence: [source-inventory-026.md](source-inventory-026.md), [report-026.md](report-026.md). Finite-field root simplicity does not prohibit deeper source-element square membership.
- Higher ideal powers, Hensel lifting, individual-factor principalization, integral transport, unit/class extraction, signed packets and FLT7 descent remain open. Historical owners/ledger preserved; stop after Step026.

## Step 027 — native one-step Taylor correction

- [x] Step027 COMPLETE / Outcome B: original GTail shell has a checked integer first-order remainder divisible by q², including q=0 and zero endpoints.
- [x] Exact integer cancellation yields q²|T(g+q*d) iff m+d*D=0 mod q. The integer derivative is explicitly transported to the Step026 field derivative.
- [x] Under canonical Tail unit/support guards, δ=−m/D is the unique residue correction; δ.val gives a verified lift. Shifted gap unit, Tail support, ratio and derivative are preserved.
- [x] Twenty-five examples explain q43,c9,g4→g1165 via δ=27, reject d0/d26, accept d70, and feed the generic lift into all six actual ideal-square memberships. All16 public axiom checks, focused source/test and Step026/025 regressions pass.
- Evidence: [source-inventory-027.md](source-inventory-027.md), [report-027.md](report-027.md). Classical Taylor correction overlaps the existing finite PolynomialHenselDigit mechanism; the new contribution is the native GTail adapter.
- Higher ideal powers/exact valuations, q-adic completion, signed packets, principalization, integral transport, unit/class extraction and FLT7 descent remain open. Historical owners/ledger preserved; stop after Step027.

## Step 028 — native second digit via existing finite polynomial API

- [x] Step028 COMPLETE / Outcome B: checked native evaluation and integer derivative guard adapters specialize the existing PolynomialHenselDigit theorem at k=2 to ∃! t:Fin q, q³|GTail(g+q²*t.val).
- [x] Optional q³ linear iff uses the existing integer criterion with a genuine integer/natural quotient cast. No second generic Hensel proof or separate digit framework is introduced.
- [x] Twenty-eight examples verify the second residue17, g1165→g32598, generic q³ support, uniqueness/exclusion in Fin43, natural correction60, ratio11/derivative28 and all six bounded K² memberships. Scalar43⁴ nondivisibility is checked separately.
- [x] All10 public axiom checks, focused source/test and Step027/026 regressions pass. Reusing the neutral owner adds two local modules relative to Step027; no additional Mathlib closure modules.
- Evidence: [source-inventory-028.md](source-inventory-028.md), [report-028.md](report-028.md). The new result is a native adapter to existing finite-depth machinery; scalar depth3 does not establish any K³ statement.
- All-k ideal valuations, q-adic completion, integral transport, signed packets, principalization, unit/class lifting and FLT7 descent remain open. Historical owners/ledger preserved; stop after Step028.

## Step 029 — actual selected third-power membership

- [x] Step029 COMPLETE / Outcome B: erased five-kernel complement splitting/comaximality gives K²∩(q)=(q)K and K³∩(q)=(q)K² in the actual degree-six carrier.
- [x] Natural scalar square/cube contractions use existing integral-coordinate scalar injectivity, without a DVR/domain hypothesis. Actual cofactor saturation proves F_i∈assigned K³ iff q³|GTail under canonical Tail guards.
- [x] Twenty-five examples include all six K³ memberships at g32598, exclusions at g4/g1165, all wrong-slot exclusions, scalar43³ cube membership versus scalar43² exclusion, residue28 and digit17 consistency.
- [x] All9 public axiom checks, focused source/test and Step028/027 regressions pass. Import closure adds only the new local owner; earlier sources and historical records are preserved.
- Evidence: [source-inventory-029.md](source-inventory-029.md), [report-029.md](report-029.md). Scalar43⁴ nondivisibility does not establish selected K⁴ exclusion or exact K-adic depth3.
- Higher selected powers/valuations, integral transport, signed packets, principalization, unit/class extraction and FLT7 descent remain open. Stop after Step029.

## Step 030 — fourth-power firewall and bounded exact third depth

- [x] Step030 COMPLETE / Outcome B: K⁴∩(q)=(q)K³ and natural scalar K⁴ contraction are checked in the actual signed-coordinate degree-six carrier, without a domain/DVR premise.
- [x] Actual cofactor maximal-power saturation proves F_i∈assigned K⁴ iff q⁴|GTail. Together with Step029, a bounded K³ membership/K⁴ exclusion corollary is public.
- [x] Thirty-eight examples verify all six exact bounded third-depth cutoffs at g32598, fourth exclusions at g4/g1165, scalar43⁴ membership versus scalar43³ exclusion, and unchanged ratio11/derivative28/cofactor28.
- [x] All4 public axiom checks, focused source/test and Step029/028 regressions pass. Historical owners and checkpoint records are preserved.
- Evidence: [source-inventory-030.md](source-inventory-030.md), [report-030.md](report-030.md). The previous Step029 K⁴ exclusion gap is now closed for the guarded actual factors.
- Stop after Step030. Recommend a separate source-typed frontier reassessment of Eisenstein Q²/focused GTail readouts versus degree-six prime-root addresses. No K⁵ hierarchy, assumed integral ring map, signed packet, class/unit extraction or FLT7 descent is introduced.

## Step 031 — conditional norm-scalar / ideal-depth synchronization

- [x] Step031 COMPLETE / Outcome B: explicit abstract doubled-valuation budget gives square/fourth scalar readouts and no scalar exact depth3; satisfiable and failed-gap-unit controls are checked first.
- [x] Full positive primitive hypothetical Fermat7 input derives all coordinate/endpoint/gap units, q≠3 and nonzero values; Step010 budget and square allocation are reused.
- [x] Separate typed Eisenstein α² split-address and actual cyclotomic K²/K³↔K⁴ endpoints share only scalar q,Q,T. Optional q⁴|T iff integer q²|normα is checked.
- [x] Twenty-six examples include universal full-contract tests, q43 mixed carriers with false Fermat/balance premises, g32598 outside hsum, gap-unit and zero-value failures, and characteristic boundaries.
- [x] All7 public axiom checks, focused final source/test and Step030/010/012/017 regressions pass. Local cycle0 and all27 reachable neutral Lib owners have FLT reachability0; historical owners/records remain unchanged.
- Evidence: [source-inventory-031.md](source-inventory-031.md), [report-031.md](report-031.md). Even-depth compatibility is a direct application of the preexisting Step010 budget, not an independent FLT7 obstruction/descent.
- Stop after Step031. Integral E→R transport, ideal equality, signed packet reconstruction, K⁵/all-k, unit/class extraction and unconditional FLT7 closure remain outside this checkpoint.

## Step 032 — exact global balance and local-compatibility firewall

- [x] Step032 COMPLETE / Outcome B: under additive focus alone, exact NAT GTail balance and typed INT norm balance are each equivalent to Fermat7Equation.
- [x] Positive primitive (1166,1857,1858,1165) satisfies strict geometry, focus, all q43 units, exact Q depth1/T depth2 and the doubled budget, but fails Fermat7Equation and both exact balances.
- [x] Thirty-eight examples include actual E square address, all6 R square memberships/cube exclusions, wrong-slot exclusions, universal iff signatures and historical characteristic/zero controls.
- [x] Lean corrects the instruction's old-focus claim: (5,8,9,4) already satisfies focus and strict geometry; the new witness adds the missing q43 budget and K² depth. The new witness fails the separate known 7|g condition, so sufficiency findings are limited to the listed q43 contract.
- [x] Both public axiom checks, final source/test and Step031/030/GTailBridge regressions pass. Local cycle0, all27 reachable neutral Lib owners have FLT reachability0; historical owners/checkpoints are preserved.
- Evidence: [source-inventory-032.md](source-inventory-032.md), [report-032.md](report-032.md), [frontier-032.md](frontier-032.md). Old descent provider requires next primitive pack, route and actual carrier_match; local values do not construct these fields.
- Stop after Step032. Exact balance reformulation is a circularity/information firewall, not a new FLT7 descent. No integral E→R map, signed packet, K⁵/all-k or unit/class extraction is introduced.

## Step 033 — no direct unital Eisenstein/cyclotomic RingHom

- [x] Step033 COMPLETE / Outcome B: no unital E→+*R using the actual R→ZMod29 evaluation and quadratic no-root; no unital R→+*E using actual E→ZMod13 evaluation and complete seventh-cyclotomic no-root.
- [x] Both proofs use the actual integral τ/ζ relations and preserve map_one. They require no Fermat equation, Tail tuple, prime-support budget or signed packet.
- [x] Twenty-four examples verify finite root lists, actual evaluations and generator images, both no-hom signatures, q43 separate common-codomain maps, −3/−7 parameter distinction and ramified/Gap contrasts.
- [x] All6 public axiom checks, final source/test and Step032/031 regressions pass. Local cycle0, all27 reachable neutral Lib owners have FLT reachability0. One intermediate letI style warning was corrected without overriding options.
- Evidence: [source-inventory-033.md](source-inventory-033.md), [report-033.md](report-033.md), [frontier-033.md](frontier-033.md). The previously missing direct-map contract is now proved impossible for these exact orders; richer common-target bridges are not ruled out.
- Stop after Step033. No compositum/tensor/21st-cyclotomic order, ideal-class theory, signed packet, provider reconstruction or FLT7 descent is introduced. Historical Step032 focus correction remains preserved.

## Step 034 — actual common quadratic receiver and q43 contractions

- [x] Step034 COMPLETE / Outcome B: C=QuadraticAlgebra R (-1)1 receives actual unital E→C and R→C maps, with both injections checked by coordinate proofs.
- [x] The q43 common evaluation has actual commuting triangles to the old root37/root11 RingHoms; both generator images and shared integer residues are checked.
- [x] Its maximal/prime kernel contracts to P37 in E and seventhRootKernel11 / slot0 in R. These are separately typed contractions, not equality of ideals across rings or extended powers.
- [x] Thirty-seven examples include the same actual α/F0 q43 witness, source square support, common residue zeros and kernel membership; an extra proof shows their two C-images are different.
- [x] All23 public declaration axiom checks, final source/test and Step033/032 regressions pass. Local cycle0 and all27 reachable neutral Lib owners have FLT reachability0. Nested-ext and a test-coordinate sign were repaired locally; final warnings0.
- Evidence: [source-inventory-034.md](source-inventory-034.md), [report-034.md](report-034.md), [frontier-034.md](frontier-034.md). Step033 no-direct-map results and historical Step032 correction remain preserved.
- Stop after Step034. No field/domain/compositum/rank12/flatness/tensor-isomorphism claim, equal extended ideals, all-k depth, signed packet, next primitive tuple or FLT7 descent is introduced.
