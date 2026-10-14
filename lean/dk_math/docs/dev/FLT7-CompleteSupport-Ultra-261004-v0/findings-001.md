# FLT7 Complete-Support Ultra — Findings 001

Branch: **research/FLT7-CompleteSupport-Ultra-261004-v0**

Base: **develop** at **82dd73bed85ff6c75fa1a8318ebafb08e7faab21**

This file is the durable, incremental research log. It must be updated during
the run; do not reserve findings for the final report.

## Current status

- Requested branch verified; initial baseline `cf7df8206`, Lean/Mathlib `v4.34.1`.
- **Raw target obstructed**: the actual current carrier has ramified exponent 1,
  so all-support seventh-divisibility is false under the current packet inputs.
- **Corrected global route checked**: after extracting one actual uniformizer,
  all six normalized phase ideals are seventh powers. The raw current ideal
  is `P7 * J^7`, and the actual element is `lambda * u * beta^7` with unit
  retained and the original Fermat equation preserved.
- Checkpoint complete. Full library build passed (10350 jobs); full test facade
  passed (10942 jobs). Focused regressions, all endpoint axiom checks, and
  final tracked/new-file whitespace checks passed. Final report saved.

## Confirmed facts

- DRC-008 selected current oriented prime has exact exponent `14e`; the raw
  finite support retained all complementary primes.
- The actual raw carrier has ramified height-one exponent 1. That prime is in
  the complement and differs from the selected kernel and its conjugate.
- Every other raw height-one exponent is divisible by 7, without an address
  coverage hypothesis. The literal raw all-support target is formally false
  under the current packet inputs.
- Exact element division `A_j=lambda*B_j` is checked for all six phases. The
  normalized phase ideals are pairwise coprime and their full product is a
  seventh power, hence each normalized complete support has 7-divisible exponents.
- Corrected current receiver: `(A)=P7*J^7`, `A=lambda*u*beta^7`, `IsUnit u`,
  and the original `Fermat7Equation x y z`. No additional exponent/class-group
  hypothesis is used. No successor coordinates or strict descent are asserted.
- All 36 public production endpoints and the three imported neutral endpoints
  have only standard axiom dependencies. Focused regressions and FLT facades pass.

## Candidate bridges

- Current six-factor element product / Dedekind coprime extraction route:
  **implemented and proved**, see checkpoints 06–08. No new residue-address
  enumeration is necessary.
- Follow-up unit gauge: divide normalized phase j by the known cyclotomic
  geometric-sum unit, prove the new quotient's scalar congruence and relative
  norm/projective-log criterion. Candidate `F_j=(1-zeta^j)*gamma^7` is unproved.
- Existing small twisted-state norm needs additive landing into a positive
  primitive natural `CounterexamplePack`; this bridge remains unproved.

## Failed / blocked routes

- Raw all-support seventh-divisibility fails at actual ramified exponent 1;
  the obstruction is now formal, not a conjectured missing enumeration.
- Universal current-address coverage excludes ramified support (`q=7`);
  arbitrary nonramified residue fields also require degree-one control to
  become maps into `ZMod q`. Full-factor aggregation bypasses this route.
- Applying the summit chosen-unit theorem directly to the new normalized
  current quotient lacks the required checked carrier equality.
- Checkpoint commit was rejected by automatic approval review as prohibited
  for the authorized task. Files and logs were saved; no workaround or commit.

## Open obligations

- Identify the new normalized quotient's unit class with the phase gauge kept
  explicit; source-specific congruence/relative-norm arguments remain to connect.
- Reconstruct positive primitive successor coordinates with their additive
  Fermat identity and strict decrease. Neither unit-times-power nor smaller
  twisted-state norm suffices.
- Support classification is settled in the ramified formulation; final report
  and validation log index are complete.

## Next action

- This support checkpoint is complete; retain the files/logs as the recovery
  record. A future unit checkpoint should first prove the new quotient's phase
  gauge/scalar congruence and relative-norm unit criterion.
- Additive landing and a smaller positive natural successor are separate later
  obligations; neither is claimed by the current receiver.

## Checkpoint history

- 2026-10-04: workspace initialized from current `develop`.

### 2026-10-04 checkpoint 01 — Initial diagnosis

- Complementary support includes every height-one prime other than the one
  chosen oriented current kernel, potentially primes over 7, other primes over
  the selected rational prime, and primes over other rational primes. The
  factorization definitions retain all of them; actual occurrence remains to test.
- Constraints: current exact selected cutoff (`CurrentCarrierCutoff`), full
  finite factorization (`CurrentFiniteAggregation`), six-factor product and
  real axis-cube-times-seventh-power identity, and existing degree-six PID.
- Most promising first route is the ramified-prime calculation. A residue
  address has a nontrivial order-seven unit in `ZMod q`, which excludes `q=7`;
  therefore such addresses cannot by themselves cover ramified support.
- DRC-004..007 impact not established: inspect their actual typed carriers first.
- Exact first intended theorem: current carrier has ramified ideal exponent 1
  (if the current packet hypotheses supply the required axis-free first jet).
  This would yield Outcome C with a formal obstruction, not prove FLT7 false.
- Historical R64 freeze was used only as orientation; DRC-008 sources are the
  current verified baseline and this new branch explicitly authorizes research.

### 2026-10-04 checkpoint 02 — Concrete ramification and coprimality APIs

- **Verified source**: `SevenRamifiedFusionCyclotomicRamifiedPrime` defines
  `ramifiedUniformizer = 1-zeta`, `ramifiedEval : Ring →+* ZMod 7`, and
  `ramifiedPrime = ker ramifiedEval`. It proves maximality, the span identity,
  `ofReal_eisensteinAxis_eq = zetaInv * ramifiedUniformizer^2`, and
  `ofReal_seven_eq_uniformizer_pow_six_mul_unit`. The axis identity has a
  **positive** unit coefficient `zetaInv`, verified in the current source.
- Its later signed-depth historical carrier theorems are not identity bridges
  into current A. Only the neutral ring/ideal identities are being reused.
- **Verified source**: `PrimeTraceOneDirectRealCubicOrbitSplit` proves
  `directOrbit_roots_isCoprime p`, `directOrbit_gap_axis_pow32_dvd p`, and
  `directOrbit_quotient_exactDepth_three p`. Thus away-seven coprimality of the
  two current real roots is available; it need not be postulated.
- The phase exponent is one of `1,4,5`; geometric phase sums have residue this
  exponent. Candidate direct proof: write current A as real gap plus
  `(1-zeta^a)*ofReal rho`, divide once by the actual uniformizer, and evaluate
  the quotient to `(a : ZMod 7) * thetaResidue rho ≠ 0`.
- **Candidate new route after obstruction**: strip exactly one uniformizer and
  use the six-factor product plus away-seven pairwise coprimality to obtain a
  corrected normalized-carrier seventh-power statement. This is not yet proved.
- DRC preliminary audit: 004 requires powers in augmentation and Φ7 components;
  005 allows arbitrary exact positive shell depths; 006 classifies supplied
  quadratic residue fibres; 007 has a quadratic Gauss half-product carrier.
  None currently identifies this fixed linear carrier or eliminates P7.
- Next: focused current ramified proof (agent scratch), while auditing the
  normalized away-seven product route. No broad build or refactor yet.

### 2026-10-04 checkpoint 03 — Structural route and DRC boundary audit

- **Verified source**: `CurrentCommonPrimeResiduePacket.q_ne_seven` excludes
  rational 7 from the selected current row. The ramified prime therefore belongs
  to complementary support if the candidate membership proof succeeds.
- **Verified source**: `PrimeTraceOneDirectCyclotomicRootPhaseNormalization`
  has neutral `firstOrderPhaseSum`, `ramifiedEval_firstOrderPhaseSum`, and
  `uniformizer_mul_mem_ramifiedPrime_sq_iff`. These prove first-order statements
  for the same explicit ring; no historical carrier equality is required.
- **Verified source via audit**: `FLT.Kummer.CyclotomicPrincipalization` has
  `linearFactorDiffSpanEqSubOneSpan` (primitive-root differences generate the
  same ideal as `(zeta-1)*base`) and
  `dedekindIdealEqPowOfProdEqPowOfPairwise` (coprime nonzero ideal factors of a
  full ideal power are powers). The specific endpoints require axiom audit;
  unrelated incomplete declarations in that file do not establish dependence.
- **Candidate stronger formulation**: normalized current factors `B_j` satisfy
  `F_j = lambda * B_j` for `j=1..6`, are pairwise coprime, and their ideal
  product equals a fourteenth power. Then each `B_j` has a fourteenth (hence
  seventh) ideal-power receiver. Raw `F_j` still has ramified exponent one.
- DRC-004 exact mismatch: `PrimeCyclicGlue.aks_prime_cyclic_is_pow_of_components`
  is in `AKSCyclicQuotient Z p` / `AdjoinRoot Phi_p`; its inputs are actual
  element powers without unit multipliers. It supplies neither a current-QA
  identification nor unit elimination.
- DRC-005 `PrimeShellHensel.exists_primeShell_exact_depth` allows every positive
  exact shell depth under simple nonramified seeds; residues do not force
  seventh valuation. Its nonramified hypotheses exclude the ramified case.
- DRC-006 `QuadraticResidueType` classifies roots for supplied base residues.
  In the current QA it can describe the ratio/inverse fibre, but does not
  construct an address for an arbitrary height-one prime.
- DRC-007 `CyclotomicQRProvenanceLift` embeds the QR half-product into the
  quadratic Gauss subfield (at p=7, a product of three linear factors).
  That element is not this single current linear factor of `rho`. Neither
  its element map nor its relative norm identifies the current carrier.
- Initial audit log saved to `logs/audit-001.log`. Next implementation is local:
  new ramified/obstruction modules and, if successful, a normalized-factor
  module; no stable current code is being refactored.

### 2026-10-04 checkpoint 04 — Ramified candidate succeeds in Lean

- **Kernel-checked scratch**: `/tmp/current-ramified-obstruction.lean` proves
  `current_carrier_mem_ramified` and `current_carrier_not_mem_ramified_sq`
  for the actual `currentLinearCarrier c`. The proof uses current gap axis
  divisibility, `p.thetaResidue_ne_zero`, and the phase exponent `1,4,5`.
- This determines the ramified exponent as 1 through the already checked
  generic `principal_exponent_eq`. Therefore the raw all-support seventh
  divisibility target has a concrete obstruction, rather than merely lacking
  an enumeration theorem. The raw conditional receiver's hypothesis cannot hold
  for these current packets. This does not construct or refute existence of
  FLT counterexamples by itself.
- New local implementation begun after recorded diagnosis:
  `CurrentCarrierRamifiedObstruction` (first jet and exact λ division),
  `CurrentSupportObstruction` (full-support witness/negated target), and
  optional `CurrentCarrierNormalizedPower` (corrected extraction).
- **Kernel-checked scratch**: `/tmp/FLT7DRCBridgeAudit.lean` shows degree-seven
  shell base 1, gap 15 has a nontrivial seventh root residue modulo 29 but exact
  29-depth 1; simple Hensel seeds allow every positive depth. It also proves
  `CurrentMuSevenResidueAddress q` implies `q≠7` directly by Frobenius.
- Checkpoint commit was attempted per the document protocol but automatic
  approval review rejected it, stating the authorized task prohibits commits.
  No commit occurred. Durable checkpoints remain saved files; no workaround.
- Next: formal complete-support obstruction and current normalized six-factor
  power receiver, with focused builds and axiom logs saved in this directory.

### 2026-10-04 checkpoint 05 — Production ramification module checked

- `CurrentCarrierRamifiedObstruction.lean` focused build passed (9188 jobs),
  logged in `logs/current-ramified-focused.log`.
- Canonical namespace: `SevenRealCubic.CurrentCarrierRamification`.
  New exact element transport: `phaseCarrier_eq_uniformizer_mul_quotient p j`.
  Explicit normalized element: `phaseCarrierQuotient p j`, residue
  `(j : ZMod 7) * thetaResidue p.rho`. For `¬7∣j`, the quotient is outside P7.
- Current specialization directly unfolds `currentLinearCarrier`; all natural
  nonzero-mod-seven phases are covered, not only the selected phase `1,4,5`.
- Parent support formalization uses the existing `principal_exponent_eq` and
  `carrier_local_exponent`; no new factor-count theory is required. First build
  exposed only local elaboration issues (explicit ideal argument to the span
  membership iff, and reducing the height-one-place definition), now repaired.
- Corrected normalized product route is still under focused verification.
- Next: finalize raw support theorem and its axiom audit; keep all provenance
  assumptions visible and do not label the obstruction a proof of FLT7.

### 2026-10-04 checkpoint 06 — Full corrected aggregation succeeds

- **Kernel-checked production**: `CurrentSupportObstruction` builds (9189 jobs).
  `ramifiedPlace_mem_support`, `ramifiedPlace_exponent` (=1), and
  `ramifiedPlace_in_complement` locate the obstruction in the actual full finite
  support, distinct from the selected current kernel and its conjugate.
  `not_completeSupport_seventh_divisibility` formally negates the raw target;
  `currentCarrier_not_unit_mul_seventh_power` shows a unit alone cannot remove it.
- **Kernel-checked production**: `CurrentCarrierNormalizedPower` builds (9189
  jobs). It uses all six current phase factors, not six scalar norm matches.
  The polynomial cyclotomic factorization gives the actual product;
  `directOrbit_roots_isCoprime` plus the root-difference span equality forces
  any common prime to be P7. Each normalized quotient avoids P7, hence the
  six normalized principal ideals are pairwise coprime.
- The normalized element product is `unit * ofReal(S)^14`; its ideal product
  is a seventh power. The existing neutral Dedekind coprime-product receiver
  yields each normalized ideal as a seventh power.
- Exact current global endpoints:
  `currentCarrier_ramifiedIdeal_mul_seventh_power c : carrierIdeal c = P7 * J^7`
  and `currentCarrier_ramified_element_receiver c : A = lambda*u*beta^7`
  with `IsUnit u` and original `Fermat7Equation x y z`. No `hdiv` assumption.
- This is Outcome C for the literal raw-support target, with a proved corrected
  extraction route. It does not remove the unit, build new additive coordinates,
  produce a smaller positive counterexample, or prove unconditional FLT7.
- **Prime-below audit**: `Nat.absNorm_under_prime` applies after transferring
  integral/finiteness structures from the existing ring-of-integers equivalence.
  An arbitrary residue field may be an extension of `ZMod q`; order 7 gives
  `7 | q^f-1`, not a `ZMod q` address without residue-degree-one control.
  Full six-factor aggregation bypasses this missing address classification.
- DRC audit and its formal shell/address regressions are durable in
  `drc-bridge-audit-001.md`, `CompleteSupportDRCBridgeAudit.lean`, and
  `logs/drc-bridge-focused.log` (9186 jobs). All six audit dependency lists
  contain standard axioms only.
- Next: expose all nonramified exponents as seventh multiples, build regression
  and axiom facade checks, then checkpoint before full builds.

### 2026-10-04 checkpoint 07 — Complete raw exponent classification and review

- **Kernel-checked production**: `away_ramified_exponent_seventh_dvd` now
  controls every height-one prime except P7. Together with exponentP7=1,
  complementary support is fully controlled in the ramified formulation.
- `normalized_completeSupport_seventh_divisibility` is also exposed, proving
  the exact finite-support hypothesis for the explicitly divided current ideal.
- Independent source review found no hidden arithmetic hypotheses or historical
  carrier identification. All six phases are covered exactly once.
- First regression build exposed only a height-one structure extensionality
  elaboration issue; repaired using the existing `HeightOneSpectrum.ext`.
  Final regressions cover all6phases, raw exponent classification, both raw
  obstruction and repaired receiver for the same c, and finite normalized root.
- Unit frontier audit saved `unit-frontier-audit-001.md`: summit original unit
  theorem is carrier-specific, not directly usable on new quotient. Generic CM
  facts apply to arbitrary units, but the new scalar/relative-norm gauge still
  needs its own proof. The phase geometric-sum unit must remain visible.
- Candidate next unit formula `F_j=(1-zeta^j)*gamma^7` is explicitly unproved.
  A smaller twisted-state norm is not a reconstructed positive Fermat packet.
- `report-001.md` now records Outcome C for raw target and the checked corrected
  global endpoint. Next: final focused regressions/axiom checks, then checkpoint
  to disk before full library/test builds.

### 2026-10-04 checkpoint 08 — Stable endpoint before full builds

- Final combined focused regression and public facade command passed (9334 jobs):
  `lake build DkMathTest.FLT.CurrentCompleteSupport
  DkMathTest.FLT.CompleteSupportDRCBridgeAudit DkMath.FLT.Seven DkMath.FLT.Prime`.
  Log: `logs/current-regression-facades-final.log`.
- All 36 new public production endpoints (31 theorems and 5 definitions) audited;
  dependencies only `propext`, `Classical.choice`, `Quot.sound` (or subsets).
  Three imported neutral power/coprimality endpoints also print only those
  standard axioms despite unrelated incomplete declarations in their module.
- Regression checks all6phases, actual ramified exponent1/complement, every
  other rawprime seventhdivisibility, normalizedfullsupport root, λ*u*β7 with
  original sourceEq, and DRC finite-residue/Hensel boundaries.
- Outcome stable: raw target formally obstructed; corrected normalized support
  and global ramified ideal/element factorization proved without hdiv.
- Full build/test facade checks start only after saving this checkpoint.

### 2026-10-04 checkpoint 09 — Library full build passed, before full test build

- Full `lake build` passed (10350 jobs), exit 0. Log `logs/full-build.log`.
- New source/test forbidden-construct scans and tracked/new-file whitespace
  checks passed. Existing unrelated research placeholders in the larger import
  graph are absent from all newly audited endpoint dependencies.
- Current-status summary and open obligations updated to the proved endpoint.
- Next full command `lake build DkMathTest` starts after this saved checkpoint;
  final report/log summary will record its actual result.

### 2026-10-04 checkpoint 10 — Final closeout

- Full `lake build DkMathTest` passed (10942 jobs), exit 0; log
  `logs/full-test-build.log`. No unresolved compiler/test failures remain.
- `report-001.md` and `logs/validation-summary.md` finalized with actual build
  results, 36 public production endpoint audits, imported neutral endpoint and
  DRC calibration audits, semantic boundary, and remaining unit/descent duties.
- Final Outcome C for the literal raw goal: actual complementary ramified
  support exponent1 forbids it. Corrected normalized complete support and
  raw `(A)=P7*J^7`, `A=lambda*u*beta^7` are proved without exponent assumptions.
- New source/test scans and final tracked/new-file whitespace checks clean.
  No unconditional FLT7, successor additive landing, or strict descent claimed.
- Optional git checkpoint commit remained rejected by automatic approval review;
  initial HEAD is unchanged. All requested durable recovery files are saved.
