# Step043 — final release validation and PR handoff

Date: 2026-10-12. **Ready: true / Blocked: false** (local release acceptance).
Research classification: **Outcome B / STOP042**. No new proof-development target.

## Performed work and scope

Read instruction-043, inspected the actual checkout, fetched origin, checked imports,
compiled all five required public entrances sequentially, directly verified all 49
added test modules, rebuilt the two corrected old terminal source targets, ran the
complete default test library, and refreshed the release-facing narrative.
No source, theorem, example, import, namespace or driver repair was necessary.
No new mathematical implementation or exploratory example was added.

Validated HEAD: `caebaf0ec98c12e1e570b6e2e9aefb2aa2362f7e`.
Branch: `feature/GTail-SelectiveGap-FLT7-261009-v0`; base: `develop`.
Lean: 4.34.1. Lake cwd: `/home/deskuma/develop/lean/dkmath/lean/dk_math`.
Initial status: user-staged `instruction-043.md` only; its staged bytes are preserved.
During work, README header metadata/Markdown breaks were concurrently updated and
staged; those bytes were retained. Final staged paths are README and instruction-043.
The instruction staged blob remains `42e6dedbb9a8daecf58cad2a4caf7a274d7daf16`.
Step043 changes: this report and source-inventory-043 (new), PR-CLOSEOUT/PR-DRAFT/README
(updated), ROADMAP (append-only). All historical reports/reviews and Lean files remain
unchanged. The two new facade/smoke files were already committed at the checked HEAD.

The HEAD comparison has 287 files (283A/4M): 48 added production Lean files,
49 added tests, 186 added documents, four modified existing files. See the complete
[source inventory](source-inventory-043.md) for 30 specialized-owner and 17 neutral-owner
coverage matrices, facade entries, changed files and all added document names.
Release working changes add two documents; the prospective comparison is 289 files.

## Executed build/test evidence

All commands used process-local `LEAN_NUM_THREADS=2`; no global settings, resource
limit changes, full clean or proof shortcuts. Builds ran sequentially. Test batches
contain explicit target arguments; production owners compile via these imports and
the scoped facade. Logs and machine-readable audit data are local ignored artifacts
under `.lake/build/gtail-step043/`, not a committed evidence archive.

| Log / target group | Exit | Seconds | Warnings | Built / Replayed event lines | Final job denominator |
| --- | ---: | ---: | ---: | ---: | ---: |
| 01 Dedicated facade | 0 | 9.21 | 0 | 0/180 | 9105 |
| 02 New research smoke | 0 | 16.43 | 0 | 1/180 | 9106 |
| 03 Neutral Lib | 0 | 8.61 | 0 | 0/31 | 8957 |
| 04 Old Lib smoke | 0 | 8.22 | 0 | 0/32 | 8958 |
| 05 Old broad FLT smoke | 0 | 8.22 | 4 | 0/361 | 9296 |
| 06 10 latest research tests + 2 corrected terminal sources | 0 | 8.49 | 0 | 0/184 | 9109 |
| 07 36 remaining owner tests | 0 | 7.88 | 0 | 0/213 | 9138 |
| 08 Full default test library | 0 | 9.75 | 5 | 0/2197 | 11284 |

`01`–`07` logs are `NN-build.log`; the full suite log is `08-test.log`.
All commands exited0 with errors0. The new smoke was actually Built in 7.3 s;
its command total was 16.43 s. Other explicit targets were Replayed. Lake counts
include cached dependency jobs, so they are not counts of newly compiled modules.
The full default run completed in 9.75 s within the configured 180 s
bound; it was not stopped. It reached 11284/11284, emitted 2197 replay events,
and discovered all 49 added tests including the new scoped smoke. The existing
`DkMathTest.+` glob works without any root-driver import edit. No memory failure was
observed; peak memory was not measured. These are cached local validations, not a
clean rebuild or a CI result.

Exact invocations (from `lean/dk_math`):

```sh
LEAN_NUM_THREADS=2 lake build DkMath.FLT.Seven.GTail
LEAN_NUM_THREADS=2 lake build DkMathTest.FLT.Seven.GTailResearchFacade
LEAN_NUM_THREADS=2 lake build DkMath.Lib
LEAN_NUM_THREADS=2 lake build DkMathTest.CosmicFormula.GTailLibFacade
LEAN_NUM_THREADS=2 lake build DkMathTest.FLT.Seven.GTailFacade
LEAN_NUM_THREADS=2 lake build DkMathTest.FLT.Seven.GTailFocusedCapacityIndependence DkMathTest.FLT.Seven.GTailFocusedDefectGlobalCapacity DkMathTest.FLT.Seven.GTailFocusedDefectSquareFirewall DkMathTest.FLT.Seven.GTailFocusedPrimeRoute DkMathTest.FLT.Seven.GTailFocusedGenericPrimeReceiver DkMathTest.FLT.Seven.GTailEisensteinCyclotomicPrimeJoin DkMathTest.FLT.Seven.GTailEisensteinCyclotomicPrimeGrid DkMathTest.FLT.Seven.GTailEisensteinCyclotomicCommonReceiver DkMathTest.FLT.Seven.GTailEisensteinCyclotomicNoDirectHom DkMathTest.FLT.Seven.GTailGlobalBalanceFirewall DkMath.FLT.Seven.SevenBaseTerminalRowZSignedResidualCore DkMath.FLT.Seven.SevenBaseTerminalRamifiedSummit
LEAN_NUM_THREADS=2 lake build DkMathTest.CosmicFormula.GTailFactor DkMathTest.CosmicFormula.GTailSelection DkMathTest.CosmicFormula.GTailSeven DkMathTest.CosmicFormula.GTailSevenPrimeAllocation DkMathTest.CosmicFormula.GTailSevenValuation DkMathTest.CosmicFormula.GTailTransport DkMathTest.FLT.Seven.GTailBridge DkMathTest.FLT.Seven.GTailConstraintAudit DkMathTest.FLT.Seven.GTailCyclotomicLocalEval DkMathTest.FLT.Seven.GTailCyclotomicPrimeAddress DkMathTest.FLT.Seven.GTailCyclotomicSixRootInterpolation DkMathTest.FLT.Seven.GTailCyclotomicSixRootOrbit DkMathTest.FLT.Seven.GTailCyclotomicTailDepthFour DkMathTest.FLT.Seven.GTailCyclotomicTailDepthOne DkMathTest.FLT.Seven.GTailCyclotomicTailDepthThree DkMathTest.FLT.Seven.GTailCyclotomicTailDepthTwo DkMathTest.FLT.Seven.GTailCyclotomicTailDerivative DkMathTest.FLT.Seven.GTailCyclotomicTailFactorProduct DkMathTest.FLT.Seven.GTailCyclotomicTailSecondDigit DkMathTest.FLT.Seven.GTailCyclotomicTailTaylorLift DkMathTest.FLT.Seven.GTailFocusedNormCyclotomicDepthBridge DkMathTest.FLT.Seven.GTailNormReadoutAudit DkMathTest.FLT.Seven.GTailPrimeAllocationAudit DkMathTest.FLT.Seven.GTailPrimeOrderAudit DkMathTest.FLT.Seven.GTailSevenUnitAudit DkMathTest.FLT.Seven.GTailValuationAudit DkMathTest.NumberTheory.GTailSevenEisensteinResidue DkMathTest.NumberTheory.GTailSevenIdealSquareAddress DkMathTest.NumberTheory.GTailSevenNormReadout DkMathTest.NumberTheory.GTailSevenPairedResidue DkMathTest.NumberTheory.GTailSevenPrimeOrder DkMathTest.NumberTheory.GTailSevenRamifiedThreeIdeal DkMathTest.NumberTheory.GTailSevenRealTraceResidue DkMathTest.NumberTheory.GTailSevenResidueIdeal DkMathTest.NumberTheory.GTailSevenSplitIdeal DkMathTest.NumberTheory.SevenUnitAllocation
LEAN_NUM_THREADS=2 lake test
```

### Existing warnings retained outside the added source matrix

The old broad facade emitted four warnings; the full suite emitted the same four
plus TriominoFLT. These are preexisting dependencies, not new GTail placeholders:

```text
warning: DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:147:6: declaration uses `sorry`
warning: DkMath/FLT/PrimeProvider/TriominoCosmicBranchA.lean:4187:8: declaration uses `sorry`
warning: DkMath/NumberTheory/GcdNextResearch.lean:850:6: declaration uses `sorry`
warning: DkMath/FLT/Kummer/CyclotomicPrincipalization.lean:5389:8: declaration uses `sorry`
warning: DkMath/CosmicFormula/TriominoFLT.lean:1919:6: declaration uses `sorry`
```

Dedicated facade, new smoke, Lib, Lib smoke and both owner-test batches had warnings0.
The complete repository is not claimed to be `sorry`-free. The 97 added Lean files
(48 production + 49 tests) passed the executable-code scan for `sorry`, `admit`,
`axiom`, `unsafe`, `native_decide` and resource-limit option hacks.

## Axiom, dependency and release-text audits

The five public smoke outputs are:

- `DkMath.FLT.Seven.fermat7Equation_iff_focused_scalar_balance` → `propext, Classical.choice, Quot.sound`.
- `DkMath.FLT.Seven.GTailPrimeJoin.M_eq_map_eisenstein_sup_map_cyclotomic` → `propext, Classical.choice, Quot.sound`.
- `DkMath.FLT.Seven.GTailFocusedDefectSquareFirewall.defect_square_prime_route` → `propext, Classical.choice, Quot.sound`.
- `DkMath.FLT.Seven.GTailFocusedDefectGlobalCapacity.full_quadratic_defect_zero_certificate` → `propext, Classical.choice, Quot.sound`.
- `DkMath.FLT.Seven.GTailFocusedCapacityIndependence.exists_full_support_without_size` → `propext, Classical.choice, Quot.sound`.

Across the focused logs, 288 distinct selected public GTail/selection-related
declarations had collected axiom outputs. All collected focused outputs use only
ordinary `propext`, `Classical.choice`, `Quot.sound`; no nonstandard axiom was
introduced. The full repository's unrelated old placeholder dependencies are
outside this selected-API guarantee. The full list is appended below.

The source-level closure audit confirms exact 30-import coverage, all 17 neutral
owners, zero neutral→FLT reachability, no historical broad-facade dependency in the
scoped entrance, and a cycle-free 473-vertex local import DAG. Closures are scoped
8962 names/182 local modules, Lib8814/34, broad9152/372. These counts are source
reachability, not clean import timings. Lib exposes only its original five added
neutral owners; later neutral APIs keep direct imports. Existing MIT headers and
module-name `#print` conventions are retained. Markdown links and whitespace were also checked against the final working files.
All 207 local links across six release documents resolve. All 97 added Lean files
retain the MIT header, exact module-name `#print` and clean line-end whitespace.
ROADMAP is strictly append-only; historical reports/reviews and all Lean files are
unchanged. Final `git diff --check` (unstaged changes) exits0. The raw merge-base-to-
worktree check exits2 solely for 31 verified intentional two-space Markdown breaks:
28 preserved historical/header lines plus three concurrent user README header lines.
Every exception is Markdown, in the first six lines, and exactly two spaces.
`git -c core.whitespace=-blank-at-eol,blank-at-eof,space-before-tab,tab-in-indent
diff --check <merge-base>` exits0. This explicit policy is not reported as a raw
whitespace PASS. New release documents were checked separately as well.

One initial `git fetch origin` failed with exit255 because the sandbox made
`.git/FETCH_HEAD` read-only. The explicitly authorized fetch was then rerun with
sandbox escalation and succeeded (exit0). No Lean build failed or needed repair.
The initial raw branch-wide `git diff --check origin/develop...HEAD` returned2:
release PR-DRAFT/README trailing spaces and historical Markdown hard-break spaces.
The rewritten release files were normalized. Historical instructions/reviews, the old ROADMAP header and concurrent README
header retain their intentional Markdown hard-break bytes under
the no-history-rewrite contract; the raw committed HEAD check still describes the
pre-edit snapshot. Current changes and added Lean source whitespace are audited
separately; no cosmetic exception is presented as a successful raw check.
Two audit-helper assertions were corrected: an initial assumption that the staged
path list stayed fixed (concurrent README staging), and a whitespace configuration
that omitted the explicit `-blank-at-eol` setting. These were harness assumptions,
not Lean/source failures; the final checks passed with the documented Markdown
exception policy, preserving user edits.

## Mathematical conclusions retained from the checked results

The existing API compiles without a new smoke namespace fix. Explicit scoped
imports provide all 30 research owners while avoiding the larger historical
facade's dependency surface; keeping this as the public research entry is useful.
The default library glob already includes later tests, so appending 49 imports to
the root is unnecessary. These are release findings, not new arithmetic results.

The checked Step040 implication is
`all p²∣Δ ∧ |Δ|<M → Δ=0 → Fermat7Equation`; it cannot be advertised as Fermat
impossibility. Step041's actual focused primitive non-Fermat examples independently
invalidate attempts to drop either premise. The (5,8,9,4) calibration still has
additive focus. No further support/depth/example catalogue was attempted.

Direct old-source regressions reconfirm the Row-Z signed root and common ramified
summit are already constructed. Old signed discriminant−7 `TraceOneInt(-2)` differs
from the new discriminant−3 `TraceOneInt(-1)` Eisenstein carrier. The terminal
exponent-one seed/provider is uninhabited; lifted primitive nextX/Y/Z, exact carrier
matching, and original CRT independent bounds / final row mismatch remain open.
Internal depth5→4 is not a reconstructed primitive descent. No replacement theorem
or implementation proposal is selected: **STOP042 remains**.

## Concrete PR handoff and integration

Title: **feat(math): package GTail selective-gap kernels and FLT7 conditional research APIs**.
Base: `develop`. Head: `feature/GTail-SelectiveGap-FLT7-261009-v0`.
Final reviewable body: [PR-DRAFT.md](PR-DRAFT.md); scientific closeout:
[PR-CLOSEOUT.md](PR-CLOSEOUT.md). Both include the exact import snippets,
validated smoke, current counts, directionality, source frontier and existing warnings.

After successful fetch, comparison is ahead136/behind1. Develop-only commit
`ad8526451` adds one independent CF2D proposal document outside this Lean subtree.
Recommend a separately authorized ordinary merge and validation at the resulting
HEAD rather than rewriting the 136-commit history. Its apparent conflict risk is
small, but no merge is claimed or tested. Optional neutral/research PR separation
may improve reviewability; no split was performed. Local release acceptance is
READY; integration, review and publication remain separate decisions.

The handoff stops here with Outcome B / STOP042. No stronger FLT7 endpoint is
asserted from successful import/test compilation.

## Collected selected public axiom outputs (288 distinct declarations)

```text
DkMath.CosmicFormula.GTail_seven_five: [propext, Classical.choice, Quot.sound]
DkMath.CosmicFormula.GTail_seven_six: [propext, Classical.choice, Quot.sound]
DkMath.CosmicFormula.coeffGCD_dvd_choose: [propext, Classical.choice, Quot.sound]
DkMath.CosmicFormula.coeffGCD_dvd_selectedBody: [propext, Classical.choice, Quot.sound]
DkMath.CosmicFormula.coeffGCD_empty: [propext, Classical.choice, Quot.sound]
DkMath.CosmicFormula.coeffGCD_eq_one_of_self_mem: [propext, Classical.choice, Quot.sound]
DkMath.CosmicFormula.coeffGCD_eq_one_of_zero_mem: [propext, Classical.choice, Quot.sound]
DkMath.CosmicFormula.coeffGCD_eq_prime_of_interior: [propext, Classical.choice, Quot.sound]
DkMath.CosmicFormula.coeffGCD_mul_monomial_dvd_selectedBody: [propext, Classical.choice, Quot.sound]
DkMath.CosmicFormula.coeffGCD_prime_interior: [propext, Classical.choice, Quot.sound]
DkMath.CosmicFormula.coeffGCD_seven_interior: [propext, Classical.choice, Quot.sound]
DkMath.CosmicFormula.coeffGCD_seven_zero_endpoint: [propext, Classical.choice, Quot.sound]
DkMath.CosmicFormula.coprime_product_seven_quadratic: [propext, Classical.choice, Quot.sound]
DkMath.CosmicFormula.dvd_coeffGCD_iff: [propext, Classical.choice, Quot.sound]
DkMath.CosmicFormula.dvd_selectedResidual_of_dvd_coeff: [propext, Classical.choice, Quot.sound]
DkMath.CosmicFormula.gtail_seven_exact_seven_layer: [propext, Classical.choice, Quot.sound]
DkMath.CosmicFormula.monomial_dvd_selectedBody: [propext, Classical.choice, Quot.sound]
DkMath.CosmicFormula.not_prime_dvd_gtail_seven_of_gap: [propext, Classical.choice, Quot.sound]
DkMath.CosmicFormula.padicValNat_gap_mul_gtail_seven: [propext, Classical.choice, Quot.sound]
DkMath.CosmicFormula.padicValNat_gtail_seven_eq_one: [propext, Classical.choice, Quot.sound]
DkMath.CosmicFormula.prime_mul_coords_dvd_selectedBody_interior: [propext, Classical.choice, Quot.sound]
DkMath.CosmicFormula.selectedBody_Ico: [propext, Classical.choice, Quot.sound]
DkMath.CosmicFormula.selectedBody_Ico_split_at: [propext, Classical.choice, Quot.sound]
DkMath.CosmicFormula.selectedBody_complement: [propext, Classical.choice, Quot.sound]
DkMath.CosmicFormula.selectedBody_empty: [propext, Classical.choice, Quot.sound]
DkMath.CosmicFormula.selectedBody_eq_min_max_mul_residual: [propext, Classical.choice, Quot.sound]
DkMath.CosmicFormula.selectedBody_eq_monomial_mul_residual: [propext, Classical.choice, Quot.sound]
DkMath.CosmicFormula.selectedBody_erase: [propext, Classical.choice, Quot.sound]
DkMath.CosmicFormula.selectedBody_full: [propext, Classical.choice, Quot.sound]
DkMath.CosmicFormula.selectedBody_insert: [propext, Classical.choice, Quot.sound]
DkMath.CosmicFormula.selectedBody_seven_five: [propext, Classical.choice, Quot.sound]
DkMath.CosmicFormula.selectedBody_seven_interior: [propext, Classical.choice, Quot.sound]
DkMath.CosmicFormula.selectedBody_seven_interior_eq_mul_residual: [propext, Classical.choice, Quot.sound]
DkMath.CosmicFormula.selectedBody_seven_six: [propext, Classical.choice, Quot.sound]
DkMath.CosmicFormula.selectedBody_singleton: [propext, Classical.choice, Quot.sound]
DkMath.CosmicFormula.selectedBody_transport: [propext, Classical.choice, Quot.sound]
DkMath.CosmicFormula.selectedGap_Ico: [propext, Classical.choice, Quot.sound]
DkMath.CosmicFormula.selectedGap_add_selectedBody: [propext, Classical.choice, Quot.sound]
DkMath.CosmicFormula.selectedGap_complement: [propext, Classical.choice, Quot.sound]
DkMath.CosmicFormula.selectedGap_empty: [propext, Classical.choice, Quot.sound]
DkMath.CosmicFormula.selectedGap_erase: [propext, Classical.choice, Quot.sound]
DkMath.CosmicFormula.selectedGap_full: [propext, Classical.choice, Quot.sound]
DkMath.CosmicFormula.selectedGap_insert: [propext, Classical.choice, Quot.sound]
DkMath.CosmicFormula.selectedGap_seven_interior: [propext, Classical.choice, Quot.sound]
DkMath.CosmicFormula.selectedGap_transport: [propext, Classical.choice, Quot.sound]
DkMath.CosmicFormula.selectedResidual_seven_interior: [propext, Classical.choice, Quot.sound]
DkMath.CosmicFormula.selectedSeven_zero_endpoint_transport: [propext, Classical.choice, Quot.sound]
DkMath.CosmicFormula.selected_balance_transport: [propext, Classical.choice, Quot.sound]
DkMath.CosmicFormula.selected_erase_of_lt: [propext, Classical.choice, Quot.sound]
DkMath.CosmicFormula.selected_insert_of_lt: [propext, Classical.choice, Quot.sound]
DkMath.CosmicFormula.selected_insert_of_mem: [propext, Classical.choice, Quot.sound]
DkMath.CosmicFormula.selected_modEq_of_dvd_moved: [propext, Classical.choice, Quot.sound]
DkMath.CosmicFormula.seven_mul_coords_dvd_selectedBody_interior: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.GTailCommonReceiver.M43: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.GTailCommonReceiver.M43_comap_cyclotomic: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.GTailCommonReceiver.M43_comap_cyclotomic_slot_zero: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.GTailCommonReceiver.M43_comap_eisenstein: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.GTailCommonReceiver.M43_isMaximal: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.GTailCommonReceiver.M43_isPrime: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.GTailCommonReceiver.eval43: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.GTailCommonReceiver.eval43_comp_cyclotomic: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.GTailCommonReceiver.eval43_comp_eisenstein: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.GTailCommonReceiver.eval43_scalar: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.GTailCommonReceiver.eval43_surjective: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.GTailCommonReceiver.eval43_tau: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.GTailCommonReceiver.eval43_zeta: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.GTailCommonReceiver.fromCyclotomic: [propext, Quot.sound]
DkMath.FLT.Seven.GTailCommonReceiver.fromCyclotomic_injective: [propext, Quot.sound]
DkMath.FLT.Seven.GTailCommonReceiver.fromCyclotomic_zeta: [propext, Quot.sound]
DkMath.FLT.Seven.GTailCommonReceiver.fromEisenstein: [propext, Quot.sound]
DkMath.FLT.Seven.GTailCommonReceiver.fromEisenstein_injective: [propext, Quot.sound]
DkMath.FLT.Seven.GTailCommonReceiver.fromEisenstein_intCast: [propext, Quot.sound]
DkMath.FLT.Seven.GTailCommonReceiver.fromEisenstein_tau: [propext, Quot.sound]
DkMath.FLT.Seven.GTailCommonReceiver.omega_relation: [propext, Quot.sound]
DkMath.FLT.Seven.GTailCommonReceiver.scalar_images_eq: [propext, Quot.sound]
DkMath.FLT.Seven.GTailFocusedCapacityIndependence.exists_full_support_without_size: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.GTailFocusedCapacityIndependence.exists_size_without_full_support: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.GTailFocusedDefectGlobalCapacity.finite_defect_zero_certificate: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.GTailFocusedDefectGlobalCapacity.finite_support_nonzero_bound: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.GTailFocusedDefectGlobalCapacity.finite_support_zero: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.GTailFocusedDefectGlobalCapacity.full_quadratic_defect_zero_certificate: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.GTailFocusedDefectGlobalCapacity.int_nonzero_modulus_bound: [propext]
DkMath.FLT.Seven.GTailFocusedDefectGlobalCapacity.int_zero_of_modulus_size: [propext]
DkMath.FLT.Seven.GTailFocusedDefectGlobalCapacity.quadratic_modulus_dvd_square: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.GTailFocusedDefectGlobalCapacity.quadratic_modulus_le_square: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.GTailFocusedDefectGlobalCapacity.quadratic_prime_support: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.GTailFocusedDefectGlobalCapacity.squarePrimeSupportModulus: [propext, Quot.sound]
DkMath.FLT.Seven.GTailFocusedDefectGlobalCapacity.squarePrimeSupportModulus_dvd_iff: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.GTailFocusedDefectGlobalCapacity.squarePrimeSupportModulus_eq: [propext, Quot.sound]
DkMath.FLT.Seven.GTailFocusedDefectGlobalCapacity.squarePrimeSupportModulus_pos: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.GTailFocusedDefectSquareFirewall.defect_square_iff_product_int: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.GTailFocusedDefectSquareFirewall.defect_square_iff_product_nat: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.GTailFocusedDefectSquareFirewall.defect_square_prime_route: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.GTailFocusedDefectSquareFirewall.endpoint_unit_of_defect: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.GTailFocusedDefectSquareFirewall.focusedFermatDefect: [propext]
DkMath.FLT.Seven.GTailFocusedDefectSquareFirewall.focusedFermatDefect_eq: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.GTailFocusedDefectSquareFirewall.focusedFermatDefect_zero_iff: [propext]
DkMath.FLT.Seven.GTailFocusedPrimeRoute.focused_coordinate_units: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.GTailFocusedPrimeRoute.focused_prime_route: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.GTailFocusedPrimeRoute.gap_nonidentity_guard_unavailable: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.GTailFocusedPrimeRoute.gap_ratio_eq_one: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.GTailFocusedPrimeRoute.norm_image_ne_cyclotomic: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.GTailFocusedPrimeRoute.tail_receiver: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.GTailFocusedPrimeRoute.tail_source_images_ne: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.GTailGenericPrimeReceiver.evPair: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.GTailGenericPrimeReceiver.evPair_43: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.GTailGenericPrimeReceiver.evPair_comp_cyclotomic: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.GTailGenericPrimeReceiver.evPair_comp_eisenstein: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.GTailGenericPrimeReceiver.evPair_surjective: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.GTailGenericPrimeReceiver.focused_receiver: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.GTailGenericPrimeReceiver.nativeEval: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.GTailGenericPrimeReceiver.nativeKernel: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.GTailGenericPrimeReceiver.nativeKernel_comap_cyclotomic: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.GTailGenericPrimeReceiver.nativeKernel_comap_eisenstein: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.GTailGenericPrimeReceiver.nativeKernel_isMaximal: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.GTailGenericPrimeReceiver.native_eisenstein_mem: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.GTailGenericPrimeReceiver.native_eisenstein_source_mem: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.GTailGenericPrimeReceiver.native_factor_mem: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.GTailGenericPrimeReceiver.native_factor_source_mem: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.GTailGenericPrimeReceiver.native_residue_zeros: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.GTailGenericPrimeReceiver.native_square_support: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.GTailGenericPrimeReceiver.pairedKernel: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.GTailGenericPrimeReceiver.pairedKernel_43: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.GTailGenericPrimeReceiver.pairedKernel_comap_cyclotomic: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.GTailGenericPrimeReceiver.pairedKernel_comap_eisenstein: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.GTailGenericPrimeReceiver.pairedKernel_eq_sup: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.GTailGenericPrimeReceiver.pairedKernel_isMaximal: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.GTailGenericPrimeReceiver.pairedKernel_isPrime: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.GTailPrimeGrid.M: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.GTailPrimeGrid.M_comap_cyclotomic: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.GTailPrimeGrid.M_comap_cyclotomic_row: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.GTailPrimeGrid.M_comap_eisenstein: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.GTailPrimeGrid.M_comap_eisenstein_column: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.GTailPrimeGrid.M_injective: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.GTailPrimeGrid.M_isMaximal: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.GTailPrimeGrid.M_isPrime: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.GTailPrimeGrid.M_zero_zero: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.GTailPrimeGrid.eisenstein43Root: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.GTailPrimeGrid.eisenstein43Root_injective: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.GTailPrimeGrid.eisenstein43Root_relation: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.GTailPrimeGrid.evGrid: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.GTailPrimeGrid.evGrid_comp_cyclotomic: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.GTailPrimeGrid.evGrid_comp_eisenstein: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.GTailPrimeGrid.evGrid_scalar: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.GTailPrimeGrid.evGrid_surjective: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.GTailPrimeGrid.evGrid_tau: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.GTailPrimeGrid.evGrid_zero_zero: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.GTailPrimeGrid.evGrid_zeta: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.GTailPrimeGrid.evR43: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.GTailPrimeGrid.factor_mem_iff: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.GTailPrimeGrid.map_cyclotomic_le: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.GTailPrimeGrid.map_cyclotomic_lt_zero_zero: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.GTailPrimeGrid.map_eisenstein_le: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.GTailPrimeGrid.map_eisenstein_lt_zero_zero: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.GTailPrimeGrid.normCoord_mem_iff: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.GTailPrimeGrid.seven43Root: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.GTailPrimeGrid.seven43Root_injective: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.GTailPrimeGrid.seven43Root_ne_one: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.GTailPrimeGrid.seven43Root_ne_zero: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.GTailPrimeGrid.seven43Root_pow_seven: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.GTailPrimeJoin.A: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.GTailPrimeJoin.B: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.GTailPrimeJoin.M43_eq_sup: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.GTailPrimeJoin.M_eq_map_eisenstein_sup_map_cyclotomic: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.GTailPrimeJoin.M_le_sup: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.GTailPrimeJoin.coordinate_decomposition: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.GTailPrimeJoin.cyclotomic_mem_B_pow: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.GTailPrimeJoin.cyclotomic_mem_M_pow: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.GTailPrimeJoin.eisenstein_mem_A_pow: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.GTailPrimeJoin.eisenstein_mem_M_pow: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.GTailPrimeJoin.rowDifference: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.GTailPrimeJoin.rowDifference_mem: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.GTailPrimeJoin.rowRemainder: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.GTailPrimeJoin.rowRemainder_mem: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.GTailPrimeJoin.sup_le_M: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.GTail_mem_scalar_mul_kernel_of_factor_mem_square: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.GTail_seven_one_eq_homogeneous_sum: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.evalCyclotomic_gtailFactor: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.eval_selected_cofactor_eq_tailShellPoly_derivative: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.existsUnique_gtail_second_digit: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.exists_positive_focused_gap: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.fermat7Equation_iff_focused_norm_balance: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.fermat7Equation_iff_focused_scalar_balance: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.fermat7_focused_bounds: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.focused_cyclotomic_depth_endpoint: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.focused_eisenstein_norm_square_endpoint: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.focused_gap_lt_coordinates: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.focused_gtail_eq_norm_square: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.focused_norm_depth_guards: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.focused_norm_scalar_depth_readouts: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.focused_tail_fourth_iff_norm_square_dvd: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.fortyNine_dvd_focused_gap_of_units: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.gtailCyclotomicCofactor: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.gtailCyclotomicCofactor_mul_factor: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.gtailCyclotomicCofactor_not_mem_selected: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.gtailCyclotomicEval: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.gtailCyclotomicEval_linearFactor: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.gtailCyclotomicFactor: [propext, Quot.sound]
DkMath.FLT.Seven.gtailCyclotomicFactor_depth_one: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.gtailCyclotomicFactor_depth_three: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.gtailCyclotomicFactor_mem_cube_iff: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.gtailCyclotomicFactor_mem_fourth_iff: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.gtailCyclotomicFactor_mem_sixRootKernel_iff: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.gtailCyclotomicFactor_mem_square_iff: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.gtailCyclotomicFactor_mem_square_of_sq_dvd_GTail: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.gtailCyclotomicFactor_not_mem_square: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.gtailCyclotomicFactor_unique_slot: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.gtailCyclotomicFactor_zero: [propext, Quot.sound]
DkMath.FLT.Seven.gtailCyclotomicLinearFactor: [propext, Quot.sound]
DkMath.FLT.Seven.gtailCyclotomicLinearFactor_mem_ker: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.gtailCyclotomicLinearFactor_mem_sixRootKernel_iff: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.gtailCyclotomicLinearFactor_mem_sixRootKernel_zero: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.gtailCyclotomicLinearFactor_not_mem_sixRootKernel: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.gtailCyclotomicLinearFactor_unique_address: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.gtailDerivativeInt: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.gtailDerivativeInt_cast: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.gtailFirstCorrection: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.gtailFirstCorrection_equation: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.gtailFirstCorrection_unique: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.gtailSelectedCofactorResidue: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.gtail_first_correction_lifts: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.gtail_integer_derivative_not_dvd: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.gtail_integer_square_support: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.gtail_integer_taylor: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.gtail_lift_sq_iff_correction: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.gtail_lift_sq_iff_linear: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.gtail_second_lift_iff_linear: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.gtail_second_lift_predicate: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.gtail_second_shift_derivative: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.gtail_second_shift_eval: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.gtail_second_shift_gap_unit: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.gtail_second_shift_ratio: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.gtail_selected_cofactor_balance: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.gtail_selected_cofactor_formula: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.gtail_selected_cofactor_ne_zero: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.gtail_selected_cofactor_uniform: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.gtail_seven_defect: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.gtail_seven_eq_of_counterexamplePack: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.gtail_seven_eq_of_fermat7Equation: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.gtail_seven_shell: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.gtail_shell_derivative_balance: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.gtail_shell_derivative_formula: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.gtail_shell_derivative_ne_zero: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.gtail_shift_cast: [propext, Quot.sound]
DkMath.FLT.Seven.gtail_shift_derivative: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.gtail_shift_gap_unit: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.gtail_shift_ratio: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.gtail_shift_tail_support: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.gtail_support_of_square: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.not_seven_dvd_sum_of_focused_equation: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.padicValNat_focused_gap_balance: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.padicValNat_focused_gap_unit_balance: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.padicValNat_focused_quadratic_budget: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.prime_focused_support_exclusive: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.prime_square_focused_allocation: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.prod_six_gtailCyclotomicFactor_eq_GTail: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.seven_dvd_focused_gap: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.seven_dvd_quadratic_of_focused_units: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.twentyOne_dvd_prime_sub_one_of_focused_tail: [propext, Classical.choice, Quot.sound]
DkMath.Lib.NumberTheory.conj_gtailSevenNormCoord: [propext]
DkMath.Lib.NumberTheory.dvd_quadratic_iff_dvd_gtailSevenNormCoord: [propext, Classical.choice, Quot.sound]
DkMath.Lib.NumberTheory.eisensteinResidueEval_gtailSevenNormCoord_conjugate: [propext, Classical.choice, Quot.sound]
DkMath.Lib.NumberTheory.eisensteinResidueEval_gtailSevenNormCoord_conjugate_ne_zero: [propext, Classical.choice, Quot.sound]
DkMath.Lib.NumberTheory.eisensteinResidueEval_gtailSevenNormCoord_zero: [propext, Classical.choice, Quot.sound]
DkMath.Lib.NumberTheory.gtailSevenNormCoord_eq: [propext]
DkMath.Lib.NumberTheory.gtailSevenNormCoord_mem_residueIdeal: [propext, Classical.choice, Quot.sound]
DkMath.Lib.NumberTheory.gtailSevenNormCoord_mul_conj: [propext, Classical.choice, Quot.sound]
DkMath.Lib.NumberTheory.gtailSevenNormCoord_not_mem_conjugate_residueIdeal: [propext, Classical.choice, Quot.sound]
DkMath.Lib.NumberTheory.gtailSevenNormCoord_split_square_address: [propext, Classical.choice, Quot.sound]
DkMath.Lib.NumberTheory.gtailSevenResidueIdeals_ne_conjugate: [propext, Classical.choice, Quot.sound]
DkMath.Lib.NumberTheory.gtailSevenResidueRoot: [propext, Classical.choice, Quot.sound]
DkMath.Lib.NumberTheory.gtailSevenResidueRoot_conjugate_polynomial: [propext, Classical.choice, Quot.sound]
DkMath.Lib.NumberTheory.gtailSevenResidueRoot_ne_conjugate: [propext, Classical.choice, Quot.sound]
DkMath.Lib.NumberTheory.gtailSevenResidueRoot_polynomial: [propext, Classical.choice, Quot.sound]
DkMath.Lib.NumberTheory.gtailSevenResidue_trace_ne_zero: [propext, Classical.choice, Quot.sound]
DkMath.Lib.NumberTheory.gtailSevenTailRatio: [propext, Classical.choice, Quot.sound]
DkMath.Lib.NumberTheory.gtailSevenTailRatio_ne_one: [propext, Classical.choice, Quot.sound]
DkMath.Lib.NumberTheory.gtailSevenTailRatio_ne_zero: [propext, Classical.choice, Quot.sound]
DkMath.Lib.NumberTheory.gtailSevenTailRatio_pow_seven: [propext, Classical.choice, Quot.sound]
DkMath.Lib.NumberTheory.gtailSeven_paired_residue: [propext, Classical.choice, Quot.sound]
DkMath.Lib.NumberTheory.norm_gtailSevenNormCoord: [propext, Classical.choice, Quot.sound]
DkMath.Lib.NumberTheory.norm_gtailSevenNormCoord_sq: [propext, Classical.choice, Quot.sound]
DkMath.Lib.NumberTheory.prime_ne_three_of_gtail: [propext, Classical.choice, Quot.sound]
DkMath.Lib.NumberTheory.scalar_dvd_gtailSevenNormCoord_iff: [propext]
DkMath.Lib.NumberTheory.scalar_three_dvd_gtailSevenNormCoord_sq: [propext, Classical.choice, Quot.sound]
DkMath.Lib.NumberTheory.selectedBody_seven_interior_eq_norm_square: [propext, Classical.choice, Quot.sound]
DkMath.Lib.NumberTheory.seven_dvd_prime_sub_one_of_gtail: [propext, Classical.choice, Quot.sound]
DkMath.Lib.NumberTheory.twentyOne_dvd_prime_sub_one_of_quadratic_gtail: [propext, Classical.choice, Quot.sound]
```
