# ROADMAP — FLT7 Kummer × Anthropic Bridge

Branch: `research/FLT7-Kummer-Anthropic-Bridge-261015-v0`  
Base: `develop`  
Document root: `lean/dk_math/docs/dev/FLT7-Kummer-Anthropic-Bridge-261015-v0/`  
Status: **000 COMPLETE; 001 ACCEPTED (Outcome B, review-001.md); 002 G1–G3 PROVED locally (Outcome A, report-002.md), REVIEW PENDING; 003+ ON HOLD**.

## Gates

| Gate | Aim | Deliverable | Acceptance |
| --- | --- | --- | --- |
| 000 | Baseline, branch, source pointer, scope | `README.md`, `ROADMAP.md`, `instruction-001.md` | this branch exists; no Lean changes |
| 001 | Workspace-wide source and theorem reconciliation | `bridge-matrix-001.md`, `report-001.md`, `review-001.md`, evidence | **ACCEPTED / Outcome B**; inventory complete, FLT7 OPEN |
| 002 | Concrete degree-six Kummer unit lemma from mod-7 scalar congruence (G1/G2/G3) | `instruction-002.md`; new source/test if provable; `report-002.md` | **G1–G3 PROVED locally / Outcome A / REVIEW PENDING**; focused build + arbitrary-unit regression passed, standard axioms only |
| 003 | Principalization + chosen-factor integration | minimal constructor/adapter proof | precise source data and unit congruence; no duplication |
| 004 | Case I vs Gap/chosen orientation mapping | branch transport lemmas, or a documented obstruction | proper hypotheses, no invalid case identification |
| 005 | Case II strict descent feasibility | witness / well-founded decreasing measure or a rigorous blocker | strict decrease and integer closure, not merely conditional existence |
| 006 | Independent FLT7 consumer assessment | minimal noncircular integration, or explicit Outcome B/C | no use of external finished FLT7 and no hiding placeholders |
| 007 | Facade, regression, audit, review | `report-007.md`, compatibility checks, final dependency DAG | green focused builds, standard axioms, reviewed diff |

**Gate 001 is complete and reviewed. Gate 002 implementation is complete locally and awaits review.**
Stop after Gate 002 for review; Gates 003+ are illustrative and must be re-scoped to reflect the already-completed chosen packet and missing actual descent. No gate entails that its mathematical obligations are provable.

## Gate 001 minimum audit rows

- Anthropic `IsRegularPrime`, `isPrincipal_of_isPrincipal_pow_of_coprime`,
  `FltRegular.fltIdeals_coprime`, `FltRegular.is_principal`.
- Anthropic `FltRegular.exists_pow_eq_of_zeta_sub_one_pow_dvd_sub_one`,
  `FltRegular.eq_pow_prime_of_unit_of_congruent`.
- Anthropic `CaseII.exists_solution'`, `not_exists_solution`, `caseI`,
  `caseII`, `flt_regular`, and `IsCyclotomicExtension.Rat.seven_pid`.
- DkMath `DegreeSixKummerUnitLemmaAtSeven`,
  `DegreeSixUnitCongruentToRationalModSeven`,
  `CyclotomicSeven.ringOfIntegers_isPrincipalIdealRing`,
  `SevenCyclotomicDegreeSixInt.ringIsPrincipalIdealRing`,
  `DirectCyclotomicChosenQuotientPowerPacket.exists_directLinearFactor_seventhPower_unconditional`,
  `CyclotomicPrincipalizationNonFirstCasePeelNormalFormDescentTarget`,
  its existence-core theorem, and `classGroupPTorsionFreeAt`.

## Outcome discipline

- **A — typed reusable bridge actually proved:** a new noncircular bridge
  closes a precisely named obligation, with kernel/axiom evidence.
- **B — truthful partial alignment:** exact theorem correspondences are
  mapped, but arithmetic hypotheses or descent witnesses remain.
- **C — incorrect target or incompatibility:** mismatch, counterexample,
  hidden hypothesis, circular dependency, vacuous/overstrong target.

Each report records: branch and HEAD, commands and exit codes, changed paths,
exact lemma statements and import parents, axioms, blockers and next smallest
testable step. Preserve historical research statuses such as GTail STOP042,
and do not claim FLT7 is solved by this roadmap.

## Build and trust policy

From the repository's `lean/dk_math` Lean project root, run appropriate focused build targets and local test/audit modules before wider builds. Parallelism, resource limits, and build strategy are chosen by Codex and the execution environment; do not prescribe `LEAN_NUM_THREADS`.
Read root `AGENT.md` for layering: `DkMath.*` research -> `DkMath.Lib.*`
promoted -> `DkMathlib.*` public. Do not allow reverse dependencies.
Check `sorry`, `admit`, new `axiom`, and `#print axioms` on every public
bridge. Baseline existing `sorry` must be clearly separated from new proof
dependencies. Respect external Apache-2.0 attribution if borrowing source.
