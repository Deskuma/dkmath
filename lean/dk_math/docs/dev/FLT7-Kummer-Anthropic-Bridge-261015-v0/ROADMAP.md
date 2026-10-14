# ROADMAP — FLT7 Kummer × Anthropic Bridge

Branch: `research/FLT7-Kummer-Anthropic-Bridge-261015-v0`  
Base: `develop`  
Document root: `lean/dk_math/docs/dev/FLT7-Kummer-Anthropic-Bridge-261015-v0/`  
Status: **000 STARTED / 001 ASSIGNED to Codex / 002+ PLANNED**.

## Gates

| Gate | Aim | Deliverable | Acceptance |
| --- | --- | --- | --- |
| 000 | Baseline, branch, source pointer, scope | `README.md`, `ROADMAP.md`, `instruction-001.md` | this branch exists; no Lean changes |
| 001 | Workspace-wide source and theorem reconciliation | `bridge-matrix-001.md`, `report-001.md`, optional `evidence/001-*.txt` | exact signatures/provenance; A/B/C statuses; missing contracts identified; audit-only |
| 002 | Kummer unit lemma at degree seven | new minimal bridge under `DkMath/FLT/Seven/` or reusable lib only if generic | no `sorry` or unproved unit-surjectivity; focused build and axioms |
| 003 | Principalization + chosen-factor integration | minimal constructor/adapter proof | precise source data and unit congruence; no duplication |
| 004 | Case I vs Gap/chosen orientation mapping | branch transport lemmas, or a documented obstruction | proper hypotheses, no invalid case identification |
| 005 | Case II strict descent feasibility | witness / well-founded decreasing measure or a rigorous blocker | strict decrease and integer closure, not merely conditional existence |
| 006 | Independent FLT7 consumer assessment | minimal noncircular integration, or explicit Outcome B/C | no use of external finished FLT7 and no hiding placeholders |
| 007 | Facade, regression, audit, review | `report-007.md`, compatibility checks, final dependency DAG | green focused builds, standard axioms, reviewed diff |

**Gate 001 is the only authorized execution step of `instruction-001.md`.**
Following gates require scope adjustment based on the source audit; the table is
a research plan, not a claim that the listed theorems can be proved.

## Gate 001 minimum audit rows

- Anthropic `IsRegularPrime`, `isPrincipal_of_isPrincipal_pow_of_coprime`,
  `FltIdeals.fltIdeals_coprime`, `CaseI.is_principal`.
- Anthropic `KummersLemma.exists_pow_eq_of_zeta_sub_one_pow_dvd_sub_one`,
  `KummersLemma.eq_pow_prime_of_unit_of_congruent`.
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

From the repository's `lean/dk_math` Lean project root, run only feasible focused targets and local
test/audit modules before large builds.  Prefer `LEAN_NUM_THREADS=1` (or 2
if memory permits); avoid fresh all-Mathlib rebuilds on limited RAM.
Read root `AGENT.md` for layering: `DkMath.*` research -> `DkMath.Lib.*`
promoted -> `DkMathlib.*` public. Do not allow reverse dependencies.
Check `sorry`, `admit`, new `axiom`, and `#print axioms` on every public
bridge. Baseline existing `sorry` must be clearly separated from new proof
dependencies. Respect external Apache-2.0 attribution if borrowing source.
