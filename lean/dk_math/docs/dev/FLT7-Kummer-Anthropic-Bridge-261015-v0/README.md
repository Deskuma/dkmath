# FLT7 Kummer × Anthropic Bridge — workspace reconciliation

Branch: `research/FLT7-Kummer-Anthropic-Bridge-261015-v0`  
Base: `develop` at `fcbcb43abe062d9f0d49c43e454f259982b995af` (2026-10-15 JST)  
Status: **Gate 001 ACCEPTED (Outcome B; see review-001.md); Gate 002 G1–G3 PROVED locally (Outcome A; review pending); FLT7 independent closure OPEN**
Owner: DkMath research / Codex implementation.  
cid: `6acfa54a-d360-83ee-8c52-2fadfef957d0`

## Purpose

Compare DkMath's actual Lean proof graph with the Kummer regular-prime route in
[Anthropic fermats-last-theorem](https://github.com/anthropics/fermats-last-theorem),
especially `P2M/Sol/S_flt_regular.lean`. Find the *smallest honest bridges* that
DkMath lacks, implement reusable lemmas without duplication, and identify whether
any missing unit normalization or genuine strict descent can be proved from
existing DkMath hypotheses.

This work **does not** close FLT7 by importing a completed external `fermatLastTheoremSeven`
or `flt_regular` theorem. A completed external result is the independent comparison
oracle, not the endpoint of the DkMath-native investigation.

## Locations and provenance

- GitHub repository `Deskuma/dkmath` is the canonical source; repository root: `/`.
- Lean project root: `lean/dk_math`. Lean development documents belong under
  `lean/dk_math/docs/dev/` (relative to the repository root), and under
  `docs/dev/` when working inside the Lean project root.
- **Codex must validate declarations, proof status and builds against the
  checked-out repository HEAD.** Prior research notes are not proof of
  current source or compilation.
- Anthropic reference pinned for inspection:
  https://github.com/anthropics/fermats-last-theorem/tree/6e837e75355538c7f80bab5b956861e86c4eacc2
- Upstream `PROOF-PATH.md` and `ATTRIBUTION.md` are part of the source map.
  `S_flt_regular.lean` includes ported work from the flt-regular project;
  do not copy/vendor code without checking its Apache-2.0 attribution and DkMath
  license requirements.

## Initial source map (candidates, not type-checked equivalences)

| Anthropic entry                                      | DkMath candidate                                                                                            | Current assessment                                                                                 |
| ---------------------------------------------------- | ----------------------------------------------------------------------------------------------------------- | -------------------------------------------------------------------------------------------------- |
| `IsCyclotomicExtension.Rat.seven_pid`                | `DkMath/FLT/Seven/SevenRamifiedFusionCyclotomicSevenPID.lean`                                               | analogous seven-cyclotomic PID result; verify exact carrier                                        |
| `isPrincipal_of_isPrincipal_pow_of_coprime`          | `DkMath/Lib/NumberTheory/IdealPowerFactor.lean`, `PrincipalIdealPower.lean`, `ClassGroupTorsionBridge.lean` | principalization bridge already available with hypotheses                                          |
| `FltRegular.fltIdeals_coprime` / `FltRegular.is_principal` | `DkMath/FLT/Kummer/CyclotomicPrincipalization.lean`, FLT7 chosen-linear-factor modules                      | hypothesis/branch matching not established                                                         |
| `FltRegular.eq_pow_prime_of_unit_of_congruent`     | `DkMath/FLT/Seven/PrimeTraceOneDirectCyclotomicUnitCongruence.lean`                                         | the Prop specification is now inhabited by `SevenCyclotomicDegreeSixInt.degreeSixKummerUnitLemmaAtSeven` (Gate 002; report-002.md) |
| `CaseII.exists_solution'` / `not_exists_solution`    | `DkMath/FLT/Kummer/CyclotomicPrincipalization.lean` peel/normal-form targets                                | strict descent witness not established                                                             |
| `flt_regular`                                        | `DkMath/FLT/Kummer/RegularPrimeRoute.lean`                                                                  | comparison endpoint only; do not use to short-circuit FLT7                                         |

Existing DkMath localized sources:
- `DkMath/FLT/Kummer/{Basic,GapDivisibleBranch,CyclotomicPrincipalization,ClassGroupBridge,RegularPrimeRoute}.lean`
- `DkMath/FLT/Seven/SevenRamifiedFusionCyclotomicDegreeSixPID.lean`
- `DkMath/FLT/Seven/PrimeTraceOneDirectCyclotomicChosenTail.lean`
- `DkMath/FLT/Seven/PrimeTraceOneDirectCyclotomicUnitCongruence.lean`
- `DkMath/FLT/Seven/PrimeTraceOneDirectCyclotomicCMTorsionPhase.lean`
- `DkMath/FLT/Seven/PrimeTraceOneDirectRealCubicCommonPrimeKummer.lean`
- `DkMath/FLT/Seven/PrimeTraceOneCyclotomicPidBypassAudit.lean`

## Mathematical frontiers

1. Ideal power to principal generator: `(a)=I^7` -> `a=u*b^7` is **not**
   an automatic exact seventh power. Preserve the unit obstruction.
2. Kummer's unit lemma: in a seventh cyclotomic integer ring with regularity,
   a unit congruent modulo 7 to an integer is a seventh power. Distinguish
   a scalar congruence from an arbitrary unit; verify the precise modulus,
   casting, field/ring equivalence, and hypotheses.
3. Case II: compare Anthropic's ramifier valuation `m+1 -> m` descent with
   DkMath's peel/Gap reduction. These may be **different** descent problems.
4. Branches: Anthropic case I/II distinguishes `p ∤ abc` and `p | abc`;
   DkMath may use `q | z-y` or a chosen orientation. No name-based identification.
5. Genuine terminal obstruction: no implication from a newly proved polynomial
   identity, unit-sector packet, or conditional receiver to unconditional FLT7.

## Critical existing risks to audit

- `DegreeSixKummerUnitLemmaAtSeven : Prop` is a stated target, not evidence
  that the corresponding theorem is proved.
- `CyclotomicPrincipalization.lean` contains an existing `sorry` in
  `cyclotomicPrincipalizationNonFirstCasePeelDescentExistenceCore_of_classGroupPTorsionFree`.
  Report its *actual active dependency path*, do not hide it or conflate it with
  every theorem in the file.
- Verify the semantics of `CyclotomicIdealPthPowerTarget` and
  `CyclotomicClassGroupPTorsionFreeTarget` directly before using them. Historically
  one was an overly weak placeholder and the other too globally quantified.
- Some FLT7 chosen-factor theorems depend on a constructed packet. Check every
  constructor and source hypothesis before labeling them unconditional.

## Research protocol

Read `ROADMAP.md`, `review-001.md`, and `instruction-002.md` from this Lean development document directory. Gate 001 has produced `bridge-matrix-001.md` and `report-001.md` and is accepted as an audit (Outcome B). Gate 002 is limited to the concrete p=7 unit bridge; Codex must stop after its report and independent review. Do not treat any conditional interface or prior proof inventory as FLT7 closure. Avoid duplicate implementations, `sorry`, extra axioms,
vacuous `True` targets, circular FLT imports, and fabricated build results.

Acceptance requires Lean kernel build, `#print axioms`, and precise report
of any existing untrusted or unrelated import dependencies. No claim of
FLT7 closure before an actual independent terminal contradiction exists.

## Gate review and active instruction (2026-10-15)

- [Gate 001 review](review-001.md): **ACCEPTED / Outcome B**. The 17-row matrix, focused builds, and axiom checks validate the reconnaissance only.
- [Gate 002 instruction](instruction-002.md): prove the congruence-constrained Kummer unit lemma for the concrete degree-six ring (G1–G3), or report an honest blocker.
- Gate 001's historical comparison-copy provenance needs a reproducibility erratum. **GitHub sources at pinned commits and this repository are authoritative**, not locally available temporary copies.
- Chosen-factor `L = π * γ^7` is already established under its source packet; the *next cyclotomic integer state with strictly reduced ramifier valuation* remains OPEN. Gate 002 does not undertake that descent.

## Gate 002 local implementation (2026-10-15)

G1–G3 are proved in `DkMath/FLT/Seven/PrimeTraceOneDirectCyclotomicKummerUnit.lean`.
The existing `DegreeSixKummerUnitLemmaAtSeven : Prop` now has the theorem
`DkMath.FLT.Seven.SevenCyclotomicDegreeSixInt.degreeSixKummerUnitLemmaAtSeven`.
The focused production build and arbitrary congruent-unit regression passed;
all three theorem axiom sets contain only `propext`, `Classical.choice`, `Quot.sound`.
See [report-002.md](report-002.md) for exact proofs, failed attempts, helper exports,
and the Gate-001 provenance erratum. Local Outcome A is limited to these three
unit lemmas; independent review is pending. STOP after Gate 002.

The enlarged cyclotomic descent state and actual strict successor remain OPEN.
Gate 003 requires new scope after review. No broad facade/default-driver wiring
was added for this module.
