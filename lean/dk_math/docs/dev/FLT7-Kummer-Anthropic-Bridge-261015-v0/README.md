# FLT7 Kummer × Anthropic Bridge — workspace reconciliation

Branch: `research/FLT7-Kummer-Anthropic-Bridge-261015-v0`  
Base: `develop` at `fcbcb43abe062d9f0d49c43e454f259982b995af` (2026-10-15 JST)  
Status: **Gate 000 / STARTED — reconnaissance and type-level reconciliation; FLT7 independent closure OPEN**  
Owner: DkMath research / Codex implementation.

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

| Anthropic entry | DkMath candidate | Current assessment |
| --- | --- | --- |
| `IsCyclotomicExtension.Rat.seven_pid` | `DkMath/FLT/Seven/SevenRamifiedFusionCyclotomicSevenPID.lean` | analogous seven-cyclotomic PID result; verify exact carrier |
| `isPrincipal_of_isPrincipal_pow_of_coprime` | `DkMath/Lib/NumberTheory/IdealPowerFactor.lean`, `PrincipalIdealPower.lean`, `ClassGroupTorsionBridge.lean` | principalization bridge already available with hypotheses |
| `FltIdeals.fltIdeals_coprime` / `CaseI.is_principal` | `DkMath/FLT/Kummer/CyclotomicPrincipalization.lean`, FLT7 chosen-linear-factor modules | hypothesis/branch matching not established |
| `KummersLemma.eq_pow_prime_of_unit_of_congruent` | `DkMath/FLT/Seven/PrimeTraceOneDirectCyclotomicUnitCongruence.lean` | key bridge candidate; DkMath `DegreeSixKummerUnitLemmaAtSeven` is **a Prop target**, not a theorem |
| `CaseII.exists_solution'` / `not_exists_solution` | `DkMath/FLT/Kummer/CyclotomicPrincipalization.lean` peel/normal-form targets | strict descent witness not established |
| `flt_regular` | `DkMath/FLT/Kummer/RegularPrimeRoute.lean` | comparison endpoint only; do not use to short-circuit FLT7 |

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

Read `ROADMAP.md` and `instruction-001.md` from this Lean development document directory. Gate 001 must first produce
`bridge-matrix-001.md` and `report-001.md`, with exact `#check` signatures,
file:line evidence, definitions unfolded when needed, and a prioritized list of
minimal lemma contracts. Only subsequent accepted gates should change
production Lean. Avoid duplicate implementations, `sorry`, extra axioms,
vacuous `True` targets, circular FLT imports, and fabricated build results.

Acceptance requires Lean kernel build, `#print axioms`, and precise report
of any existing untrusted or unrelated import dependencies. No claim of
FLT7 closure before an actual independent terminal contradiction exists.
