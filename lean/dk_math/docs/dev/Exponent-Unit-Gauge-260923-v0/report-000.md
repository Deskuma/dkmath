# GAGE-000 — Exponent / Unit Gauge inventory and API boundary

Branch: `research/Exponent-Unit-Gauge-260923-v0`
Checkpoint: GAGE-000
Result: **Outcome B — documentation-only boundary freeze**

## 1. Outcome

The requested vocabulary is not yet a single production API, but nearly all of
the arithmetic and carrier theorems it would expose already have owners. No
new Lean definition is justified at GAGE-000. Adding a Gauge hierarchy now
would duplicate one or more of the following existing layers:

- Pascal prime-dial and prime-power row data;
- natural-number valuation and power-factor utilities;
- the generic Power Gap/Beam factorization;
- the GTail/GN to cyclotomic shell, norm, and ideal-norm chain;
- TraceOne coordinate landing and the fixed-prime scalar calibrations.

The smallest non-duplicating boundary is therefore a future thin facade for
the exponent-side names, followed by separate value-side, dyadic, and landing
modules only when their missing statements are specified. GAGE-000 stops here;
GAGE-001 is not implemented.

## 2. Inventory

| concept | existing owner/module | existing theorem/definition names | reuse status | missing theorem if any | proposed new owner |
|---|---|---|---|---|---|
| `ExponentGaugeHeight` | `DkMath.NumberTheory.PascalPrimeDial` | `pascalCoeffMass`, `pascalPrimeDialHeight`, `UniformPrimeDialHeight`, `FilteredPrimeDialHeight`, `pascalPrimeDialHeight_eq_zero_of_row_lt`, `pascalPrimeDialHeight_prime_pow`, `pascalPrimeDialHeight_prime_pow_add_index` | **Semantic reuse.** The intended height is already exactly `padicValNat p (Nat.choose n k)` through `pascalPrimeDialHeight`. | No arithmetic lemma is missing for GAGE-001. Only a public vocabulary alias/theorem family may be added; do not define a second height. | `DkMath.NumberTheory.Gauge.Exponent` as a thin facade over `PascalPrimeDial` |
| `PrimeExponentGauge` | `DkMath.NumberTheory.BinomialPrime`, `BinomialPrimePower`, `PascalPrimeDial` | `InnerRowSupportPrime`, `RowBirthPrime`, `UniformBeamHeight`, `prime_innerRowSupportPrime_self`, `prime_uniformBeamHeight_self`, `prime_power_innerRowSupportPrime`, `prime_power_unitFilteredPrimeDialHeight` | **Reuse existing predicates and bridges.** These already distinguish support from uniform valuation height. | A bundled neutral gauge record is absent, but is not required until the facade shape is fixed. | `DkMath.NumberTheory.Gauge.Exponent`; retain the divisibility theorem ownership in the existing modules |
| `PrimePowerExponentGauge` | `DkMath.NumberTheory.BinomialPrimePower`, `PascalPrimeDial` | `PrimePowerRowSupport`, `padicValNat_choose_prime_pow`, `padicValNat_choose_prime_pow_add_index`, `prime_power_unitFilteredBeamHeight`, `prime_power_unitFilteredPrimeDialHeight`, `prime_power_pow_dvd_choose_of_padicValNat_index` | **Reuse as-is.** Exact prime-power depth and the `p`-unit index filter already exist. | No new characterization may be assumed. In particular, the converse “common inner support implies prime-power row” remains open/deferred. | `DkMath.NumberTheory.Gauge.Exponent` for names only |
| `ValueGauge` / local power residue | `DkMath.Lib.NumberTheory.PadicValNat`, compatibility facade `DkMath.ABC.PadicValNat`, and `DkMath.Lib.Cosmic.GTailPadic` | `padicValNat_split`, `padicValNat_eq_zero_iff`, `Vp_ge_one_iff`, `padicValNat_le_iff_dvd`, `padicValNat_pow`, `dvd_padicValNat_pow`, `padicValNat_carrier_shape_of_mul_eq_prime`, `prime_pow_sub_one_dvd_carrier`, `padicValNat_GN_exact_of_head_unit`, `padicValNat_GN_prime_eq_one_of_dvd_gap` | **Partial reuse.** The valuation engine and transport are present, but no value-side Gauge name exists. | A future `powerGaugeResidue n p a := padicValNat p a % n` and its nonzero/power transport lemmas are genuinely missing. Their hypotheses must handle zero and the prime/base conditions explicitly. | `DkMath.NumberTheory.Gauge.Value`; keep the valuation primitives in `DkMath.Lib.NumberTheory.PadicValNat` |
| `DyadicGauge` | `DkMath.CosmicFormula.PowerGapBeam`, `DkMath.CosmicFormula.CosmicFormulaPythagoras` | `powerGap`, `powerBeam`, `powerBeam_two`, `pow_two_sub_eq_pythagorean`, `powerBeam_two_eq_pythagorean_beam`, `PythagoreanCosmicForm`, `sq_sub_sq_gap_beam`, `gap_beam_factorization` | **Partial reuse.** The degree-two Gap/Beam algebra exists. The real Pythagorean layer is not the intended denominator-free natural exponent gauge API. | A denominator-free exponent-2 calibration and its exact correction-zero statement are missing from the intended gauge vocabulary. | `DkMath.NumberTheory.Gauge.Dyadic` |
| `MidpointCorrection` | No matching exponent-gauge owner. There are unrelated real/dyadic phase and midpoint modules under `DkMath.Analysis.DkReal` and `DkMath.CosmicFormula.HalfUnitZeroConjugate`. | Existing midpoint/phase declarations are not exponent-2 Gap/Beam statements. | **Do not reuse by name or semantics.** The nearby analytic midpoint APIs concern a different model. | The natural/integer denominator-free midpoint identity and any generic odd correction formula are missing. | `DkMath.NumberTheory.Gauge.Dyadic`; keep analytic phase modules out of this dependency |
| `FLT2` gauge split | Generic owner `DkMath.CosmicFormula.PowerGapBeam`; Pythagorean owner `DkMath.CosmicFormula.CosmicFormulaPythagoras`; neutral extraction owner `DkMath.Lib.NumberTheory.PowerFactor` | `flt_eq_forces_powerGapBeam`, `pow_two_sub_eq_pythagorean`, `powerBeam_two`, `power_factor_split` | **Partial reuse only.** The factorization and generic coprime-power split are available. | A bounded primitive-natural FLT2 calibration combining `(z-y)(z+y)=x^2`, removal of the common factor `2`, and coprime square extraction is absent. | A separate FLT-owned file, preferably `DkMath.FLT.QuadraticGauge` (or an explicitly FLT-scoped successor); do not move this theorem into `DkMath.Lib` |
| `CyclotomicGaugeResolver` | `DkMath.Lib.Cosmic.GTailCyclotomic`, `DkMath.CFBRC.CyclotomicNorm`, `DkMath.CFBRC.CyclotomicIdeal`, `DkMath.FLT.Prime.PrimeCyclotomicIdeal`, `PrimeCyclotomicTraceOne`, `PrimeCyclotomicCalibration` | `GTail_one_eq_GTailCyclotomicShell`, `GTail_one_eq_cyclotomicHomEval_of_prime`, `cyclotomicRootProduct_eq_shell`, `cyclotomicRootProduct_eq_GTail_one`, `cyclotomicRootProduct_eq_GN`, `gap_mul_cyclotomicRootProduct_eq_sub_pow`, `cyclotomicLinearFactor_norm_eq_GN`, `cyclotomicLinearFactorIdeal_absNorm_eq_GN`, packet `...absNorm_eq_residual`, packet `...gap_mul_..._eq_pow` | **Semantic bridge required; proofs already exist.** Do not re-prove the carrier chain. | A named exponent-gauge-to-carrier adapter is missing. It should be a theorem facade over the existing scalar identities, not a new cyclotomic or ideal construction. | `DkMath.FLT.Prime.PrimeGaugeBridge` for the FLT packet adapter; generic shell/norm ownership remains unchanged |
| `GaugeConservationKernel` | Distributed across `GTail`, `GTailCyclotomic`, `CyclotomicNorm`, `CyclotomicIdeal`, and the prime packet adapters | `GTail_one_eq_sum`, `GTail_one_eq_GTailCyclotomicShell`, `cyclotomicRootProduct_eq_GN`, `gap_mul_cyclotomicRootProduct_eq_sub_pow`, `gap_mul_cyclotomicLinearFactorIdeal_absNorm_eq_sub_pow`, `PrimeAdicFactorPacket.gap_mul_cyclotomicIdeal_absNorm_eq_pow` | **Existing conservation chain; no new kernel structure justified.** The complete gap must remain visible. | Only a thin named theorem family is missing. Do not introduce quotient-group machinery or replace the PR #105 chain with a record. | Reuse current owners; if a facade is needed, place only semantic aliases in `PrimeGaugeBridge` |
| `AdditiveLanding` | `DkMath.Lib.NumberTheory.TraceOneLatticeLanding`, `TraceOnePowerLanding`, `DkMath.FLT.Prime.PrimeCyclotomicTraceOne`, `PrimeCyclotomicCalibration` | `traceOne_pow_core_landing_iff`, `traceOne_sq_core_landing_iff`, `traceOne_pow_coordinates`, `traceOne_sq_coordinates`, `traceOne_norm_pow`, `traceOne_norm_eq_norm_mul_pow_of_eq`, `traceOne_lattice_landing_not_square`, `TraceOneScalar.coord_norm_eq_cyclotomicIdeal_absNorm`, `coord_norm_eq_traceOneNorm_three/five/seven` | **Partial reuse.** Neutral power/Core landing and fixed-prime scalar calibrations already exist. | A neutral additive predicate for `x^n + y^n` and a resolved-carrier landing facade are absent. No universal non-landing theorem follows from the current criteria. | `DkMath.NumberTheory.Gauge.Landing`; import the neutral TraceOne library, and keep fixed-prime adapters in `DkMath.FLT.Prime.PrimeGaugeBridge` |

### Boundary observations

`DkMath.NumberTheory.StructuralArithmetic.PowerGauge` already defines
`projectExponent`, `SamePowerSector`, and `SamePowerStructure`. This is a
period-modulo observation kernel for abstract exponent coordinates; it does
not expose Pascal `p`-adic height or value-side power landing. It must not be
silently renamed or treated as the proposed `ExponentGauge`.

Likewise, `DkMath.NumberTheory.MultiGauge` owns `GNGaugeStage`, `PrimeCaught`,
and `PrimeEscapes` for a value-side GN observer and cross-multiplication
transitions. It is not the exponent-side gauge requested here. Reusing either
module without a semantic equivalence theorem would violate the separation
between exponent data and value data.

## 3. Recommended module and facade layout

The thinnest future layout is:

```text
DkMath/NumberTheory/Gauge/Exponent.lean  -- GAGE-001; Pascal facade only
DkMath/NumberTheory/Gauge/Value.lean     -- GAGE-003; valuation residue only
DkMath/NumberTheory/Gauge/Dyadic.lean    -- GAGE-004; denominator-free d=2 layer
DkMath/NumberTheory/Gauge/Landing.lean   -- GAGE-007; neutral landing vocabulary
DkMath/FLT/QuadraticGauge.lean            -- GAGE-005; FLT-owned arithmetic split
DkMath/FLT/Prime/PrimeGaugeBridge.lean   -- GAGE-006; FLT packet/cyclotomic adapters
```

The FLT2 arithmetic calibration should remain FLT-scoped. It may use
`DkMath.CosmicFormula.PowerGapBeam` and
`DkMath.Lib.NumberTheory.PowerFactor`, but it should not be placed in the
generic gauge library. No `DkMath/NumberTheory/Gauge/Conservation.lean` is
recommended at this stage: the existing conservation chain is already owned
and a new structure would obscure the complete-product boundary.

No file from this layout is created by GAGE-000.

## 4. APIs to reuse unchanged

The following are the canonical inputs for later checkpoints:

1. Exponent-side Pascal data:
   `pascalPrimeDialHeight`, `UniformPrimeDialHeight`,
   `FilteredPrimeDialHeight`, `PrimePowerRowSupport`,
   `padicValNat_choose_prime_pow`,
   `padicValNat_choose_prime_pow_add_index`, and
   `prime_power_unitFilteredPrimeDialHeight`.
2. Weighted and tail transport:
   `weightedBinomialTerm`, `GTailOneTerm`,
   `FilteredBeamHeight.dvd_GTailOneTerm_of_height_ge`,
   `FilteredBeamHeight.dvd_filteredGTailOneSum_of_height_ge`, and
   `GTail_one_eq_innerBeam_add_right`.
3. Generic Gap/Beam algebra:
   `powerGap`, `powerBeam`,
   `pow_sub_pow_eq_gap_mul_powerBeam`,
   `pow_two_sub_eq_pythagorean`, and
   `powerBeam_two_eq_pythagorean_beam`.
4. Value-side and power-factor utilities:
   `padicValNat_le_iff_dvd`, `padicValNat_pow`,
   `dvd_padicValNat_pow`, `power_factor_split`,
   `exists_squarefree_mul_sq`, and the ideal counterparts in
   `IdealPowerFactor`/`PrincipalIdealPower`.
5. The existing carrier chain:
   `GTail_one_eq_GTailCyclotomicShell`,
   `cyclotomicRootProduct_eq_GN`,
   `gap_mul_cyclotomicRootProduct_eq_sub_pow`,
   `cyclotomicLinearFactor_norm_eq_GN`,
   `cyclotomicLinearFactorIdeal_absNorm_eq_GN`, and the
   `PrimeAdicFactorPacket`/`PrimeAdicPowerSplit` adapters.
6. Neutral TraceOne landing:
   `traceOne_pow_core_landing_iff`, `traceOne_sq_core_landing_iff`,
   `traceOne_pow_coordinates`, `traceOne_norm_pow`, and the explicit
   nonzero-norm condition. The latter is essential: arbitrary TraceOne norms
   are not positive-definite for every parameter.

## 5. Genuinely missing lemmas or API decisions

The following are the actual next gaps, rather than reasons to duplicate
existing implementations:

- Decide whether `ExponentGaugeHeight` is an `abbrev`/semantic alias or only a
  theorem vocabulary. Either choice must reduce to `pascalPrimeDialHeight`.
- Define the value-side residue interface separately from exponent-side
  Pascal data. The first useful statement is local and valuation-based; it is
  not a quotient-group construction.
- Prove the denominator-free exponent-2 midpoint/correction identity in the
  intended natural/integer domain, with no appeal to real division.
- Prove the bounded primitive FLT2 arithmetic split, including the exact
  hypotheses needed to remove the common factor `2` before applying
  `power_factor_split`.
- Add only semantic carrier bridges for the already-proved GN/shell/norm/ideal
  chain. The complete gap factor must remain in the theorem statements.
- Choose a neutral `AdditiveLanding` predicate and connect it to the existing
  TraceOne Core-image criteria. This must not be presented as a universal
  non-landing theorem for all prime exponents.

Deferred by the checkpoint contract: converse prime-power-row
characterizations, quotient-group power-class machinery, universal additive
non-landing, class-group elimination for arbitrary primes, and any general-FLT
terminal contradiction.

## 6. Proposed GAGE-001 scope

GAGE-001 should implement only the exponent facade:

- import `DkMath.NumberTheory.PascalPrimeDial` and, where needed,
  `DkMath.NumberTheory.BinomialPrimePower`;
- expose the existing Pascal height under the agreed exponent-gauge
  vocabulary without introducing a second implementation;
- expose prime-row and prime-power-row height/support facts by direct theorem
  aliases or thin semantic bridges;
- preserve the distinction between `InnerRowSupportPrime` (support),
  `UniformBeamHeight` (valuation height), and value-side data;
- include focused API and `#print axioms` audits for every new substantive
  theorem;
- do not implement ValueGauge, DyadicGauge, FLT2, cyclotomic carrier
  re-proofs, or AdditiveLanding in GAGE-001.

## 7. Validation and audit results

- Current branch verified: `research/Exponent-Unit-Gauge-260923-v0`.
- The required README, ROADMAP, and instruction were read before the audit.
- All 17 modules named by the instruction were present and inspected.
- Cross-repository searches were performed for gauge, valuation, prime-power
  support, power-factor, coprime-power, Gap/Beam, midpoint, FLT2, cyclotomic,
  and landing APIs.
- Production Lean files were not changed. Therefore no focused Lean build or
  `lake build DkMath` was necessary for this documentation-only outcome.
- No new substantive theorem was added, so no new `#print axioms` audit was
  applicable.
- The report contains no `sorry`, `admit`, declared axiom, or unsafe proof
  shortcut.
- `git diff --check` and the untracked-file equivalent
  `git diff --no-index --check /dev/null docs/dev/Exponent-Unit-Gauge-260923-v0/report-000.md`
  are the required documentation checks for this change.

## 8. Git diff summary

Only this file is added:

```text
docs/dev/Exponent-Unit-Gauge-260923-v0/report-000.md
```

No production Lean module, import facade, theorem, definition, or existing
report was modified. Stop at GAGE-000.
