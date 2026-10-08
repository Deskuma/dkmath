# Source inventory 025

The initial checkout was clean on research/GapFocusing-ExponentGauge-Ultra-261004-v0.
Read instruction-025.md, report-024.md and the current Legendre facade before edits.

## Neutral Pascal sources

- BinomialPrime defines AllInnerChooseDivisible, InnerRowSupportPrime and the historical RowBirthPrime. Its forward theorem prime_allInnerChooseDivisible_self is reused. RowBirthPrime records common support and row-index divisibility, not globally new coordinate birth. Its roadmap comment now points to the proved converse in PascalPrebirthBoundary.
- BinomialPrimePower defines PrimePowerRowSupport, prime_power_allInnerChooseDivisible, prime_power_rowBirthPrime and the exact prime-power index-valuation identities. Existing PrimePrebirthAlternation is now a definitional specialization of one generic carrier. prime_prebirthAlternation_step consumes the generic recurrence step, and prime_prebirthAlternation consumes the generic equivalence. No second prime-specific induction remains.
- PascalPrimeDial exposes coefficient height, pascalPrimeDialHeight_prime_pow_add_index, pascalPrimeDialHeight_prime_pow and prime_power_unitFilteredPrimeDialHeight. prime_not_dvd_pascalCoeffMass_of_row_lt requires an actual in-range coefficient; out-of-range zero coefficients are not usable absence evidence.
- PascalPrimeCoordinateDecoder defines genuine birth by cumulative support difference. mem_pascalPrimeCoordinateBirthSupport_iff identifies it with the row's own prime. pascalPrimeBirthLogMass_eq is prime-only, and pascalPrimeCoordinateSupportUpTo_succ adds a coordinate only at a prime successor. These definitions are unchanged.
- StructuralArithmetic.PowerGauge projects exponents by remainder modulo a period. It is unrelated to the common Pascal modulus or the newly local pascalPrimePowerLogGauge.

## Growth and existing Legendre sources

- WallisGrowthBridge supplies exact central-binomial growth identities through centralRatioQ, mirrorOddRatioPartialQ and Wallis products. It supplies no old-coordinate budget for the gnomon cell.
- WallisCellGrowth supplies exact arbitrary-cell prefix products, the symmetry-shortened pascalCellGrowthQ evaluator, and pascalCellGrowthQ_eq_cast_choose. The new calibration wallisCellGrowth_bridge applies this existing evaluator to the gnomon cell. The large Wallis module is kept out of the new production dependency chain.
- ZsigmondyCyclotomic imports Mathlib.Data.Nat.Choose.Lucas and wraps Lucas and Kummer. Foundational Pascal classification imports Mathlib Lucas directly; no Zsigmondy dependency is introduced.
- Legendre.Basic fixes the strict SquareCell endpoints, SquareOffset, squareOffsets and squareCell_iff_exists_squareOffset. The new shell mass reuses that exact finite carrier.
- Legendre.Frontier identifies LegendreConjecture with the support-escape provider and failure of complete old-wave cover. These are equivalences, not proofs of the provider.
- Live modules introduced or changed by implementation checkpoints 016 through 024 were inventoried from their implementation commits. There are 24 checkpoint/file entries and 23 distinct current source files. Headers, imports and named declarations are recorded in [prior-source-index-025.txt](evidence/MANIFEST.md#log-3ec58fa1d1216bac). This is a source inventory, not a claim that all old declarations were individually axiom-audited in 025.
- The earlier shell-transition, owner-fold, CRT, full-town, deletion, retained-direction and terminal-product layers preserve finite or conditional capacity semantics. The 024 terminal-product and source-count bounds do not supply a strict carry-budget bound for the new Pascal cell. No deletion-packing layer is extended here.

## Installed Mathlib API

Exact namespaces and relevant signature conditions were checked in the installed sources.

- Choose.lucas_theorem_nat is an alias of choose_modEq_prod_range_choose_nat. It requires Fact p.Prime and bounds n and k below a power of p.
- Choose.eq_pow_multiplicity_of_choose_modEq_zero_nat requires positive N and all coefficients indexed by Finset.Icc 1 (N-1) congruent to zero modulo p. It concludes N = p ^ multiplicity p N. For N > 1 the resulting exponent is positive.
- Choose.gcd_choose_eq_minFac_of_isPrimePow uses exactly (Finset.Icc 1 (N-1)).gcd (Nat.choose N).
- Choose.gcd_choose_eq_one_of_not_isPrimePow requires N > 1. The wrapper uses this exact gcd, without new gcd machinery.
- Nat.factorization_choose expresses the valuation as a carry-count filter on Finset.Ico 1 b. It requires p prime, k <= N and Nat.log p N < b.
- Nat.factorization_choose_le_log has no additional caller hypotheses. Nat.factorization_choose_le_one requires N < p^2. Nat.factorization_choose_eq_zero_of_lt requires N < p.
- Nat.Prime.dvd_choose requires k < p, N-k < p and p <= N. This gives the fresh-factor direction directly, avoiding a new product-divisor argument.
- Nat.ascFactorial_eq_factorial_mul_choose and ascFactorial_eq_prod_range provide the exact factorial numerator identity.
- Real.log_nat_eq_sum_factorization supplies the full weighted prime-power ledger. Finset.sum_range_add and sum_Ico_add' provide the old/fresh split and exact offset reindexing.

## Placement and audit scope

The generic recurrence is in BinomialPrimePower. Classification and the common gcd are in PascalPrebirthBoundary. Decoder and real-log adapters are local to PascalPrebirthBirth. Gnomon wrappers are in Legendre.GnomonPascalCell. Neutral modules do not import Legendre.

[declaration-coverage-025.json](evidence/MANIFEST.md#log-2092ea8ffd4895a6) enumerates every named public declaration in the five affected production source modules and both new calibration modules. The axiom probe covers 95 production declarations and 33 calibration declarations, including all 49 new production declarations. Existing declarations in changed files are included, rather than only a handpicked theorem sample.
