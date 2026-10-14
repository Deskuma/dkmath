# Report 025

Implemented the exact Pascal prebirth boundary, its prime-power classifier, the prime-row converse, and the gnomon Pascal fresh-factor and log-ledger bridges. The common modulus is an exact arithmetic scalar. No universal positive shell birth mass or Legendre provider was proved.

Changed production sources are BinomialPrime comments, BinomialPrimePower, PascalPrebirthBoundary, PascalPrebirthBirth and Legendre.GnomonPascalCell. The root and Legendre facades expose the new modules. New calibration modules cover the boundary and the gnomon cell; a complete named-public axiom probe is generated from the affected sources.

See [source-inventory-025.md](source-inventory-025.md), [findings-025.md](findings-025.md) and [validation-025.md](validation-025.md).

## 1. Generic carrier without a second prime theory

PascalPrebirthAlternationMod d m uses ZMod m and the phase (-1)^k for every k <= d. PrimePrebirthAlternation p is definitionally its specialization at d=p-1 and m=p. primePrebirthAlternation_iff is the thin adapter. The existing prime step and prime theorem now derive from the generic recurrence and equivalence; their separate induction was removed. Existing caller signatures are retained.

## 2. Exact next-row divisibility

pascalCancellationDefect_eq identifies each adjacent additive residue with choose(d+1,k+1). Its zero criterion is ordinary modulus divisibility. pascalPrebirthAlternationMod_iff_allInnerChooseDivisible proves the equivalence for every natural row and modulus. The reverse proof starts at choose(d,0)=1 and inducts using consecutive negation. Primality is unnecessary. The next-row prime-dial adapter requires an in-range coefficient, which ensures it is nonzero.

## 3. Modulus two

The equivalence includes modulus two, as well as zero and one. The binary regression proves the endpoint and (-1 : ZMod 2)=1. Collapsed signs retain the same cancellation theorem; no odd-prime assumption occurs.

## 4. Every positive prime-power exponent

prime_power_prebirthAlternation and prime_power_prebirth_packet prove the previous-row phase and common next-row support for prime p and every a>0. The divisibility component reuses prime_power_allInnerChooseDivisible. Zero exponent is excluded from the synchronization classification to avoid the empty inner row at N=1.

## 5. Exact synchronization classification

For prime p and N>1, allInnerChooseDivisible_prime_iff states common divisibility exactly as a positive witness N=p^a. The forward direction uses installed Choose.eq_pow_multiplicity_of_choose_modEq_zero_nat; N>1 forces its multiplicity witness positive. The reverse direction reuses the existing prime-power theorem. pascalPrebirthAlternationMod_prime_iff predicts the next positive p-power directly from the alternating phase. No new Lucas proof was written.

## 6. The old converse is closed

prime_iff_allInnerChooseDivisible_self proves primality equivalent to divisibility of every inner coefficient by the row number, for N>1. If N is not a prime power, its common gcd is one, contradicting N divisibility. Otherwise N divides minFac N and minFac N<=N, so N equals its prime minimal factor. No FactorRigid or custom primality predicate is introduced.

## 7. Prime rows from the preceding phase

prime_iff_prebirthAlternation_self proves, for N>1, that N is prime exactly when row N-1 alternates modulo N. This follows by the generic boundary and the closed converse. The N>1 restriction avoids the vacuous row-one boundary.

## 8. Maximal common cancellation modulus

pascalInnerCommonDivisor wraps exactly Mathlib's gcd on Finset.Icc 1 (N-1). dvd_pascalInnerCommonDivisor_iff identifies its divisors with all common inner-row moduli. pascalPrebirthAlternationMod_iff_dvd_commonDivisor identifies those same divisors with preceding-row alternating cancellation. Maximal means maximal under divisibility. For N>1 it equals minFac N at prime powers, one at other rows, and N precisely at prime rows.

## 9. Mathlib already supplies the detector

IsPrimePow, the Lucas multiplicity theorem and the common-gcd classification suffice. No custom detector is needed. At p^a with a>0, pascalInnerCommonDivisor_prime_pow gives common modulus p. The local real corollary pascalPrimePowerLogGauge_eq proves log(p)/log(p^a)=1/a. Its prime and positive-exponent hypotheses handle nonzero logarithms. It is unrelated to StructuralArithmetic.PowerGauge, which reduces exponents modulo a period.

## 10. Monotonicity audit

Raw adjacent-defect count, phase mismatch count and centered adjacent magnitude all have increases. The scan order and the smallest recorded counterexamples for the three raw and three normalized quantities are in findings-025.md. Prime targets already fail for raw A and C at target 5, rows 1 to 2; phase M fails at rows 2 to 3. Higher powers fail for every tested quantity at target 4, base 2, rows 1 to 2. These numerical counterexamples are also Lean regressions.

The exception for first prime targets is A/d: all in-range adjacent defects are nonzero before the prime boundary, and all vanish at it. Its pattern is exactly one followed by zero. The pointwise absence theorem is proved; no general count-antitonicity API is added. There is no smooth monotone approach theorem for higher powers. The scan checks 138 prime-target transitions and 663 higher-power-target transitions with base primes through 31 and powers at most 128. Smallest is relative to the recorded ordering, not a universal minimality claim.

## 11. Genuine birth and existing-direction synchronization

prime_prebirth_birth_packet packages earlier-row absence, prime prebirth phase, genuine coordinate birth at p and birth log mass log(p). For positive powers, prime_power_coordinate_birth_iff proves base-coordinate birth exactly when a=1. prime_power_resynchronization_packet proves the higher-power phase and common support while locating p in earlier cumulative support and excluding it from new birth support. Decoder definitions are unchanged. Historical RowBirthPrime is explicitly documented as row-index support, not genuine global birth.

## 12. Gnomon Pascal fresh-factor criterion

GnomonPascalCell n is choose(n^2+2*n,2*n). gnomonPascalCell_mul_factorial gives the exact product of n^2+1 through n^2+2*n, divided by (2*n)!.

For n>=3 and prime p>n^2, prime_dvd_gnomonPascalCell_iff gives cell divisibility exactly when SquareCell n p. The reverse direction uses Nat.Prime.dvd_choose with 2*n<p and n^2<p. The forward direction uses the bound that prime support of choose(top,k) lies below top. Thus the requested existential equivalence closes with strict square endpoints. The rational ratio is exactly 2/(n+2) for n>0; the zero-anchor failure is separately kernel-checked. This shrinking ratio supplies no prime-existence proof.

## 13. Positive shell birth log mass

gnomonPascalShellBirthLogMass sums pascalPrimeBirthLogMass over the existing squareOffsets carrier. gnomonPascalShellBirthLogMass_pos_iff proves positivity exactly when the square shell has a prime, for every natural n, including the empty zero shell. It uses nonnegative row birth mass and log(p)>0 at primes. This is an exact restatement, not a proof of positivity.

## 14. The growth-to-birth gap

The cell has an exact prime-power carry ledger, gnomonPascalCell_factorization_carries. For every fresh prime above n^2 the height is at most one and is exactly one in the shell. Nonprime coordinates contribute zero. Consequently gnomonPascalCell_fresh_logLedger identifies the fresh part with shell birth mass exactly, without extra fresh cancellation terms.

gnomonPascalCell_log_eq_old_add_birth proves:

log(cell) = old log budget + shell birth log mass.

The old budget counts all coordinates p<=n^2 with the complete binomial height, including repeated factors and factorial cancellation. This is a global-birth cutoff, larger than the old-wave cutoff p<=n in the capacity stack. A square-free old budget would be incorrect.

gnomonPascalOldLogBudget_lt_iff identifies the missing strict old-budget deficit with a local prime witness. legendreConjecture_iff_pascalOldBudget identifies the strict inequality for every n>=3 with the entire conjecture, after separately checking n=1 and n=2. These are reductions, not stronger providers. WallisCellGrowth is connected by an exact calibration evaluator theorem; central Wallis growth and the generic logarithmic valuation bound alone do not furnish the needed strict old-carry budget. No large analytic proof was attempted.

## 15. The 024 cofactor proposal

The geometry-reduced terminal cofactor proposal remains a possible local arithmetic refinement. The new Pascal boundary neither proves it nor supplies a stronger universal shell provider. Its relevance to the existing deletion route is unchanged; it is separate from the exact Pascal carry decomposition. No cofactor proof or new deletion campaign was added. Any later cofactor estimate still needs comparison with retained excess before claiming a capacity improvement.

## 16. The apparent 024 mismatches

No mismatch is present in the current report or kernel source. The existing carriers are {19,59,79} and {11,241,401}; the continuing primes are 19 and 11. New Lean arithmetic checks and independent exact diagnostics verify both factorization identities. No old theorem or report was altered to fit the suspected substitutions.

## Required finite rows

The previous-row phase and next-row common support in this table use the indicated modulus. At non-prime-powers the selected modulus is minFac N for a concrete negative diagnostic; there is no prime-power base.

| N | Gcd | Prime | Prime power | Base | Modulus | Previous phase | Common next support | Selected heights k:height |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| 2 | 2 | yes | yes | 2 | 2 | yes | yes | 1:1 |
| 3 | 3 | yes | yes | 3 | 3 | yes | yes | 1:1, 2:1 |
| 4 | 2 | no | yes | 2 | 2 | yes | yes | 1:2, 2:1, 3:2 |
| 5 | 5 | yes | yes | 5 | 5 | yes | yes | 1:1, 2:1, 4:1 |
| 6 | 1 | no | no | - | 2 | no | no | 1:1, 2:0, 3:2, 5:1 |
| 7 | 7 | yes | yes | 7 | 7 | yes | yes | 1:1, 3:1, 6:1 |
| 8 | 2 | no | yes | 2 | 2 | yes | yes | 1:3, 2:2, 4:1, 7:3 |
| 9 | 3 | no | yes | 3 | 3 | yes | yes | 1:2, 3:1, 4:2, 8:2 |
| 10 | 1 | no | no | - | 2 | no | no | 1:1, 2:0, 5:2, 9:1 |
| 12 | 1 | no | no | - | 2 | no | no | 1:2, 2:1, 6:2, 11:2 |
| 15 | 1 | no | no | - | 3 | no | no | 1:1, 3:0, 7:2, 14:1 |
| 25 | 5 | no | yes | 5 | 5 | yes | yes | 1:2, 5:1, 12:2, 24:2 |
| 27 | 3 | no | yes | 3 | 3 | yes | yes | 1:3, 3:2, 13:3, 26:3 |

This includes the required 4 to 5, 6 to 7, 7 to 8, 8 to 9, 24 to 25 and 26 to 27 boundaries. The neutral regression proves the nine positive-power packets, the four non-power gcd results, the binary endpoint and selected exact dial heights.

## Gnomon anchors

Exact support and valuation counts below were computed from factorial valuations. Their full prime-power product was independently compared to the exact binomial coefficient without printing that coefficient. Each anchor also has a named Lean regression proving one prime witness, cell divisibility, fresh height one and positive shell birth mass. The complete fresh-count totals are diagnostic results, not six new kernel prime-enumeration theorems.

| n | Row | Index | Ratio | Support count | Old support count | Fresh count | Maximum height | Shell birth log, approximate |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| 5 | 35 | 10 | 2/7 | 8 | 6 | 2 | 2 | 6.801283 |
| 11 | 143 | 22 | 2/13 | 16 | 12 | 4 | 3 | 19.573839 |
| 19 | 399 | 38 | 2/21 | 28 | 22 | 6 | 2 | 35.660027 |
| 29 | 899 | 58 | 2/31 | 43 | 35 | 8 | 4 | 54.147116 |
| 297 | 88803 | 594 | 2/299 | 421 | 376 | 45 | 4 | 512.592717 |
| 1031 | 1065023 | 2062 | 2/1033 | 1449 | 1289 | 160 | 3 | 2220.404276 |

The compact log records selected small-prime heights and the first and last fresh prime at each anchor. The JSON contains the full fresh support lists. Approximate real readouts are not used in any Lean proof.

## Next implementation proposal

Promote the log split to an exact natural-product certificate before seeking an analytic inequality. Define the old carry product as the product, over primes p<=n^2, of p raised to the cell's complete factorization height. Define the fresh product over shell prime points. For n>=3, prove cell = old carry product * fresh product using Mathlib's bounded binomial factorization product and the proved fresh height-one theorem.

Then prove, for n>=3, old carry product < cell exactly when shell birth mass is positive, with positivity of the cell explicit. Treat smaller anchors separately; at n=1 the fresh shell point 2 cancels against the local factorial, so the proposed fresh product formula cannot be extended unchanged. A useful bounded certificate would upper-bound the old carry product by an integer B strictly below the cell, using carry-count certificates rather than approximate logarithms or direct fresh-prime scanning. Test how sharp such old-carry bounds are at the six existing anchors. The global strict inequality remains equivalent to Legendre; product factorization alone cannot discharge it.

A useful preliminary arithmetic audit is whether the gnomon top row n*(n+2) can be a prime power for n>=3. The factor separation suggests it cannot: a shared prime base must divide two, and consecutive halves cannot both be nontrivial powers of two. This inference is not implemented here. If proved, it would explain why the whole-row common-modulus boundary does not directly supply a prime in this specific cell; it would still not rule out individual fresh factors.

The 024 cofactor proof may be resumed independently after this certificate interface is reviewed. It should remain a local arithmetic task until a strict global capacity improvement is proved.

Outcome B - PRIME-POWER PREBIRTH BOUNDARY IS EXACT BUT LEGENDRE GROWTH BRIDGE REMAINS
