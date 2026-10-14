# Instruction 040 report

Outcome B. A first-power gate gives a genuine independent repeated-large upper envelope. The general repeated-mass bound, its comparison with the 037 band, the combined correction bound, and its conditional prime-existence consumer are kernel checked. A strict repeated-budget saving at n=69 is also kernel checked. Floating diagnostics recover the 037 correction failures at n=69 and n=297, without the unresolved central-binomial conjecture. No universal strict budget theorem or new unconditional prime-existence range was proved.

## Mechanism and audited source

For a prime base p define

    a0(n,p) = max(2, floor_log_p(2*n) + 1).

This is the least repeated exponent whose power exceeds the shell width. Test only this first power:

    active(n,p) iff carryBit(n,p^a0) = 1.

For any a >= a0, p^a0 divides p^a. If the latter has carry, the existing next-multiple packet supplies a shell integer divisible by p^a. That integer is also divisible by p^a0. The existing large-divisor carry theorem then proves that the first power carries. Consequently, an inactive base excludes its entire later exponent chain. No test at a later power is needed to construct the envelope.

The source audit covered `gnomonLowDivisorCarryBit_large_gap`, the next-multiple packet and uniqueness, same-target same-base geometry, consecutive exponent fibers and their cutoff/cardinality/weight theorems, and the repeated/singleton split in GnomonCofactorWindow. The proof reuses GnomonCarryFiber's `gnomonLarge_divisor_carry`, rather than rebuilding divisibility incidence or factorial identities. Mathlib's `Nat.factorization_lcm`, prime-power factorization representation, and MaxPowDiv divisibility specification were also inspected. An lcm maximum would recover exact valuation information without an independent quantitative estimate; the thinner first-power gate already gives a useful bound, so no lcm framework was added.

The earlier 037 band/prefix identity was exposed as `gnomonRepeatedCarryBandBudget_prefix_identity`; its mathematical statement and proof remain unchanged. The Legendre facade imports the new production module.

## Strongest independent bound proved

The production module [GnomonRepeatedCarryPhase.lean](../../../DkMath/NumberTheory/Legendre/GnomonRepeatedCarryPhase.lean) defines a finite envelope

    E(n) = {d : 2*n < d <= n^2, d nonprime,
                 active(n,minFac(d))}.
    R_phase(n) = sum over d in E(n) of vonMangoldt(d).

Only prime powers contribute a nonzero weight. Every actual repeated carry label lies in E(n), and E(n) is a subset of the old nonprime band. Thus, for n >= 3,

    repeatedCarryMass(n) <= R_phase(n) <= repeatedBandBudget(n).

The definition does not use Q, shell primes, shell-prime birth mass, or budget strictness. It uses one fixed modular test per base, discards all later-power phase tests, and retains the full old exponent cutoff. In particular it does not substitute the exact repeated carry carrier into a new sum.

This information loss is certified in [GnomonRepeatedCarryPhaseCalibration.lean](../../../DkMathTest/NumberTheory/GnomonRepeatedCarryPhaseCalibration.lean): at n=69, 512 lies in E(69), but its actual carry bit is zero. The first base-2 power 256 carries; retaining 512 and all later powers deliberately overestimates the target. The generic excluded-label inequality proves

    R_phase(n) + vonMangoldt(d) <= repeatedBandBudget(n)

for any old-band label d outside E(n). Applying it to 625 at n=69, whose weight is log(5)>0, proves a strict budget saving in Lean. Uniform strictness for all n is not asserted.

## Multiplicity and the 2896 regression

An active base retains every exponent from a0 to floor_log_p(n^2). Every such exponent charges one log(p), including several exponents routed to the same shell integer. `gnomonRepeatedExponentInterval_weight` proves that this interval's weight is its cardinality times log(p). No target quotienting or constant fiber-length assumption occurs.

At n=2896, base 2 has a0=13, first power 8192, first gap 1792 <= 5792, and old cutoff 22. The calibration retains the existing exact fiber at target 8388608, its cardinality 10, all ten envelope memberships, and interval weight 10*log(2). This base contributes all ten powers, not one log per target. Across all bases, the repeated band decreases from about 3033.326690 to 184.362916; the exact repeated mass is about 96.974881. The envelope still contains 58 prime-power labels against 31 exact labels and excludes 422 old-band prime powers.

## Structural exclusions at n=69

Width is 138. Active bases are 2, 3, 7 and 31. Their retained exponent intervals are respectively [8,12], [5,7], [3,4] and [2,2]. Therefore

    R_phase(69) = 5*log(2) + 3*log(3) + 2*log(7) + log(31)
                approximately 14.087380.

The first power of base 5 is 625, with gap 239 > 138; both 625 and 3125 are excluded by one failed test. Base 13 starts at 169 with gap 140 > 138, so both 169 and 2197 are excluded. Base 11's 1331 is excluded, as are the square labels for bases 17, 19, 23, 29, 37, 41, 43, 47, 53, 59, 61 and 67. These are 17 excluded prime powers. The four active bases retain 11 labels, while only five labels carry. This difference is deliberate envelope slack.

All anchor base blocks, their first exponents/powers/gaps, later labels, and actual carry diagnostics are retained in `logs/diagnostics-040.json`. Composite labels that are not prime powers have weight zero and are omitted from the numerical prime-power inventory.

## Combined correction and consumer

The new `gnomonRepeatPhaseCorrectionBudget` is

    B040(n) = psi(2*n) - smallPhaseExcludedMass037(n)
                + R_phase(n) + higherReciprocalBudget(n).

The kernel-checked inequalities are, for n >= 3,

    C_ns(n) <= B040(n) <= B_phase037(n).

The comparison uses the exposed 037 prefix identity, so the small-carry estimate is exactly the strongest proved 037 bound. The higher term remains the existing reciprocal bound. No central-binomial compensation premise is introduced.

The consumer `exists_prime_squareCell_of_repeatPhaseBudget_lt` proves

    Q(n) + B040(n) < log(GnomonPascalCell(n))
      -> exists p, Prime(p) and SquareCell(n,p).

This remains a sufficient conditional criterion. It is not an equivalence and does not establish its strict premise globally.

## Retained diagnostics

The following logarithmic values and margins are floating diagnostics, not Lean proof premises. Margin means log(cell)-Q-B. General inequalities and the n=69 strict repeated saving are formal; the displayed consumer recoveries are numerical only.

| n | Exact repeated | Band 037 | R_phase | B040 | Margin 037 | Margin 040 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 3 | 0.000000 | 1.791759 | 0.000000 | 2.512121 | 2.268402 | 4.060161 |
| 32 | 9.124456 | 31.910486 | 11.321680 | 61.662604 | 22.189462 | 42.778268 |
| 69 | 9.117567 | 68.413726 | 14.087380 | 121.935840 | -11.231783 | 43.094563 |
| 297 | 18.855282 | 318.035599 | 37.079292 | 520.133429 | -52.888370 | 228.067937 |
| 1031 | 64.293694 | 1087.055997 | 107.338042 | 1933.676333 | 254.171238 | 1233.889193 |
| 2896 | 96.974881 | 3033.326690 | 184.362916 | 5560.492239 | -74.700426 | 2774.263347 |
| 5000 | 79.216579 | 5193.783679 | 147.922125 | 9576.589572 | 186.132458 | 5231.994013 |

The reproducible diagnostic sample is n=3..300 plus 1031, 2896 and 5000: 301 points. Every sampled repeated envelope is strictly smaller than the full band in floating weight. All 301 new correction criteria have positive sampled margins; 34 previously nonpositive margins recover. This finite sample provides no universal conclusion. Q and cell diagnostics are reused from 036 except at the new 2896 anchor, where Q is enumerated directly through the exact quotient windows and log(cell) through a stable finite log product. The source artifact hash is retained.

## Validation

The new production source has five definitions and ten theorems, plus one decidability instance. The axiom audit covers all 15 named declarations and the newly exposed 037 identity; the instance is checked through the envelope's dependency closure. Dependencies are confined to the standard Lean logical axioms propext, Classical.choice and Quot.sound, with some declarations needing fewer. There is no sorryAx or new assumption oracle.

The calibration file contains eight kernel-checked regressions, including the proper overcover, inactive-base exclusion, strict saving, retained ten-power interval, and gates at all required anchors. Point membership proofs expose interval bounds before scalar decisions; the quadratic carrier is not enumerated in these regression proofs. Two earlier exploratory focused invocations were manually interrupted while replacing expensive concrete carrier decisions with these local proofs. No memory failure was observed.

The source scan covers all five touched Lean files: three new modules, the modified 037 module and the facade. Headers and the immediate import-following file markers are preserved. The artifact check verifies the 301 diagnostic points, anchor block reconstruction, axiom coverage, four successful builds, ASCII report/log artifacts, and git diff whitespace.

| Build | Exit | Seconds | Maximum RSS (MiB) | Swaps |
| --- | ---: | ---: | ---: | ---: |
| focused | 0 | 34.594 | 6567.9 | 0 |
| axiom-audit | 0 | 20.127 | 6521.2 | 0 |
| facade | 0 | 51.544 | 6819.8 | 0 |
| root | 0 | 30.537 | 6822.2 | 0 |

All four final invocations used LEAN_NUM_THREADS=2 and GNU time resource telemetry. These are incremental builds with import replay, not clean-build performance benchmarks. Focused, facade and axiom logs contain no warnings. Root succeeds with five existing sorry warnings in TriominoFLT, ZsigmondyCyclotomicResearch, TriominoCosmicBranchA, GcdNextResearch and CyclotomicPrincipalization; none is in a touched file. No whole-repository sorry-free claim is made.

Reproduce from lean/dk_math:

    python3 docs/dev/GapFocusing-ExponentGauge-Ultra-261004-v0/checks/diagnostics-040.py
    python3 docs/dev/GapFocusing-ExponentGauge-Ultra-261004-v0/checks/build-040.py focused axiom-audit facade root
    python3 docs/dev/GapFocusing-ExponentGauge-Ultra-261004-v0/checks/check-040.py

The artifacts are `logs/coverage-040.json`, `logs/diagnostics-040.json`, four build logs, and per-build performance/telemetry files. Check results are retained in `logs/check-040.txt`.

## Next natural frontier

The new loss is explicit: once the first power carries, every later exponent below the old cutoff is charged, even when it does not carry. A base-sum API expressing the envelope through its full exponent-interval weight would make this loss easier to estimate without a quadratic label carrier. The useful next quantitative question is an independent aggregate bound on the active bases, rather than evaluating every later carry bit or the exact maximum target valuation. For bases with p^2>2*n the first test is the square-power test; a quotient k gives the intervals n^2 < k*p^2 <= n^2+2*n. Their integer endpoint geometry may support a weighted interval-count bound, while the smaller bases retain their full exponent multiplicity. That is an implementation proposal suggested by this result, not an additional result proved here.

The remaining universal obstruction is proving a strict total criterion against Q for arbitrary n. The sampled improvements do not solve that problem, and a cofactor or lcm restatement of exact active valuations would not itself supply an independent estimate. The central-binomial conjecture stays parked; singleton prime fibers were not reopened.
