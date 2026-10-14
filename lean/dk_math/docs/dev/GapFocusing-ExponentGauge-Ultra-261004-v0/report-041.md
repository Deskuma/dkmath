# Instruction 041 report

Outcome B. The 040 label envelope was reindexed exactly by prime base, and then bounded by a genuinely broader endpoint envelope: small-prime activity is discarded, while large-base primality is discarded. The large contribution is a scalar sum over integer square-root endpoints, with at most one integer base per quotient. This bound is looser than 040 but simpler to evaluate and still useful in the retained total-budget diagnostics. No universal strict criterion or new unconditional prime-existence range was proved.

## Exact base receiver and source audit

The implementation is [GnomonRepeatedBaseAggregate.lean](../../../DkMath/NumberTheory/Legendre/GnomonRepeatedBaseAggregate.lean), exported by the Legendre facade. For any integer base p, define

    A(n,p) = [max(2, Nat.log p (2*n)+1), Nat.log p (n^2)].
    W(n,p) = card(A(n,p)) * log(p).

Natural interval cardinality handles empty intervals. The exact prime-base receiver is

    R_phase(n) = sum over prime p in [2,n] with the 040 first-power gate active
                   of W(n,p).

The equality is kernel checked for n>=3. Its proof filters out the zero von-Mangoldt weights at non-prime-powers, partitions prime-power labels by base, proves different prime-base power images disjoint using minFac, and transports the existing 040 exponent-interval weight theorem. The bound p<=n follows from exponent>=2 and p^a<=n^2.

This equality is infrastructure only. The quantitative change is the broader aggregate carrier below. No exact later carry bits are used in either its definition or its diagnostic reconstruction.

The audit reused 040's phase carrier and interval weight, the next-multiple packet and cofactor cutoff, and GnomonCarryFiber's large-divisor carry/uniqueness machinery. Mathlib's finite disjoint-union/image sums, natural square-root endpoint equivalences, and log monotonicity/power identities were inspected and used. No unproved prime-distribution result was imported.

## Natural split and the independent endpoint envelope

For p^2<=2*n, retain every prime base p in [2,n], whether its first power is active or not. Its full weight W(n,p) is preserved. This discards small-base activity without imposing a uniform exponent length.

For p^2>2*n, the first repeated exponent is two. An active prime base has the unique square multiple

    n^2 < k*p^2 <= n^2+2*n,
    k = n^2 / p^2 + 1 in [2,n-1].

Define integer endpoints

    L(n,k) = max(sqrt_floor(n^2/k), sqrt_floor(2*n)) + 1,
    U(n,k) = min(n, sqrt_floor((n^2+2*n)/k)).

The window [L,U] contains exactly the integer bases satisfying p<=n, p^2>2*n, and the displayed square-multiple inequalities. This endpoint equivalence, the active-base route, and the canonical quotient identity are kernel checked. The window has no primality predicate and no carry-bit predicate.

Every quotient window contains at most one integer base. Indeed, if p<q were both in the window, p<=n and n^2<k*p^2 imply n<k*p. The gap k*(q^2-p^2) is at least k*(2*p+1)>2*n, contradicting the shell width. Different quotient windows are disjoint, since any shared integer base would have the same canonical quotient. This is an injective route in the large-square-base region only; it does not apply to or discard the long small-base exponent chains.

Let the aggregate carrier be the union of all small prime bases and all integer quotient windows. The strongest new independent repeated bound is

    repeatedCarryMass(n) <= R_phase(n) <= R_base(n),

where, by a second kernel-checked identity,

    R_base(n) = sum over small prime bases of W(n,p)
                 + sum over k in [2,n-1]
                     if L(n,k)<=U(n,k) then W(n,U(n,k)) else 0.

Thus the large part is a scalar endpoint sum with n-2 possible terms, and requires no enumeration or primality test of active large prime bases. At a nonempty window L=U. It deliberately charges composite bases as well as prime bases, and retains the complete exponent weight even at those composite bases. This is a geometric upper envelope, not an exact active-prime-base restatement.

The small contribution also has the separate proved bound

    smallBaseMass(n) <= sqrt_floor(2*n) * log(n^2).

The proof bounds each prime base's complete interval by log(n^2) and the number of small bases by the square-root cutoff. The production R_base uses the more precise interval sum, not this coarser scale bound. No sublinear bound on the number of nonempty large windows was proved: at-most-one per quotient alone gives only a weak global count. The useful result here is the weighted endpoint envelope and its retained total-budget performance.

## Strict information loss at n=69

The small region contains prime bases 2,3,5,7,11. Its weight is about 16.270164; base 5 is inactive under 040 but deliberately retained here.

The nonempty large windows are

| k | Endpoint base |
| ---: | ---: |
| 2 | 49 |
| 3 | 40 |
| 5 | 31 |
| 10 | 22 |
| 11 | 21 |
| 12 | 20 |
| 15 | 18 |
| 19 | 16 |
| 34 | 12 |

Eight of the nine endpoints are composite; 31 is the only prime endpoint. Their full weighted mass is about 33.551347. In particular, composite base 12 has exponent interval {2,3} and positive weight 2*log(12). The calibration proves its aggregate membership and positive weight, its absence from the exact active-prime-base carrier, and the strict inequality

    R_phase(69) < R_base(69).

This strict overcover is a formal certificate that the aggregate bound discards information. Numerically R_base(69) is 49.821511, versus 14.087380 for 040 and 68.413726 for the 037 band. The new bound is not advertised as a tightening of 040.

## The 2896 multiplicity regression

Base 2 lies in the small region. Its exponent interval remains [13,22], and its contribution is proved equal to 10*log(2). The existing exact fiber at target 8388608 and cardinality 10 are retained. No target quotienting, one-log-per-target estimate, or uniform bound on exponent length is used.

At n=2896, the small-base mass is approximately 139.998979. The large endpoint mass is approximately 620.672451, from 75 nonempty windows, of which 59 have composite bases. The aggregate repeated bound is about 760.671429, compared with 184.362916 for 040 and 3033.326690 for 037.

## Combined correction and quantitative comparison

The new independent correction envelope is

    B041(n) = psi(2*n) - smallPhaseExcludedMass037(n)
                + R_base(n) + higherReciprocalBudget(n).

For n>=3 the kernel proves

    C_ns(n) <= B040(n) <= B041(n),
    Q(n) + B041(n) < log(cell(n))
      -> exists p, Prime(p) and SquareCell(n,p).

This conditional provider retains the exact existing Q term. It introduces no central-binomial premise and no assertion that its strict premise always holds. The stronger 040 provider remains available.

The following are floating diagnostics only. Margin means log(cell)-Q-B; numerical margins are never Lean proof premises.

| n | R_phase 040 | R_base 041 | Band 037 | Margin 040 | Margin 041 |
| --- | ---: | ---: | ---: | ---: | ---: |
| 3 | 0.000000 | 0.693147 | 1.791759 | 4.060161 | 3.367014 |
| 32 | 11.321680 | 21.707594 | 31.910486 | 42.778268 | 32.392354 |
| 69 | 14.087380 | 49.821511 | 68.413726 | 43.094563 | 7.360432 |
| 297 | 37.079292 | 125.536137 | 318.035599 | 228.067937 | 139.611092 |
| 1031 | 107.338042 | 376.925955 | 1087.055997 | 1233.889193 | 964.301279 |
| 2896 | 184.362916 | 760.671429 | 3033.326690 | 2774.263347 | 2197.954834 |
| 5000 | 147.922125 | 1055.348827 | 5193.783679 | 5231.994013 | 4324.567310 |

The diagnostic sample is n=3..300 plus 1031,2896,5000: 301 points. All have positive 041 margins. R_base is not uniformly below the old band even in this sample: it exceeds the 037 band at n=15,22,26,29,31. No universal inequality R_base<=band is claimed. The required large anchors do retain substantial savings against the old band and useful positive total margins. The small anchor n=3 has empty repeated carry but a harmless log(2) small-base overestimate.

`logs/diagnostics-041.json` retains every anchor window and small-base interval. All endpoints, canonical quotients, singleton window cardinalities, exponent lengths and multiplicities use exact integer arithmetic. Log weights and margins are floating diagnostics; the retained 040 source artifact is linked by SHA256. No primality test is performed on large bases to select the aggregate carrier; diagnostic prime flags only record how much information the bound discards.

## Validation

The production module contains eight definitions, twenty public theorems and two private proof helpers. All 28 public declarations are covered by the axiom audit; both helpers are checked through the audited dependency closure. The calibration contains ten kernel-checked regressions, covering composite extra mass, inactive small bases, required-anchor windows, the ten-exponent interval, the existing fiber, and the trivial anchor.

The two fixed n=69 aggregate calibration proofs use a local maxRecDepth of 4096 for elaboration of the concrete finite carrier. Production proofs retain the default recursion setting. Earlier focused attempts exposed elaboration recursion-depth limits; those were proof elaboration limits, not memory failures, and were resolved without changing theorem statements or adding assumptions.

The source audit covers four touched Lean files: the three new modules and the modified facade. Standard headers and immediate import-following file markers are retained. Forbidden proof constructs, axiom coverage, diagnostic reconstruction, build artifacts, ASCII documents/logs and git diff whitespace are checked by `checks/check-041.py`.

| Build | Exit | Seconds | Maximum RSS (MiB) | Swaps |
| --- | ---: | ---: | ---: | ---: |
| focused | 0 | 13.036 | 6617.4 | 0 |
| axiom-audit | 0 | 12.607 | 6567.4 | 0 |
| facade | 0 | 12.416 | 6587.9 | 0 |
| root | 0 | 14.885 | 6919.7 | 0 |

All four final builds used LEAN_NUM_THREADS=4, completed successfully, and retained GNU time telemetry. These are incremental invocations including import replay, not clean-build performance measurements. No memory failure or swap was reported by the measured processes. The largest recorded RSS was about 6.76 GiB; telemetry is process resource usage, not a whole-machine memory survey.

All audited declarations depend only on a subset of the standard logical axioms propext, Classical.choice and Quot.sound; there is no sorryAx or new axiom/oracle. Focused, facade and axiom logs contain no warnings. Root succeeds with five existing sorry warnings in ZsigmondyCyclotomicResearch, TriominoCosmicBranchA, GcdNextResearch, CyclotomicPrincipalization and TriominoFLT, all outside touched sources. No whole-repository sorry-free claim is made.

Reproduce from lean/dk_math:

    python3 docs/dev/GapFocusing-ExponentGauge-Ultra-261004-v0/checks/diagnostics-041.py
    python3 docs/dev/GapFocusing-ExponentGauge-Ultra-261004-v0/checks/build-041.py focused axiom-audit facade root
    python3 docs/dev/GapFocusing-ExponentGauge-Ultra-261004-v0/checks/check-041.py

Artifacts are retained as `logs/coverage-041.json`, `logs/diagnostics-041.json`, four build logs, per-build telemetry/performance files, and `logs/check-041.txt`.

## Stopping decision and next natural frontier

Further local correction refinement should stop here. The 040 envelope is already uniformly at least as strong as this endpoint aggregate, and already passes all retained numerical correction tests. The new result answers the aggregate question by simplifying the large-base test to integer endpoint geometry and preserving the small-base multiplicity; it does not justify another hierarchy of phase exclusions.

The remaining frontier is independent control of Q, or a lower bound on the available total margin log(cell)-Q strong enough to pay the already proved correction. A useful next implementation proposal is a receiver for that aggregate available margin, connected directly to the exact cofactor-window Q sum and the existing conditional provider, followed by research into an independent quantitative estimate from those windows and factorial/log-product geometry. Merely renaming the exact available margin is infrastructure, not progress; a new estimate must discard exact prime inventory and prove a useful inequality. This keeps the problem at the aggregate total-budget level rather than restarting singleton factor-depth classification.

No new density estimate for occupied square windows or universal total strictness has been proved. The central-binomial conjecture stays parked, and the singleton factor-depth route was not reopened.
