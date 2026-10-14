# Instruction 042 report

Outcome C. Q's exact prime-only floor-pulse bridge and injective target/cofactor representation are now kernel checked. One independent global target-capacity mechanism was investigated. It reduces some previous large-anchor overcovers but is formally incapable of satisfying the 040 strict criterion for every n>=3. The route is stopped for a proved normalization obstruction, not merely an unsuccessful numerical scan. No new unconditional prime-existence result or useful strict Q estimate is claimed.

## Exact Q currencies

The new production module is [GnomonQFloorPulse.lean](../../../DkMath/NumberTheory/Legendre/GnomonQFloorPulse.lean), exported by the Legendre facade. It retains the exact existing cofactor-window definition and proves

    Q(n) = sum over prime p with 2*n < p <= n^2
             log(p) * ((n^2+2*n)/p - n^2/p).

The floor operations and subtraction are natural-number operations; the pulse is cast to the reals only for its log weight. Above the width, the floor difference equals the existing carry bit and lies in {0,1}. The bridge first uses the existing cofactor-window/singleton equality and then extends the active prime-label sum to the full old prime band with zero pulse outside its support.

Primality is explicit in the band. Carrying repeated powers are excluded, and primes born above n^2 are also excluded: both are distinct currencies in the established ledger. Regression tests fix the carrying nonprime label 256 at n=69 and the new shell prime 1031 at n=32 outside Q. This is not an unfiltered von-Mangoldt pulse.

For every Q label p the canonical cofactor and target satisfy

    k = n^2/p + 1, 2<=k<n,
    y = p*k, n^2<y<=(n^2+2*n).

Distinct Q primes have distinct targets. The proof reuses the existing same-base theorem for two large prime-power divisors with both exponents equal to one. Thus it couples all quotient windows through one shell target carrier. Its prime-only hypothesis is essential: the old ten-exponent repeated-power fiber at n=2896 is retained and is not claimed to be injective.

The natural selected-product identity is also proved:

    product of Q primes * product of their cofactors
      = product of their canonical targets.

For n>=3 the target injection allows the indexed target family to be treated as distinct selected shell targets. The product identity alone supplies no independent quantitative saving. At n=3 the kernel calibration fixes the three products as 7, 2 and 14.

## Aggregate mechanism investigated

The entire quotient-index family [2,n-1] is treated as one global capacity family. No dyadic partition, per-window binomial bound, finite wheel, adaptive factor-depth test or favorable prime subset is used to define the new upper envelope.

Every selected cofactor is at least two, hence

    log(p) = log(y)-log(k) <= log(y)-log(2).

Injectivity prevents different quotient windows from charging the same target. The selected target sum is bounded by the complete endpoint shell sum, whose summands are nonnegative for n>=3. This proves the independent bound

    Q(n) <= U_target(n),
    U_target(n) = sum over y in [n^2+1,n^2+2*n] of (log(y)-log(2)).

U_target uses ordinary integer endpoints and a universal cofactor lower bound. It does not use Q, any prime filter, actual target occupancy, shell prime birth, later carry bits, or strictness in its definition. It is genuinely an independent upper bound, but the whole-shell capacity is too broad to be a useful strict provider.

## Exact obstruction and stopping theorem

The existing Pascal factorial identity yields the new exact identity

    U_target(n) = log(cell(n)) + log((2*n)!) - 2*n*log(2).

The kernel also proves

    2^(2*n) <= (2*n)! for n>=3.

Consequently,

    log(cell(n)) <= U_target(n) for n>=3.

The existing nonnegative exact correction and its 040 bound imply B040>=0. The final route-stopping theorem therefore proves

    not (U_target(n)+B040(n)<log(cell(n))) for every n>=3.

This is a theorem about the tested capacity envelope. It is not a counterexample to the exact Q criterion or to Legendre's conjecture. The exact Q+B040 diagnostic remains positive at all retained sample points. The failure already occurs before charging any nonnegative correction, so reopening local correction refinement cannot rescue this envelope.

The precise loss is the factorial normalization penalty log((2*n)!)-2*n*log(2), plus B040 in the strict comparison. An improvement would need independent weighted information about unoccupied shell targets and/or cofactors beyond the universal lower bound two. Selecting targets by the exact Q inventory, or assuming the required cofactor credit, would merely reconstruct the desired inequality and is not an independent estimate.

No new provider based on U_target is exposed, because its premise is proved impossible. The strongest proved useful correction consumer remains the 040 consumer.

## Comparison with 030/031 and retained diagnostics

All values below are floating diagnostics, not Lean premises. The margin is log(cell)-U_target-B040. The stronger 040 correction is used throughout; the deliberately looser 041 correction is not substituted.

| n | Exact Q | Proposed U_target | B040 | log(cell) | Proposed margin |
| --- | ---: | ---: | ---: | ---: | ---: |
| 32 | 135.995020 | 401.242672 | 61.662604 | 240.435892 | -222.469384 |
| 69 | 460.234053 | 1074.954322 | 121.935840 | 625.264455 | -571.625707 |
| 210 | 1750.287269 | 4202.446930 | 379.536259 | 2372.722503 | -2209.260686 |
| 297 | 2814.032462 | 6354.423237 | 520.133429 | 3562.233828 | -3312.322838 |
| 1031 | 11769.172577 | 27186.215403 | 1933.676333 | 14936.738102 | -14183.153634 |
| 2896 | 39607.813444 | 88324.348784 | 5560.492239 | 47942.569030 | -45942.271993 |
| 5000 | 73428.352340 | 163414.391956 | 9576.589572 | 88236.935925 | -84754.045603 |

| n | 030 geometric Q envelope | 031 sieve Q envelope | U_target |
| --- | ---: | ---: | ---: |
| 32 | 403.778959 | 209.368435 | 401.242672 |
| 69 | 1403.928062 | 781.304375 | 1074.954322 |
| 210 | 7253.895663 | 3870.094432 | 4202.446930 |
| 297 | 11805.854900 | 6296.584440 | 6354.423237 |
| 1031 | 63299.407782 | 33700.728319 | 27186.215403 |
| 2896 | 240200.708389 | 128061.354526 | 88324.348784 |
| 5000 | 477785.348850 | 254694.610119 | 163414.391956 |

The capacity materially decreases the previous large overcovers at 1031,2896,5000, but it still exceeds the available margin by roughly a factor of two. At 5000 its advantage against 031 is about 91280.22, while its remaining strict-budget deficit is about 84754.05. This numerical improvement is not classified as Outcome B: the whole-shell product route is proved useless for closing the criterion, as anticipated by the checkpoint's target-product guard.

The scan covers n=3..300 plus 1031,2896,5000: 301 points, including all seven required anchors. The capacity passes no sampled strict comparison. It is below 030 at 273 points and below 031 at only four points. The largest sampled U_target/M040 ratio occurs at n=38 and is about 2.296592. The first sampled failure is n=3; the separate universal kernel theorem makes scan extrapolation unnecessary.

The exact floor-pulse Q inventory is recomputed from primes in the old band, rather than merely relabeling a stored Q value. Each pulse is checked binary; each target is checked in the shell, each cofactor in [2,n-1], and targets are checked distinct. At every required anchor the quotient-window inventory and the selected-product identity are also checked in exact integer arithmetic. Anchor incidence samples and hashes are retained. Primality is used only for these exact-Q diagnostics, never to construct U_target. Log values and comparisons are floating evidence only.

## CFBRC finite-pulse audit

The audit inspected `DkMath/RH/CFBRC/PascalCenteredXiPrimeSideFiniteTailProjectionAudit.lean` and `CosmicFormulaZetaVonMangoldtPulseCompressionAudit.lean`. The former defines `pascalCenteredXiPrimeSideFiniteModeKernel` as an integral over a transport-window half interval of a Mellin/phase integrand. The latter's CFZP pulse is twice the von-Mangoldt weight times that kernel, with aggregate successor/telescoping laws.

This kernel depends on frequency and complex-transport window data and has no proved identification here with the arithmetic shell's binary floor difference. Its generic mode support and successor decomposition do not supply the missing weighted quotient-window estimate. The implementation reuses the ordinary Mathlib finite-sum and von-Mangoldt facts already available in the Legendre dependency chain. It imports no CFBRC module, RH statement, cofinal sign provider, PNT premise, or compensation contract.

## Validation

The production module contains three definitions, thirteen public theorems and one private nonnegativity helper. All 16 public declarations are axiom audited; the helper is checked through their dependency closure. The nine kernel regressions cover all required-anchor scalar pulses/targets, prime-only support, repeated-power exclusion, shell-birth exclusion, a zero pulse, the tiny selected-product identity, universal capacity failure specialized to the anchors, and the retained ten-power fiber.

The source audit covers four touched Lean files: the three new modules and the modified Legendre facade. Headers and immediate import-following file markers are preserved. Forbidden proof constructs, declaration coverage, diagnostic arithmetic/hashes, successful build artifacts, ASCII documents/logs and git diff whitespace are checked by `checks/check-042.py`.

| Build | Exit | Seconds | Maximum RSS (MiB) | Swaps |
| --- | ---: | ---: | ---: | ---: |
| focused | 0 | 13.836 | 6722.0 | 0 |
| axiom-audit | 0 | 12.384 | 6565.0 | 0 |
| facade | 0 | 12.055 | 6584.7 | 0 |
| root | 0 | 12.936 | 6926.8 | 0 |

LEAN_NUM_THREADS was removed from the subprocess environment for all four final builds. The build runner records null for its value and false for its presence. No actual runtime worker count is inferred from an unset variable. All builds succeeded with no observed memory failure; GNU time reports zero swaps and a maximum recorded RSS of about 6.76 GiB. These are incremental Lake invocations including import replay, not clean-build benchmarks or a whole-machine memory survey. No speedup claim against earlier thread settings is made.

All 16 audited declarations depend only on a subset of the standard logical axioms propext, Classical.choice and Quot.sound; there is no sorryAx or new assumption oracle. Focused, facade and axiom logs contain no warnings. Root succeeds with five existing sorry warnings in ZsigmondyCyclotomicResearch, TriominoCosmicBranchA, GcdNextResearch, CyclotomicPrincipalization and TriominoFLT, outside touched sources. No whole-repository sorry-free claim is made.

Reproduce from lean/dk_math:

    python3 docs/dev/GapFocusing-ExponentGauge-Ultra-261004-v0/checks/diagnostics-042.py
    python3 docs/dev/GapFocusing-ExponentGauge-Ultra-261004-v0/checks/build-042.py focused axiom-audit facade root
    python3 docs/dev/GapFocusing-ExponentGauge-Ultra-261004-v0/checks/check-042.py

Artifacts are `logs/coverage-042.json`, `logs/diagnostics-042.json`, four build logs, per-build performance/telemetry files, and `logs/check-042.txt`.

## Stopping decision and next natural frontier

Stop the investigated whole-target-capacity route here. Its missing factorial cancellation is proved and cannot be repaired by a better local correction bound. The Legendre laboratory now has an exact prime-only weighted floor-pulse/quotient-window receiver and a precise example of why global occupancy capacity alone does not control that weight at the required scale.

The remaining mathematical frontier is a genuinely weighted short-interval or coupled quotient-window theorem. A future implementation proposal is to test an independent aggregate block inequality against M040 before adding any further receiver: its credits must come from a proved endpoint/product or coupled-window estimate, not from the exact prime inventory or a favorable selected target set. Finite summation and endpoint cancellation may supply infrastructure, but reindexing or telescoping alone must not be reported as the missing estimate. Lower certified credits have the subtractable orientation; unrelated global upper bounds or upper bounds on composite error do not.

This report does not predesign another checkpoint or begin a new sieve hierarchy. The unresolved comparison remains Q<M040. The central-binomial route remains parked; the singleton factor-depth and local correction campaigns remain closed.
