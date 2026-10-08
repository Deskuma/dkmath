# Instruction 039 report

Outcome C. One canonical pooled principle was investigated and formally refuted: cumulative residual prime-base products above every size threshold. At n=27 the threshold-8 left pool exceeds the corresponding right pool, although the full product comparison still holds. This is a counterexample to the investigated pooled principle, not to the original central-binomial conjecture. No new unconditional small-carry bound or correction envelope is claimed.

## Principle actually investigated

For a finite residual-coordinate set S and a threshold t, define

    P(S,t) = product of minFac(d) over d in S with t <= minFac(d).

The proposed capacity principle at fixed n is

    P(small-only,t) <= P(central-only,t)
      for every integer t in [2,2*n].

This pools all bases above the cutoff; several right factors may jointly pay for a left factor, and excess from a larger right factor may pay for several smaller left factors inside that pool. It imposes no equal-cardinality matching or divisibility. Prime-power coordinates remain distinct even when their bases coincide, so exponent multiplicity is preserved.

The rule is canonical and independent of comparison success: both pools are determined only by the residual carriers from 038 and the contributed base-size cutoff. No partition is chosen by searching until products satisfy the target, and the rule never queries Q, shell-prime existence, oldBudget strictness or computed total products. The diagnostic computes products to test the fixed rule; those results do not choose its pools. No manual calibration blocks or tunable hierarchy are introduced.

Existing finite combinatorics was inspected before implementation. The proof uses Mathlib's exact filtered-product partition identity. List sorting/prefix APIs were inspected as candidates, but only the thresholded cumulative-product principle was pursued. No second heuristic or arbitrary-binomial framework was added.

## Formal API and exact currency

The production module [GnomonPooledThresholdAudit.lean](../../../DkMath/NumberTheory/Legendre/GnomonPooledThresholdAudit.lean) exposes two definitions and four theorems. It proves the exact high/low split

    product(S) = P(S,t) * product over minFac(d)<t.

For prime-power carriers, P(S,2) is the full contributed-base product. Thus the threshold-capacity hypothesis implies the 038 residual-product inequality by its threshold-2 instance; the existing positive-product bridge then yields smallCarry <= log choose(2*n,n).

This sufficient receiver is explicitly conditional. Its threshold-2 assumption already includes the total-product comparison, so the receiver is logical infrastructure, not a new compensation proof. The mathematical conclusion of this checkpoint is the counterexample to the proposed uniform family. Real logarithms are introduced only by transport through the existing 038 bridge, after the natural-product reasoning.

## n=4 and n=27

At n=4 the residual bases are left {3}, right {5,7,2}. The calibration proves that all threshold capacities hold. At threshold 2, 3<=70; at threshold 3 the right pool is 5*7=35 and still pays for 3. The small-carry central bound at this finite anchor follows from the conditional receiver. The original pointwise counterexample and 3 not dividing 70 are retained unchanged.

At n=27 the exact residual bases are left {5,11,19,23}, right {2,2,2,7,7,47,53}. The same canonical rule gives at threshold 8

    left high  = 11*19*23 = 4807,
    right high = 47*53    = 2491,
    left low   = 5,
    right low  = 2^3*7^2 = 392.

The production theorem kernel-checks the high products and proves the threshold-capacity principle false at n=27. The calibration separately checks the low products and retains the full comparison

    4807*5 = 24035 <= 2491*392 = 976472.

Therefore the lower pool carries surplus that must cross the cutoff to pay the upper deficit. Threshold segregation loses precisely the compensation needed here. The high-product weighted defect is log(4807)-log(2491), about 0.657389, while the full inequality remains favorable. The thresholds 8 through 11 fail in the bounded diagnostic; they have the same high-coordinate pools.

The 038 no-dominating-injection theorem at 27 is retained as a calibration. The new obstruction is different: even pooled high-base products, without one-coordinate matching, fail their uniform capacity condition. This does not rule out disjoint cross-threshold blocks. It shows that such blocks must move credit across base-size classes and need an independent arithmetic transfer rule. The informal calibration grouping is not hard-coded into the implementation.

## Universal target and budget interpretation

The universal total comparison L(n)<=R(n), hence the central-binomial small-carry bound, remains unresolved. Refuting a sufficient threshold family cannot refute its weaker total comparison. The negative theorem is deliberately scoped to the investigated principle.

No substantially corrected uniform product inequality or independent cross-threshold error bound was obtained. Defining an error from the exact failing pool products would merely rename the open target, so no such correction is introduced. The strongest proved small-carry bound remains the 037 phase-prefix bound psi(2*n)-E_037, and the applicable independent correction envelope remains B_phase_037<=B_036. Existing repeated-large band and reciprocal higher correction are unchanged. No B_central provider or new unconditional prime-existence range is added, and the closed singleton factor-depth campaign remains closed.

## Bounded diagnostics

The diagnostic independently constructs the two residual prime-power carriers and checks every integer threshold in [2,2*n] using exact integer products. It covers n=3..300 plus 1031 and 5000, 300 samples. It records the 038 source SHA-256 for the retained budget coordinates. All sampled total residual-product comparisons hold. Exactly one sampled n fails the threshold principle: 27. This is not a claim that no further threshold failures exist outside the sampled range. The kernel theorem certifies the specific counterexample independently of diagnostics.

| n | every threshold passes in diagnostic | first failed threshold | proved 037 envelope margin diagnostic | hypothetical central envelope margin diagnostic |
|---|---|---|---|---|
| 4 | yes | - | 7.160648 | 4.010765 |
| 27 | no | 8 | 22.477546 | 22.623259 |
| 32 | yes | - | 22.189462 | 24.973217 |
| 69 | yes | - | -11.231783 | -3.808373 |
| 210 | yes | - | 64.626574 | 107.540259 |
| 297 | yes | - | -52.888370 | 10.213420 |
| 1031 | yes | - | 254.171238 | 639.553776 |
| 5000 | yes | - | 186.132458 | 2667.302497 |

The margin columns reuse 038's floating diagnostic interpretation, not a new proof. Hypothetical central compensation would make 297 positive and greatly improve 5000, but still leaves 69 about -3.808373. Since the uniform compensation theorem remains open, none of those hypothetical signs supply a new consumer. The proved 037 envelope still has diagnostic failures at 69 and 297. Correction slack therefore remains separate from Q, and Q is not reported as the sole remaining frontier.

## Validation

Focused production/calibration, complete Legendre facade, root DkMath and axiom audit all pass with LEAN_NUM_THREADS=2. All six new public production declarations are audited; only propext, Classical.choice and Quot.sound occur, with no sorryAx or new axiom. Calibration preserves eight regressions including the 038 pointwise and injection obstructions, exact products, finite pooling at 4, and the high/low split at all retained anchors.

New Lean files retain the unified header and immediate file marker. The forbidden-construct/source audit, ASCII documentation/log audit and git diff --check pass. Timings are incremental measurements, not clean-build performance comparisons.

| Build | Exit | Seconds | Peak RSS KiB | Swaps |
|---|---|---|---|---|
| focused | 0 | 16.42 | 7041164 | 0 |
| axiom-audit | 0 | 13.189 | 6729100 | 0 |
| facade | 0 | 13.216 | 6752328 | 0 |
| root | 0 | 14.088 | 7114508 | 0 |

Focused, facade and axiom-audit logs contain no warnings. The root retains five pre-existing sorry warnings in ZsigmondyCyclotomicResearch:147, TriominoCosmicBranchA:4187, GcdNextResearch:850, TriominoFLT:1919 and CyclotomicPrincipalization:5389, outside the new-declaration audit. No repository-wide sorry-free claim is made. No memory failure occurred.

Artifacts: [source inventory](source-inventory-039.md), [coverage](evidence/MANIFEST.md#log-01e55710cbc243f0), [diagnostics](evidence/MANIFEST.md#log-a0254b04dc3f9cf1), [focused](evidence/MANIFEST.md#log-11ea4ebd1acb780a), [axiom audit](evidence/MANIFEST.md#log-0cc546fb2446777e), [facade](evidence/MANIFEST.md#log-6017ac91057aa383), [root](evidence/MANIFEST.md#log-52e04bb7bfcbb19b), and [artifact check](evidence/MANIFEST.md#log-c2a586da70c32254). Reproduce with checks/build-039.py (focused axiom-audit facade root), checks/diagnostics-039.py and checks/check-039.py.

## Stopping decision and next natural frontier

Stop this threshold-capacity route at its proved counterexample. Do not add exceptional thresholds, enlarge blocks by trial, widen the 037 residue radius, or infer a uniform theorem from the other passing samples. No canonical cross-threshold transfer rule was obtained.

For the central conjecture, the remaining frontier is a genuinely global weighted comparison that accounts for credit flowing across base-size thresholds. A future proof would need an arithmetic allocation rule independent of the desired product comparison; a receiver assuming successful pooling or a product-driven greedy search would not resolve it.

A practical next implementation proposal is to redirect the correction investigation to the repeated-large prime-power band. Audit its existing exponent cutoffs and modular carry phase to seek an independent bound sharper than the full nonprime band. The retained n=69 hypothetical-central deficit shows that this term would still matter even after the central conjecture were solved. Such an estimate should keep its slack separate from the small-carry comparison and Q, without re-entering singleton fibers. This is a frontier suggestion, not a proved improvement or a design for Instruction 040.
