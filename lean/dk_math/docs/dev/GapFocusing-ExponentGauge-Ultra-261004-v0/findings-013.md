# Findings 013

## Source checkpoint

instruction-013 is the bounded acceptance document for the requested implementation. The live checkout was clean. Instruction012 endpoints are present and will be reused. No AGENTS.md was found in the workspace.

- `mem_uncovered_iff_no_activeSupport`: existing uncovered object, all n.
- `roughWave_sum_eq_support_sum`: exact full rough incidence.
- `canonicalRootTail_card_eq_rough_support_sum`: erased multiplicity k-1.
- `sqrtCutoff_support_card_le_three`, `sqrtCutoff_power_four_gt`: independent cutoff and fourth-power threshold.
- `Internal.upperPairs`, `card_upperPairs_eq_choose`: unordered pair representatives.
- Mathlib `Finset.card_eq_three`, `Finset.card_powersetCard`: triple combinatorics sources.

Implementation and verification checkpoints follow below.

## Empty class and local algebra

`rough_empty_eq_uncovered` is public for every cutoff P. The two neutral identities use kernel finite cases k=0,1,2,3; the support bound is explicit. The neutral module and `ParitySafeSqrtRoughMoments` passed focused compilation.

## Global conservation and consumer

`sqrt_rough_moment_balance`, `sqrt_tail_moment_balance`, exact card/nonempty iff, recovered margin, covered-seat balance, and `prime_squareCell_of_sqrt_moment` passed compilation. All conservation equations are Nat-safe additions. The prime consumer needs n>0, while combinatorial identities include n=0.

## Bounded discovery

Independent Python scan of all 430 prime anchors <=3000 (last2999) found no direct-failure/moment-success anchor. Required211,503,1009,1013 and additional1019 have positive moment margins. This is discovery only until the numerical calibration bridge is checked; no uniform direct-rough sufficiency follows from the scan.

## Incidence and product-wave bridges

`roughPairIncidences_card` realizes M2 on (r,(p,q)), p<q. `sqrt_roughTripleIncidences_card` realizes M3 on (r,(p,q,s)), p<q<s. Local `upperTriples` needs only support.card<=3; outer active triples have no cardinal restriction. The generic regrouping, exact product-divisibility fibers, and sqrt period bounds compiled successfully. Raw pair occupancy<=2 and triple occupancy<=1 hold for every anchor without hidden tiny-n assumptions.

## Exact factorization checkpoint

The triple quotient is positive and <sqrt(n)+1. Any nonunit quotient has a prime divisor <=sqrt(n), contradicting actual candidate roughness including anchor coprimality and parity. The exact equality `sqrt_roughTriple_point_eq_product` compiled. Two-support quotient is <L² and is either1 or a prime <=n, with actual support membership; `sqrt_two_support_classification` compiled. No counterexample occurred. A subsequent refinement excludes the squarefree pq case because both active labels are <=n.

## Strict triple cost refinement

`sqrt_roughTripleWave_card_eq_product_indicator` and `sqrt_roughTripleMoment_eq_product_count` compiled: M3 counts actual active triple products in the open/lower, closed/upper shell, rather than all raw multiples. The false raw odd/coprime hit (n,r,p,q,s)=(503,106,23,31,71) has point=5*p*q*s and rough cost0. This will be a kernel regression using the product indicator theorem.

## Local implementation repairs

Explicitly typed finite-product sum functions avoid rw matching and metavariable expansion in Mathlib's new product API. Nat.Coprime uses `mul_dvd_of_dvd_of_dvd`, not the nonexistent mul_dvd field. Formatting repair preserved the tactic spelling `decide +kernel`. These were elaboration/local formatting failures, not changes to theorem statements.

## Sharper pair occupancy checkpoint

`candidateProductWave_card_le_one_of_anchor_lt` uses even-separated odd candidate points and m>n to prove card<=1. `sqrt_roughPairWave_card_le_one` inherits it. This improves the proved raw pair bound2 uniformly, without a prime-anchor hypothesis. Focused production compilation passed with no warnings after the local repairs.

## Calibration and structural endpoints

All five actual active inventories, cutoff sets, sqrt-rough cardinalities and moments passed kernel reduction. `moment_inputs_checked` proves the normalization maps; `recovered_uncovered_checked` derives U from global conservation. Generic product-wave sums are instantiated at all five anchors. `checkpoints_prime_from_moments` uses the product moment consumer to prove each square-cell prime, including1019. Counts are cached in their separate module; final calibration/regression build passed9053 jobs with no new warnings.

The k=4 failure, n=0, sharp triple19, both two-support repeated-prime branches13/29, and strict raw/candidate versus rough triple regression503 are checked. No failed quotient classification or arithmetic counterexample occurred.

## Final validation and judgment

Production build passed9048 jobs; facade passed9083 jobs; DkMath root passed10386 jobs. The complete manifest has96 new public declarations: production66, numerical calibration/bridges/regressions30. Every #check/#print axioms record is covered; only propext, Classical.choice, Quot.sound occur. Nine written Lean files have consistent headers/import-adjacent markers. Forbidden-token and tracked/newfile whitespace scans passed.

Root build replays five pre-existing out-of-scope placeholder warnings; none is in the96 dependency sets. The final report answers all ten questions and isolates the remaining uniform singleton arithmetic provider.

Outcome A — ROUGH MOMENT BALANCE ADDS QUANTITATIVE LEVERAGE

A is justified by uniform parity pair occupancy1 and exact actual-triple-product cost with a strict finite raw-wave overcount regression. No direct-failure prime was found among430 prime anchors<=3000; finite direct success does not prove a uniform comparison.
