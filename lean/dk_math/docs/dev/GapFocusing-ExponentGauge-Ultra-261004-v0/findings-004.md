# Instruction 004 findings

## Checkpoint 1: live source and ledger audit

The existing lower common support is the old support filtered by divisors of `oddGnomon n`. `GnomonPetalTurnover` localizes divisors of this displacement; it supplies no multi-shell count. `Frontier` is a reduction of Legendre to support escape, not a provider.

The parity-safe ledger counts incidences `(candidate offset r, active prime q)` in one shell. Its `paritySafeIncidenceCount_eq_candidate_support_sum` is the exact interface. Support excess sums `support.card - 1`; pair overlap sums `choose support.card 2`; low-cost capacity and depth residual capacity bound separate residual fibers. The actual-fiber cancellation theorem still has incidence on the right side.

Two obstacles to the proposed unweighted count are already visible in the definitions: one prime can support multiple offsets in the same shell, and lower reindexing adds an odd displacement, reversing point parity. Neither an incidence injection into prime-shell events nor preservation of the parity-safe candidate family follows from address spacing. These observations will be kernel checked below.

The fixed-coordinate degree ray from Instruction 003 and the fixed-degree varying-shell residue class are different axes. No global prime-existence claim is being attempted.

## Checkpoints 2-5: checked structural bridge

`CyclotomicPersistence.lean` passes its focused build. The actual integer homogeneous evaluator satisfies `cyclotomicShiftedEval 2 1 n = oddGnomon n`. Lower support membership is old membership and divisibility of that value. Primality forces both coordinates nonzero; for every odd prime the divisibility is equivalent to `primeOrder q (n+1) n = 2`, including the boundary where a denominator divisible by q gives order zero.

The complete natural shell address is `n = (q-1)/2 + k*q`. Repeated addresses are congruent modulo q; consecutive addresses are impossible. Quotient blocks inject the address offsets of any finite run into a range of size `if T=0 then 0 else (T-1)/q+1`, exactly ceil(T/q) for positive q.

## Checkpoint 6: incidence interface implementation in progress

The new lower-sector quantities restrict the existing successor parity-safe candidates and active supports. They split actual active support into its intersection and difference with the full old support. The old parity-safe candidate family is deliberately not used as the persistence reference, because the canonical lower displacement reverses parity. A proposed safe capacity weights prime-shell frequency by the maximal number of lower seats in the run. No reduction of a residual capacity has been established.

## Checkpoint 7: checked weighted bound and exact fresh split

The focused `ParitySafePersistence` build passes. In addition to the shell residue, old point divisibility forces `q | 4*r+1`. Define the fixed seat pool `W_q(M) = {r in [1,M] : q | 4*r+1}`. For a run starting at N of length T, actual lower persistent incidences are at most

`C(N,T) = sum_{q prime <= N+T, q != 2} |W_q(N+T)| * ceil(T/q)`.

This is stronger than multiplying all prime-shell frequencies by N+T: it uses the fixed-seat restriction. The active-support intersection/difference partition gives an exact lower-sector incidence = persistent + fresh identity. Consequently lower-sector incidence minus C is at most lower-sector fresh count. Under the existing full-cover predicate for every successor shell, replace incidence by the number of actual lower candidates to obtain the requested conditional charging inequality.

This remains a sector bound. It supplies no upper bound for fresh incidences and no inequality reducing support excess, pair overlap, low-cost residual capacity, or depth residual pair capacity. The coarse maximal-shell pool also drops both seat parity and coprimality. No strict full-cover frontier gain is asserted.

## Checkpoint 8: checked failures and calibrations

The regression module passes for the shell q=3 progression, ratio order at (11,10), absence in the next shell, arbitrary finite runs including T=0 and a full period. At n=10, q=3 persists at both successor parity-safe seats r=2 and r=8, while the single-transition prime-shell event count is one. The proposed unweighted single-prime incidence inequality is therefore false. Old odd candidate r=1 at n=10 is not an odd successor candidate. The refined capacity at (N,T)=(10,1) is 9, strictly below the crude all-seat value 44; these are the new temporal capacities, not the existing residual-capacity quantities.

## Checkpoint 9: nonzero charging calibration and frontier decision

The twenty-transition regression is kernel checked: `N=20,T=20` has 245 lower successor candidate seats and seat-weighted periodic persistence cap 169. The existing full-cover hypothesis for all twenty successor shells therefore forces at least 76 fresh lower incidences. The full-cover hypothesis is retained; this is not a prime-existence proof.

A second checked regression has a fresh active prime three at successor shell 7, offset 2, while the entire existing `paritySafeSupportExcess 7` is zero. Thus the unconditional candidate inequality charging fresh incidences directly to support excess is false. The main frontier's residual terms have no checked fresh-incidence upper bound. Increasing fresh incidence does not by itself decrease the incidence on the right side of the full-cover capacity inequality.

Decision: Outcome B. The temporal sector bound and conditional lower charging step are new; the existing support-excess/pair-overlap/residual-capacity frontier has not been strictly sharpened. Outcome A would require such a checked strict comparison. Outcome P is not chosen because the incidence partition and containment into the actual candidate-side ledger have now been proved, rather than left as a missing injection.

## Final validation checkpoint

Final focused modules, named regressions, Legendre facade, GapFocusing facade, and DkMath build passed (10368 Lake jobs, including replayed dependencies). The five existing unrelated unfinished-declaration warnings in the full facade build remain outside the new theorem dependencies. The final axiom audit covers 39/39 new public production declarations and 11/11 named regressions; all dependency sets are subsets of the three accepted standard kernel axioms. Changed production and named regression forbidden-token scans have zero matches. Final whitespace/diff checks are recorded in validation-004.md.

Outcome B — EXACT ADDRESS BRIDGE, NO STRICT CAPACITY GAIN
