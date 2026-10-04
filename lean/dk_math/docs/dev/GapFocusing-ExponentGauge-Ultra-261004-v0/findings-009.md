# Instruction 009 findings

## Initial source audit

Baseline `cfd1d5f12`,008 implementation `b88687d79`; initial tree clean. Exact types are recorded in the inventory before implementation. The named `ParitySafePrimeSupport` source is absent as in008: `Basic`, `ParitySafeActiveCapacity`, and `ParitySafeIncidenceBalance` provide the actual support interfaces and are audited instead. The Primitive facade and existing block/reduced-residue identities remain unchanged.

`sum_witness_support_excess_le_supportExcess`, `paritySafeUncovered_nonempty_of_local_witnesses`, and `exists_prime_squareCell_of_local_witnesses` already have the requested arbitrary finite-seat-set shape. Reuse them, rather than create a new certificate/excess ledger or a required-charge definition.

## Planned separation

- Prove mandatory41/91 from three actual candidate seats and specified prime subsets.
- Congruence-to-support transport is independent of finding a candidate.
- A positive residue representative in one period is neutral arithmetic. Adding parity doubles the odd-prime product period. Coprimality to the anchor remains a separate obligation for general anchors.
- For a prime anchor, positivity, a strict window bound and an odd shell point exclude the only possible anchor multiple. This suggests a reusable prime-anchor witness provider, to be proved rather than inferred from numerical scans.
- New Lean files use the standard copyright/import/file-print header, including generated data and inspection probes.

## Checkpoint: mandatory41 and91

The mandatory regression builds. Actual candidate memberships and each witness prime's full active-support conditions are checked, without computing whole-shell incidence/excess. The existing finite witness-subset sum proves E41≥6 and E91≥6. Cap/candidate pairs44/40 and76/72 yield U≥2 in both shells, then primes in(1681,1764) and(8281,8464).

## Checkpoint: congruence and short-period construction

The support direction uses `point ≡0 modq`, avoiding truncated Nat subtraction as a negative residue. A neutral positive-residue lemma handles zero residues by using the period itself. An odd-prime product can be combined with modulus2 through Mathlib's CRT; the resulting positive offset is at most twice the product. General anchors still require a separate coprimality proof.

Smallest counterexamples found in the bounded search2..30: n6,Q={5}, product5 fits the window but the unique parity-compatible hit9 is not anchor-coprime; n11,Q={3,7}, product21 fits22 but the only raw hit5 has the wrong parity. These failed candidate/window assertions will be kernel checked.

## Checkpoint: adaptive charge discovery (before kernel validation)

The bounded budget is three distinct seats and at most three witness primes per seat. Of the previous30 Class2 shells, predicted new successes are41,43,56,91 with charge5 and44 with charge6. A triple is truncated to a two-prime subset when charge5 suffices. Mandatory41/91 retain their separate full charge6 certificate. Every remaining25 shell has three actual multi-support witness candidates supplying6, but its required charge is at least7. Thus the search finds enough seats to exhaust the stated budget; it does not establish that no larger certificate exists.

## Provider design checkpoint

Different witness sets do not certify different seats; a regression realizes{3,5} and{3,23} at the same seat44 of shell41. Indexed aggregation therefore takes an injective actual-seat map. For a prime anchor, one parity CRT solution can instead generate distinct offsets r+2m*j. The proposed counted family has floor((n−1)/m) seats, all in the strict window, and charge floor((n−1)/m)*(Q.card−1). This supplies a quantitative infinite-class provider while leaving the hybrid demand inequality separate.

## Checkpoint: successful generic CRT and family proofs

The CRT production module builds without warnings. Congruence/product transport, positive period endpoints, parity-adjusted existence, prime-anchor automatic coprimality, the indexed injective-seat aggregation and its adaptive prime consumer are proved. The prime-anchor same-modulus lift family is also proved with counted charge floor((n−1)/m)*(Q.card−1)≤E. The family theorem permits an empty range if the period is too large; it does not force charge from a long period.

For any prime n>105, Q={3,5,7} gives a candidate and excess≥2. This is an infinite arithmetic class of certificate providers, not a square-cell prime theorem for every such n. Demand may exceed the supplied charge.

## Checkpoint: charge6 diagnostic validation

Kernel checks cover all30 previous Class2 shells, their at-most-three-seat witness families, exact local charges, the4/1/25 partition, all five successful uncovered/prime conclusions and all25 budget obstructions. Survivors have actual certified excess≥6; every e≤6 fails the sufficient incidence-deficit criterion. All25 survivor anchors have at most one distinct odd prime factor, so008's general B2=B limitation applies.

## Final implementation and validation checkpoint

The final combined focused/facade/root build succeeds with10383 jobs. The CRT regression now checks positive zero-residue endpoints, parity and coprimality counterexamples, witness-set seat collision, prime107's actual short-period candidate and insufficient charge2 criterion, prime211's distinct lift seats and generic charge4, and the indexed41 prime consumer. The211 finite primality check required a scoped recursion-depth setting; no proposition was weakened.

The new declaration manifest covers19 production theorems and47 regression/data declarations. Complete axiom-set inspection, source/whitespace/header and document-link checks are recorded in [validation](validation-009.md). All written Lean files retain the requested import-following module print. The root build's existing research admissions are outside the dependency sets of the new results.

The precise missing uniform provider, all25 survivor demands, arithmetic classes and next bounded/collision/mixed-anchor proposals are recorded in [report](report-009.md). Quantitative prime-anchor CRT families advance the provider, while demand sufficiency remains unproved.

Outcome A — ADAPTIVE CERTIFICATE PROVIDER ADVANCES
