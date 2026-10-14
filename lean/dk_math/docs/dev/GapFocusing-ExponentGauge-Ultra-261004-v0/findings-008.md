# Instruction 008 findings

## Source checkpoint

Baseline `a8d0be1e6`, with007 committed as `6362ea935`; working tree initially clean. Exact live names/types are recorded in the inventory probe before adding abstractions. The instruction's `ParitySafePrimeSupport` module does not exist in this checkout: `Legendre.Basic` contains `squareOffsetPrimeSupport`, `ParitySafeActiveCapacity` contains the odd active-prime set, and `ParitySafeIncidenceBalance` contains the actual parity-safe support. These live providers are audited instead.

The existing support excess is exactly the sum of `activeSupport.card - 1` over actual candidates. Subset-of-sum monotonicity suffices for local certificates; no new ledger is needed. The prime/wave incidence count,007 cap and deficit identities remain the starting objects. Conditional temporal excess is not an unconditional local certificate.

## Implementation targets

1. Neutral finite-set two-exclusion inequality, then odd quotient specialization.
2. Pair cap folded over distinct odd anchor-prime pairs, initialized with007's cap, so the new cap is automatically no larger.
3. Candidate-seat subset certificates and independently checked finite support witnesses.
4. Mandatory shell29 and bounded shell classification, retaining failed criteria and exact scope.

## Checkpoint: two-prime cap

The neutral finite-set theorem and its odd quotient specialization build. The inequality retains the intersection credit before subtracting both divisor counts: `card ≤ O+Δ_de−(Δ_d+Δ_e)`. A finite minimum over off-diagonal actual odd-anchor-prime pairs is initialized with007's wave cap. Shell bounds `I≤B2≤B` build, without actual wave evaluation. A structural boundary theorem proves B2=B when the anchor has at most one distinct odd prime factor.

## Initial bounded diagnostics (arithmetic exploration, pending kernel regression)

The range2..100 has at most two distinct odd anchor prime factors. With a budget of at most two distinct candidate seats, and at most three distinct witness primes per seat (total certified excess≤4), the predicted classes are59 zero-excess successes,10 local-certificate successes and30 unresolved. The prime29 calibration chooses exactly seats14,56. Two-prime exclusion predicts that all six007 residual waves become exact and the main cap drops425 to418. Prime anchors have no pair exclusion; prime powers and2^a p^k have the same structural limitation.

The class “at least two odd prime divisors implies B2<A” already fails at77 in this bounded search. Even the two-seat budget fails at91. These are failures of sufficient providers, not failures of prime existence.

## Checkpoint: reusable local certificate and mandatory shell29

The new excess-certificate production module builds. A finite candidate subset and lower local costs embed into the existing `support.card−1` sum. A witness-prime-set version and a two-distinct-seat version are proved, followed by Nat-safe pair-cap deficit/nonempty/prime consumers. Distinct witness primes within a seat and distinct seats in the sum prevent double charging.

Shell29's exact candidate memberships and witness prime sets{3,5,19} at14,{3,13,23} at56 are checked against all actual production conditions. Each support has cardinality at least3 and pays excess at least2; the two-seat theorem proves4≤E29 without evaluating the whole excess. B2=31,A=28 then yield U29≥1 and a prime strictly between841 and900. These regression theorems build.

## Checkpoint: six-wave audit

All six previously loose caps now equal their recorded actual wave cardinalities. The structural main cap is418, down from425, and shell21 cap is6, down from7. The structural cap proof uses only floor and divisor data even where its numerical value happens to equal the old actual incidence. Actual wave cardinalities occur only in diagnostics.

The pair cap must not be asserted exact for arbitrary anchors: at n105,q19, exclusion of3 and5 alone gives4 while actual wave cardinality is3; the additional anchor prime7 still excludes a quotient. This kernel-checked example preserves the distinction.

## Checkpoint: bounded classification and arithmetic-class audit

All99 caps/candidate values, the59/10/30 partition, ten pairs of local three-prime support witnesses, and each positive hybrid criterion are kernel checked. All69 successful shells have uncovered and prime consequences. All30 unresolved shells satisfy B2≥A+4, so no certificate within the specified excess budget≤4 can close their sufficient criterion. This is a provider obstruction, not a proof that the shells lack primes.

With the same certificate budget, cap refinement gains shells77,85,95: the unresolved set shrinks33 to30. The success is modest and finite. Of the remaining30:13 anchors are prime,15 have shape2^a p^k, one is64=2^6, and one is91=7*13. Odd prime powers all succeed in this range;49 needs local excess. Prime31, pure power32 and mixed38,52 also demonstrate that local excess can compensate for no pair exclusion.

No unconditional infinite arithmetic class of prime-existence providers is established. The natural two-odd-divisor zero-excess class has checked counterexample77, and the bounded two-seat variant has counterexample91. A reusable infinite *limitation* theorem is established: for every prime p and exponents a,k, `B2(2^a*p^k)=B(2^a*p^k)`, including zero exponents. The missing general lower provider is described precisely in report008.

## Final acceptance and decision

The final focused/facade/root build passes with10378 Lake jobs, including replays. All20 new public production declarations and36 new named regression/data declarations are audited, together with21 existing public declarations in the changed upper module:77/77 complete dependency sets contain only the standard axioms. Forbidden-token, tracked/new-file whitespace and local document-link checks pass.

Outcome A: shell29 is proved by an independent local excess certificate, a strictly sharper reusable cap is added, and the finite fixed-budget provider gains77,85,95. No uniform prime provider is claimed. The final report records all ten requested answers and next development proposals.
