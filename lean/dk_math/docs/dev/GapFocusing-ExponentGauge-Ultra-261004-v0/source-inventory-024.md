# Source inventory 024

The checkout is clean after the committed 023 implementation.

- CoarseTownPrimeHandoff exports unique maximum/minimum predicates, represented/extremum and missing/deleted equivalences, signed-gap and uniform branching regressions. Reuse these endpoint semantics.
- CoarseTownRetainedDirections and CoarseTownSymmetricDeletion export exact disjoint remainder partitions and both loss decompositions. CoarseTownDeletionConservation exports the actual continuing witnesses and deletion/multiplicity equivalence; the right witness API is its mirror.
- CoarsePrimeWorldFullTown exports coarseFullTown_subset_squareOffsets and coarseFullTown_survivor. Basic exports actual prime support membership and square-offset arithmetic. Preserve the strict shell endpoint.
- PrimorialUniverse.FinitePrimeSynchronization exports finitePrimeBasisProduct_dvd_of_commonMultiple. IsFinitePrimeBasis is pointwise primality; finitePrimeBasisProduct is definitionally Finset.prod id. This is the chosen common-multiple bridge.
- PrimitiveSet.RealLog exports natProductDvdOn_of_pairwise_coprime_dvd and natProductBoundOn_of_pairwise_coprime_dvd. They are valid alternatives but importing its real logarithm layer is unnecessary.
- Mathlib already exports Finset.pow_card_le_prod with an arbitrary pointwise base and function. No new FinsetProductBounds module or duplicate induction is needed. Finset.prod_union and card_biUnion cover the exact support product and endpoint partitions.
- Petal.ABCBridge contains petal_two_pow_card_le_prod_of_two_le. It duplicates a special case of the Mathlib generic inequality; no Petal import is added.
- Nat.log has le_log_of_pow_le and exact power adjunctions, but an explicit power threshold suffices. No logarithmic gauge or StructuralArithmetic.PowerGauge is needed.
- Existing rough sqrt-factorization strata require their own rough-carrier hypotheses. A general full-town support product does not imply those hypotheses or valuation-one factors.
- No existing terminal-source carrier indexed by a deleted extremum seat was found. Add one application carrier and a compact minimum mirror using the same finite subset/product lemmas.

Diagnostic boundary: the 602 prior worlds include nonempty odd bases excluding
prime 2 from S. Such S is not primeScalesUpTo(P). Record that distinction explicitly;
the initial cutoff lower bound must not be applied to the odd worlds. An
orientation-independent base 2 bound remains valid for their actual supports.

Comparison to investigate: a support-card power bound cannot exclude any
actual support already present. If a size threshold supplies support.card<=k,
its single-continuation source capacity k-1 is at least support.card-1.
Formalize this comparison before claiming a new global loss frontier.

Distinct-prime refinement audit searched PrimorialUniverse and the Primitive
and StructuralArithmetic prime-world sources for first/smallest/eligible
prime and order-statistic products. Existing first-hit transport is about
seats, not ordered eligible primes. Mathlib.Data.Nat.Prime.Nth supplies prime
enumeration, but no new enumeration layer is added solely for this checkpoint.
The simple existing pow_card_le_prod baseline meets the required scope.
