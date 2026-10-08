# Source inventory 022

Audit before production edits; the checkpoint 021 checkout is clean.

- FinsetSupportPacking: supportPackingRemainder_pairwiseDisjoint, card_supportPacking_partition, supportPackingRightRemainder_pairwiseDisjoint, card_supportPackingRight_partition. No smaller-universe capacity wrapper exists here.
- CoarseTownDeletionCapacity: coarseTownPackingRemainder_family, card_coarseTownDeletion_partition, coarseTownDeletionVertices_eq_fibers. Preserve the 021 old-world consumers.
- CoarseTownSupportPacking: mem_coarseTownSupportCollisionEdges, card_coarseTownPrimeCollisionEdges; reuse the existing collision relation.
- CoarsePrimeWorldVerticalCapacity: coarseFullTownPrimeFiber, coarseFullTownIncidence_eq_support_sum, coarseFullTownPrimeFiber_eq_column_union, card_coarseColumnWaveIndices_le_one. Reuse the exact actual-support incidence transpose.
- CoarsePrimeWorldFullTown: coarseFullTown_survivor, coarseFullTown_subset_squareOffsets, card_coarsePrimeWorldFullTown.
- CoarsePrimorialTown: coarseOutsidePrimes, coarse_survivor_support_outside.
- OldSupportCapacity: card_pairwiseOldSupportDisjointSquareSeatFamily_le_primeScalesUpTo_of_fullyCovered; its disjoint biUnion argument supplies the neutral capacity proof pattern.
- OldSupportCapacityCertificate: squareOffsetPrimeSupport_eq_boundedSquareSupport, oldSupportSeatFiber, checkOldSupportCapacityCertificate_eq_true_iff. Actual divisibility, never imported Python labels.
- Wave: squareCoverOverlapExcess and its full-cover incidence ledger. Carrier is the entire shell, so a local full-town adapter is needed.
- PairOverlap: squareCoverOverlapExcess_le_squarePrimePairOverlapCount. Pair collisions are not deletion multiplicity overlap.
- ParitySafeIncidenceBalance: paritySafeIncidenceCount_eq_candidate_support_sum, paritySafeNonemptyActivePrimes_card_add_duplicateBudgetExact_eq_incidence, paritySafeCoveredCandidates_card_add_supportExcess_eq_incidence, paritySafeIncidenceConservation. These use parity-safe candidates, not fullTown; reuse counting patterns rather than change their semantics.
- Frontier: not_squareOffsetsFullyCovered_iff_escaping_nonempty and prime_of_squareAnchoredSupportEscape supply a single pointwise adapter to existing escape-to-prime arithmetic; no new primality arithmetic is necessary.
- Mathlib finite counting: Finset.card_biUnion, Finset.card_filter, Finset.sum_comm, Finset.sum_boole, Finset.sum_filter, Finset.lt_sup_iff, Finset.le_sup, Finset.max'_mem, Finset.card_erase_add_one.

Repository searches found no existing full-town deletion multiplicity or overlap ledger. The earlier parity-safe ledger cannot simply be renamed: deletion counts nonmaximum witnesses, rather than all extra prime-fiber incidences.
