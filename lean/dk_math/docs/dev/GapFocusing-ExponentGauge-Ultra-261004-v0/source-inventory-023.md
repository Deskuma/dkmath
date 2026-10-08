# Source inventory 023

Clean committed checkout at checkpoint 022. Audit before new production edits.

- FinsetSupportPacking: card_le_supportUniverse, supportPackingRemainder_pairwiseDisjoint, supportPackingRightRemainder_pairwiseDisjoint, mem_supportCollisionEdges, exact left and right partitions. Reuse packing, never build a new collision relation.
- CoarseTownDeletionConservation: mem_coarseTownDeletionVertices_iff_multiplicity_pos, coarseTownDeletionMass_eq_nonmaximum_sum, coarseTown_remainder_conservation, coarseTownDeletionOverlap_le_supportExcess, coarseTown_remainder_add_loss_eq_uncovered_add_active, coarseTown_outside_deficit_iff_loss_add_inactive_lt_uncovered. Keep 022 unchanged.
- CoarseTownSurvivorCapacity: both remainder families, both survivor-capacity consumers, coarseTownRightDeletionVertices_eq_fibers. Reuse the min-fiber deletion representation and Frontier adapter.
- CoarseTownDeletionCapacity: coarseTownDeletionVertices_eq_fibers, exact left partition. No retained-direction union or handoff API yet.
- CoarsePrimeWorldVerticalCapacity: coarseColumn_commonPrime_dvd_index_gap, coarseColumn_no_commonPrime_of_small_gap, coarseCrossColumn_commonPrime_signed_gap, coarseCrossColumn_compatible_index_unique. These control destination indices; they do not count sources.
- CoarsePrimeWorldFullTown: mem_coarsePrimeWorldFullTown, coarseFullTown_survivor, coarseFullTown_subset_squareOffsets. Reuse certified support containment.
- OldSupportCapacity: pairwise actual-support family predicate and old-prime capacity. New selectors will use the sharper 022 universe.
- Repository terminal/recharge APIs concern parity-safe pairs and cofactor descent, not extremal full-town prime fibers. No matching represented-direction or handoff carrier was found.
- Mathlib: Finset.card_biUnion, card_filter, sum_comm, max'_mem, le_max', min'_mem, min'_le, OrderDual. A strictly increasing or decreasing seat rank suffices for the required cycle judgment; no graph library is needed.

Extract only neutral supported-seat accounting, unique represented occurrence,
nonmaximum-fiber counting and finite witness transpose where they remove left/right duplication.
