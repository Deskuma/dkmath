# Instruction 007 source inventory

Baseline `bed7c6d4b` (006 implementation `e18edcd7b`), initially clean. All eleven requested modules were read before choosing the upper-bound representation. The [inventory probe](../../../DkMathTest/NumberTheory/LegendreIncidenceUpperInventory.lean) records exact live names; its [output](logs/source-inventory-007.txt) records checked types. The [declaration listing](logs/declaration-inventory-007.txt) records the complete requested source set.

| Required module | Existing interfaces and conclusion of audit |
| --- | --- |
| `ParitySafeIncidenceBalance` | `paritySafeIncidenceCount_eq_candidate_support_sum`, `paritySafeCoveredCandidates_card_add_supportExcess_eq_incidence`, `paritySafeCoveredCandidates_card_add_uncoveredCandidates_card_eq_candidate_card`, `paritySafeIncidenceConservation`: the existing ledger supplies the deficit identity. |
| `ParitySafeReducedResidue` | `paritySafeIncidenceCount_eq_reducedQuotientInterval_sum`, `card_paritySafeActiveWaveOffsets_eq_reducedQuotientInterval`, `paritySafeActiveWave_same_wave_quotient_rigidity`: reduced quotient intervals expose odd endpoints and anchor coprimality. |
| `ParitySafeMobiusOddCorrection` | `paritySafeOddRawQuotientInterval_card_eq`, `paritySafeOddMultipleFloorDelta`, `paritySafeActiveWave_card_eq_oddRaw_add_correction`, `paritySafeOddMobiusCorrection_nonpos`, `paritySafeIncidenceCount_le_oddRaw_sum`: the raw endpoint bound already exists. Its private odd-divisor counting proof is now exposed as `card_filter_odd_dvd_Ioc_eq_paritySafeDelta`, with unchanged mathematics. |
| `ParitySafeWavePruning` | `paritySafeDuplicateDeletionSet_card_le_waveDuplicateBudget`: deletion/recharge bookkeeping does not supply a new independent upper bound. |
| `ParitySafePersistence` | `lowerParitySafePersistentSupport_subset_primeFactors`: the `4*r+1` factor restriction applies to persistent support; applying it to fresh or all active support would be false. |
| `ParitySafePersistenceParity` | `sum_lowerPersistentCount_le_parityCap`: checked temporal parity capacity. |
| `ParitySafeFreshCost` | `sum_lowerCandidates_sub_parityCap_sub_firstSlots_le_excess`: temporal excess lower bound needs simultaneous full cover. It cannot be substituted as an unconditional deficit lower bound. |
| `ParitySafeBlockLocalization` | `block_incidence_add_uncovered_eq_candidate_add_supportExcess`, `not_block_fullyCovered_of_incidence_lt_candidate_add_freshBound`, `exists_prime_squareCell_of_not_block_fullyCovered`: reused block consumers. |
| `ParitySafeFullCoverCapacityFrontier` | `paritySafeCandidate_card_add_supportExcess_eq_incidence_of_fullyCovered`: the old full-cover identity is a consumer, not a premise of the new upper theorem. |
| `ParitySafeActualFiberCancellation` | Actual residual/collision decomposition remains unchanged; it does not improve the independent wave cap. |
| `ParitySafeUnusedResidualPairRouting` | Unused residual routing remains unchanged. The facade's `paritySafeLowCostResidualCapacity_eq_mass_add_slack` and `paritySafeSecondCancellationFrontier_iff_reducedSupportCharge` explain the cancellation boundary recorded in006. |

The wave side is selected after this comparison. The candidate side gives the independent subset `paritySafeActiveSupport n r ⊆ (n^2+r).primeFactors`; counting all point factors includes large factors, and is weaker in the checked shell21. Restricting those factors by every active-prime condition recovers the original support and offers no upper-bound simplification by itself.

New production uses the existing active-prime set and existing incidence count. There is no second incidence ledger. Finite numerical regressions normalize the active-prime set to a proven prime filter; the main structural proof never evaluates actual incidence.
