# Instruction 006 source inventory

Live baseline: `832ef9c3b`. Exact declaration types were checked through the Legendre facade; see [raw inventory](logs/source-inventory-006.txt) and [inventory Lean](../../../DkMathTest/NumberTheory/LegendreBlockLocalizationInventory.lean).

## Required modules and quantities

| Source | Audited role |
| --- | --- |
| `ParitySafeFreshCost` | Actual incremental fresh excess, first slots, fresh-involving pairs, block temporal charge and full-cover balance |
| `ParitySafePersistence` | Actual lower candidates, old/successor support split, canonical reindex semantics |
| `ParitySafeIncidenceBalance` | `paritySafeSupportExcess`, candidate support transpose, covered/uncovered partition |
| `ParitySafeFullCoverCapacityFrontier` | `candidate.card + supportExcess = incidence` under full cover, original residual upper frontier |
| `ParitySafeCollisionPairOverlapCancellation` | `paritySafePairOverlapOutsideDepthCollision`, collision pair mass, named collision support cost, exact collision baseline/residual decomposition, eleven-collision readable frontier |
| `ParitySafeFifthDirectionGate` | `3*collision.card + fifth.card <= collisionLocalSupportCost`, terminal/collision support charge |
| `ParitySafeActualFiberCancellation` | Actual residual fiber decomposition and collision residual slack; capacity-free nine-collision frontier |
| `ParitySafeLowCostCapacitySlack` | Exact LowCost capacity = realized mass + unused slack |

## Additional mature identities discovered in the audit

`ParitySafePairResidual` already supplies:

```text
paritySafePrimePairOverlapCount_eq_supportExcess_add_residual
  Q = E + R
```

`ParitySafeSecondCancellationRedundancyAudit` already supplies:

```text
paritySafeSupportExcess_eq_outsideCollision_add_collisionSupportCost
  E = Eoutside + S
paritySafePairOverlapOutsideDepthCollision_eq_outsideSupport_add_outsideResidual
  O = Eoutside + Routside
paritySafePairOverlapOutsideDepthCollision_eq_outsideSupport_add_terminal_add_lowCostAfterUnused
  O = Eoutside + Terminal + LowCostAfterUnused
paritySafeSecondCancellationFrontier_iff_reducedSupportCharge
```

These are reused rather than reproved as new shell identities. The new module adds missing local/shell inequalities, block transports and block contradiction consumers.

## Name reconciliation

| Instruction spelling | Actual checked production declaration |
| --- | --- |
| `lowerParitySafeFreshExcessChargeCount` | `lowerFreshSupportExcessChargeCount` |
| `lowerParitySafeFreshPair` | `lowerParitySafeFreshPairs` |
| all other required quantity names | Exact spelling exists in production |

No compatibility aliases or parallel mathematical ledger were introduced.

## Finite reduction dependencies

The regression normalizes actual candidates and supports by proven Finset equalities. LowCost is reduced using its exact production definition: Near first-prime fibers, anchor-coprime prime-square hits, and the Fourth gated exact-witness dual-base universe. Unbounded existential syntax in the Fourth filter is replaced by equivalent witnesses in the actual finite active-prime set; this is an equality of the existing set, not a relaxed upper capacity. Every numerical theorem uses ordinary kernel `decide` or previously checked equalities.
