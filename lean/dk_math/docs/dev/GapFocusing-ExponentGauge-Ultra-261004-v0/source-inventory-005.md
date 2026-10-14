# Instruction 005 source and cost inventory

The required production sources and definitions were read before new cost code. `LegendreFreshCostInventory.lean` records their exact checked types below. The inventory starts from the current checkout, including Instruction 004.

| Production quantity | Exact definition or relation | Fresh-cost interpretation |
| --- | --- | --- |
| `paritySafeActiveSupport n r` | Active bounded odd nondivisor primes that divide `n^2+r` | Full actual successor support K. |
| `paritySafeSupportExcess n` | Sum over actual candidates of `support.card-1` | One mandatory first hit is uncharged at each occupied seat. |
| `paritySafePrimePairOverlapCount n` | Sum over actual candidates of `choose(support.card,2)` | Unordered pairs, including canonical-star edges. |
| `paritySafeResidualPairMass n` | Sum over actual candidates of `choose(support.card-1,2)` | Removes the canonical star; K=2 has no residual pair. |
| `paritySafeLowCostResidualMass n` | Near residual-triple incidences.card + exact-depth noncollision seats.card + exact fourth-direction pairs.card | Three actual residual branches. Freshness alone does not locate one. |
| `paritySafeLowCostResidualCapacity n` | Near first-prime wave budget + anchor-coprime prime-square depth budget + fourth-gate dual-base pairs.card | Upper capacity for the above residual branches; capacity slack is explicit. |
| `paritySafeRechargeExactDepthResidualPairCapacityExcess n` | Sum over exact-depth collisions of `choose(support.card-1,2)-1` | Residual room at collisions; not the first support-excess unit. |
| `paritySafePairOverlapOutsideDepthCollision n` | Pair sum over candidates minus collision seats | Receives the outside restriction of fresh pairs, not every fresh pair automatically. |
| `paritySafeDepthCollisionLocalSupportCost n` | Sum over collision seats of `support.card-1` | Actual collided-seat excess cost. |
| `lowerParitySafeFreshSupport n r` | Successor active support minus full old bounded-prime support | Existing fresh object; no substitute support is introduced. |
| `lowerParitySafeFreshCount n` | Sum of fresh.card over existing lower successor candidates | Counts seat-prime incidences. |
| `lowerPersistentSeatPool q M` | `{r in [1,M] : q divides 4*r+1}` | Fixed-seat persistent-label restriction. |
| `lowerParitySafePersistenceCap N T` | Sum over old bounded odd primes of seat-pool.card times ceil(T/q) | Instruction 004 temporal bound, before retaining candidate parity. |

`ParitySafeFullCoverCapacityFrontier` provides the exact candidate-card + support-excess = incidence identity under the existing full-cover predicate. `ParitySafeCollisionPairOverlapCancellation` removes local collision mass exactly and supplies the eleven-collision readable frontier. `ParitySafeLowCostCapacitySlack` splits actual mass and unused capacity. `ParitySafeActualFiberCancellation` retains actual fiber excess rather than using a new artificial cost budget. `ParitySafeFifthDirectionGate` supplies a fifth direction only on existing five-direction collision seats.

Existing collision seats have K>=4; fifth-direction collision seats have K>=5. This excludes a singleton from collision, but does not make every K>=2 fresh seat collide.

The prime-factor set is existing `Nat.primeFactors`, already available through production imports. The finite unordered-pair representatives are existing `Internal.upperPairs`, with `card_upperPairs_eq_choose`. No new omega-style function or generic cover framework is needed.

## Exact checked existing types

```lean
DkMath.NumberTheory.Legendre.paritySafeActiveSupport (n r : ℕ) : Finset ℕ
DkMath.NumberTheory.Legendre.paritySafeSupportExcess (n : ℕ) : ℕ
DkMath.NumberTheory.Legendre.paritySafePrimePairOverlapCount (n : ℕ) : ℕ
DkMath.NumberTheory.Legendre.paritySafeLowCostResidualCapacity (n : ℕ) : ℕ
DkMath.NumberTheory.Legendre.paritySafeRechargeExactDepthResidualPairCapacityExcess (n : ℕ) : ℕ
DkMath.NumberTheory.Legendre.paritySafePairOverlapOutsideDepthCollision (n : ℕ) : ℕ
DkMath.NumberTheory.Legendre.paritySafeDepthCollisionLocalSupportCost (n : ℕ) : ℕ
DkMath.NumberTheory.Legendre.lowerParitySafeFreshSupport (n r : ℕ) : Finset ℕ
DkMath.NumberTheory.Legendre.lowerParitySafeFreshCount (n : ℕ) : ℕ
DkMath.NumberTheory.Legendre.lowerPersistentSeatPool (q M : ℕ) : Finset ℕ
DkMath.NumberTheory.Legendre.lowerParitySafePersistenceCap (N T : ℕ) : ℕ
DkMath.NumberTheory.Legendre.paritySafeCandidate_card_add_supportExcess_eq_incidence_of_fullyCovered {n : ℕ}
  (hn : 0 < n) (hfull : SquareOffsetsFullyCovered n) :
  (squareAnchorOddPointCoprimeOffsets n).card + paritySafeSupportExcess n = paritySafeIncidenceCount n
DkMath.NumberTheory.Legendre.paritySafeLowCostResidualCapacity_eq_mass_add_slack (n : ℕ) :
  paritySafeLowCostResidualCapacity n = paritySafeLowCostResidualMass n + paritySafeLowCostResidualCapacitySlack n
DkMath.NumberTheory.Legendre.paritySafeDepthCollisionPairOverlapMass_eq_supportCost_add_collision_add_depthResidualCapacity
  (n : ℕ) :
  paritySafeDepthCollisionPairOverlapMass n =
    paritySafeDepthCollisionLocalSupportCost n + (paritySafeRechargeExactDepthFiberCollisionSeats n).card +
      paritySafeRechargeExactDepthResidualPairCapacityExcess n
DkMath.NumberTheory.Legendre.two_mul_outsideCollisionPairOverlap_add_elevenCollision_add_twoFiveDirection_le_threeSupportExcess_add_twoLowCostCapacity
  (n : ℕ) :
  2 * paritySafePairOverlapOutsideDepthCollision n + 11 * (paritySafeRechargeExactDepthFiberCollisionSeats n).card +
      2 * (paritySafeRechargeExactDepthFiveDirectionCollisionSeats n).card ≤
    3 * paritySafeSupportExcess n + 2 * paritySafeLowCostResidualCapacity n
DkMath.NumberTheory.Legendre.paritySafePrimePairOverlapCount_eq_supportExcess_add_lowCostMass_add_terminal_add_collision_add_depthFiberExcess
  (n : ℕ) :
  paritySafePrimePairOverlapCount n =
    paritySafeSupportExcess n + paritySafeLowCostResidualMass n + (paritySafeTerminalSurvivingFarProductKeys n).card +
        (paritySafeRechargeExactDepthFiberCollisionSeats n).card +
      paritySafeRechargeExactDepthFiberExcess n
DkMath.NumberTheory.Legendre.paritySafeRechargeExactDepthFiberCollision_support_card_ge_four {n r : ℕ}
  (hr : r ∈ paritySafeRechargeExactDepthFiberCollisionSeats n) : 4 ≤ (paritySafeActiveSupport n r).card
DkMath.NumberTheory.Legendre.paritySafeRechargeDepthFiveDirectionCollision_fiveDirection_packet {n r : ℕ}
  (hr : r ∈ paritySafeRechargeExactDepthFiveDirectionCollisionSeats n) :
  have p := paritySafeCanonicalSupportPrime n r;
  ∃ q s u v,
    p ∈ paritySafeActiveSupport n r ∧
      q ∈ paritySafeActiveSupport n r ∧
        s ∈ paritySafeActiveSupport n r ∧
          u ∈ paritySafeActiveSupport n r ∧
            v ∈ paritySafeActiveSupport n r ∧
              p < q ∧
                p < s ∧ p < u ∧ p < v ∧ q ≠ s ∧ q ≠ u ∧ q ≠ v ∧ s ≠ u ∧ s ≠ v ∧ u ≠ v ∧ p * q * s * u * v ∣ n ^ 2 + r
DkMath.NumberTheory.Legendre.lowerParitySafePersistentSupport_subset_addresses {n r M : ℕ}
  (hr : r ∈ lowerParitySafeCandidates n) (hnM : n ≤ M) :
  lowerParitySafePersistentSupport n r ⊆
    {q ∈ (DkMath.NumberTheory.Primitive.primeScalesUpTo M).erase 2 | q ∣ DkMath.Gnomon.oddGnomon n}
DkMath.NumberTheory.Legendre.Internal.card_upperPairs_eq_choose (s : Finset ℕ) :
  (Internal.upperPairs s).card = s.card.choose 2
Nat.mem_primeFactors {n p : ℕ} : p ∈ n.primeFactors ↔ Nat.Prime p ∧ p ∣ n ∧ n ≠ 0
```
