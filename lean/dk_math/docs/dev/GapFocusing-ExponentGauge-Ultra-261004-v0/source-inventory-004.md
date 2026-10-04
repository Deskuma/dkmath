# Instruction 004 source/API inventory

Live production sources were read before bridge implementation. The critical existing support and ledger types were recorded by `LegendrePersistenceInventory.lean` before adding bridge code; the inventory was later extended with the petal and boundary API types. The exact compiler output follows below. No theorem was inferred from a report title.

| Source | Exact audited interface | Meaning and boundary |
| --- | --- | --- |
| GnomonSupportTurnover | `mem_reindexed_primeSupport_inter_lower_iff`, `reindexed_primeSupport_inter_lower_eq_filter`, `mem_reindexed_primeSupport_inter_upper_imp_eq_two` | Exact lower filter and prime-threshold upper collapse to two. |
| GnomonPetalTurnover | `mem_reindexed_primeSupport_inter_lower_petalMul_iff`, `common_lower_dvd_gnomonPetalTransition_numerator_of_not_dvd_first` | Divisor localization under petal factorization; no frequency ledger. |
| Frontier | `legendreConjecture_iff_squareOffsets_not_fully_covered` | Reduction only; no cover-failure provider. |
| ParitySafeIncidenceBalance | `paritySafeIncidenceCount_eq_candidate_support_sum`, `paritySafeSupportExcess` | Counts pairs (seat, prime) and per-seat excess, not just prime-shell events. |
| ParitySafeFullCoverCapacityFrontier | `paritySafeCandidate_card_add_supportExcess_eq_incidence_of_fullyCovered`, `two_mul_pairOverlap_add_threeCollision_add_threeCandidate_le_fullCoverCapacity` | Exact full-cover balance and residual capacity inequality in one shell. |
| ParitySafeLowCostCapacitySlack | `paritySafeLowCostResidualCapacity_eq_mass_add_slack`, `paritySafeFullCoverRequiredLowCostSlack_le_two_capacitySlack` | Explicit actual mass plus capacity slack; no temporal persistence term. |
| ParitySafeCollisionPairOverlapCancellation | `paritySafePrimePairOverlapCount_eq_outsideCollision_add_collisionMass` | Exact separation of collision pair mass. |
| ParitySafeActualFiberCancellation | `two_mul_outsideCollisionPairOverlap_add_nineCollision_add_threeFiveDirection_add_twoResidualSlack_add_threeCandidate_le_fullCoverActualMass` | Capacity-free frontier still has actual incidence on its right side. |
| HomogeneousAddress | `dvd_cyclotomicShiftedEval_iff_primeOrder_eq_of_not_dvd` | Actual integer homogeneous value; invertible denominator and characteristic not dividing degree. |
| PrimeOrder | `primeRatio`, `primeOrder` | Ratio in ZMod and its multiplicative order; zero ratio has order zero. |
| CyclotomicAddress | `isRoot_cyclotomic_iff_prime_pow_mul_orderOf` | Fixed-coordinate degree-axis classification. |
| CyclotomicBoundary | `dvd_cyclotomicShiftedEval_iff_dvd_first_of_dvd_second` | Positive-degree vanishing-denominator branch. |

The new bridge imports only the production order/homogeneous stack and support turnover. Its dependencies are audited per declaration, rather than judging proof safety from the full facade's import set.

## Exact checked existing types

```lean
DkMath.NumberTheory.Legendre.mem_reindexed_primeSupport_inter_lower_iff {n r q : ℕ} (_hr : SquareOffset n r)
  (hlow : r < n + 1) :
  q ∈ squareOffsetPrimeSupport n r ∩ squareOffsetPrimeSupport (n + 1) (successorThresholdInsert n r) ↔
    q ∈ squareOffsetPrimeSupport n r ∧ q ∣ DkMath.Gnomon.oddGnomon n
DkMath.NumberTheory.Legendre.reindexed_primeSupport_inter_lower_eq_filter {n r : ℕ} (hr : SquareOffset n r)
  (hlow : r < n + 1) :
  squareOffsetPrimeSupport n r ∩ squareOffsetPrimeSupport (n + 1) (successorThresholdInsert n r) =
    {q ∈ squareOffsetPrimeSupport n r | q ∣ DkMath.Gnomon.oddGnomon n}
DkMath.NumberTheory.Legendre.mem_reindexed_primeSupport_inter_upper_imp_eq_two {n r q : ℕ} (hr : SquareOffset n r)
  (hupp : n + 1 ≤ r) (hsucc : Nat.Prime (n + 1))
  (hcommon : q ∈ squareOffsetPrimeSupport n r ∩ squareOffsetPrimeSupport (n + 1) (successorThresholdInsert n r)) : q = 2
DkMath.NumberTheory.Legendre.paritySafeIncidenceCount_eq_candidate_support_sum (n : ℕ) :
  paritySafeIncidenceCount n = ∑ r ∈ squareAnchorOddPointCoprimeOffsets n, (paritySafeActiveSupport n r).card
DkMath.NumberTheory.Legendre.paritySafeCandidate_card_add_supportExcess_eq_incidence_of_fullyCovered {n : ℕ}
  (hn : 0 < n) (hfull : SquareOffsetsFullyCovered n) :
  (squareAnchorOddPointCoprimeOffsets n).card + paritySafeSupportExcess n = paritySafeIncidenceCount n
DkMath.NumberTheory.Legendre.two_mul_pairOverlap_add_threeCollision_add_threeCandidate_le_fullCoverCapacity {n : ℕ}
  (hn : 0 < n) (hfull : SquareOffsetsFullyCovered n) :
  2 * paritySafePrimePairOverlapCount n + 3 * (paritySafeRechargeExactDepthFiberCollisionSeats n).card +
      3 * (squareAnchorOddPointCoprimeOffsets n).card ≤
    3 * paritySafeIncidenceCount n + 2 * paritySafeLowCostResidualCapacity n +
      2 * paritySafeRechargeExactDepthResidualPairCapacityExcess n
DkMath.NumberTheory.Legendre.paritySafeLowCostResidualCapacity_eq_mass_add_slack (n : ℕ) :
  paritySafeLowCostResidualCapacity n = paritySafeLowCostResidualMass n + paritySafeLowCostResidualCapacitySlack n
DkMath.NumberTheory.Legendre.paritySafeFullCoverRequiredLowCostSlack_le_two_capacitySlack {n : ℕ} (hn : 0 < n)
  (hfull : SquareOffsetsFullyCovered n) :
  paritySafeFullCoverRequiredLowCostSlack n ≤ 2 * paritySafeLowCostResidualCapacitySlack n
DkMath.NumberTheory.Legendre.paritySafePrimePairOverlapCount_eq_outsideCollision_add_collisionMass (n : ℕ) :
  paritySafePrimePairOverlapCount n =
    paritySafePairOverlapOutsideDepthCollision n + paritySafeDepthCollisionPairOverlapMass n
DkMath.NumberTheory.Legendre.two_mul_outsideCollisionPairOverlap_add_nineCollision_add_threeFiveDirection_add_twoResidualSlack_add_threeCandidate_le_fullCoverActualMass
  {n : ℕ} (hn : 0 < n) (hfull : SquareOffsetsFullyCovered n) :
  2 * paritySafePairOverlapOutsideDepthCollision n + 9 * (paritySafeRechargeExactDepthFiberCollisionSeats n).card +
          3 * (paritySafeRechargeExactDepthFiveDirectionCollisionSeats n).card +
        2 * paritySafeDepthCollisionResidualPairSlack n +
      3 * (squareAnchorOddPointCoprimeOffsets n).card ≤
    3 * paritySafeIncidenceCount n + 2 * paritySafeLowCostResidualMass n
DkMath.NumberTheory.Legendre.legendreConjecture_iff_squareOffsets_not_fully_covered :
  LegendreConjecture ↔ ∀ (n : ℕ), 0 < n → ¬SquareOffsetsFullyCovered n
DkMath.NumberTheory.GapFocusing.dvd_cyclotomicShiftedEval_iff_primeOrder_eq_of_not_dvd (q : ℕ) [Fact (Nat.Prime q)]
  (n : ℕ) (a b : ℤ) (hb : ¬↑q ∣ b) (hqn : ¬q ∣ n) :
  ↑q ∣ DkMath.CFBRC.cyclotomicShiftedEval n (a - b) b ↔ primeOrder q a b = n
DkMath.CFBRC.cyclotomicShiftedEval.{u_1} {R : Type u_1} [CommRing R] (m : ℕ) (x u : R) : R
DkMath.NumberTheory.Legendre.mem_reindexed_primeSupport_inter_lower_petalMul_iff {a b r q : ℕ}
  (hr : SquareOffset (DkMath.Gnomon.petalMul a b) r) (hlow : r < DkMath.Gnomon.petalMul a b + 1) (hq : Nat.Prime q) :
  q ∈
      squareOffsetPrimeSupport (DkMath.Gnomon.petalMul a b) r ∩
        squareOffsetPrimeSupport (DkMath.Gnomon.petalMul a b + 1)
          (successorThresholdInsert (DkMath.Gnomon.petalMul a b) r) ↔
    q ∈ squareOffsetPrimeSupport (DkMath.Gnomon.petalMul a b) r ∧
      (q ∣ DkMath.Gnomon.oddGnomon a ∨ q ∣ DkMath.Gnomon.oddGnomon b)
DkMath.NumberTheory.Legendre.common_lower_dvd_gnomonPetalTransition_numerator_of_not_dvd_first {a b r q : ℕ}
  (hr : SquareOffset (DkMath.Gnomon.petalMul a b) r) (hlow : r < DkMath.Gnomon.petalMul a b + 1) (hq : Nat.Prime q)
  (hnotFirst : ¬q ∣ DkMath.Gnomon.oddGnomon a)
  (hcommon :
    q ∈
      squareOffsetPrimeSupport (DkMath.Gnomon.petalMul a b) r ∩
        squareOffsetPrimeSupport (DkMath.Gnomon.petalMul a b + 1)
          (successorThresholdInsert (DkMath.Gnomon.petalMul a b) r)) :
  q ∣ (DkMath.NumberTheory.MultiGauge.gnomonPetalTransition a b).numerator
DkMath.NumberTheory.Legendre.paritySafeSupportExcess (n : ℕ) : ℕ
DkMath.NumberTheory.Legendre.paritySafePrimePairOverlapCount (n : ℕ) : ℕ
DkMath.NumberTheory.Legendre.paritySafeLowCostResidualCapacity (n : ℕ) : ℕ
DkMath.NumberTheory.Legendre.paritySafeRechargeExactDepthResidualPairCapacityExcess (n : ℕ) : ℕ
DkMath.NumberTheory.GapFocusing.isRoot_cyclotomic_iff_prime_pow_mul_orderOf.{u_1} {R : Type u_1} [CommRing R]
  [IsDomain R] {q : ℕ} [hq : Fact (Nat.Prime q)] [CharP R q] {n : ℕ} (hn : 0 < n) (z : R) :
  (Polynomial.cyclotomic n R).IsRoot z ↔ ∃ k, n = orderOf z * q ^ k
DkMath.NumberTheory.GapFocusing.dvd_cyclotomicShiftedEval_iff_dvd_first_of_dvd_second (q : ℕ) [Fact (Nat.Prime q)]
  {n : ℕ} (hn : 0 < n) (a b : ℤ) (hb : ↑q ∣ b) : ↑q ∣ DkMath.CFBRC.cyclotomicShiftedEval n (a - b) b ↔ ↑q ∣ a
DkMath.NumberTheory.GapFocusing.primeOrder (q : ℕ) (a b : ℤ) : ℕ
DkMath.NumberTheory.GapFocusing.primeRatio (q : ℕ) (a b : ℤ) : ZMod q
```
