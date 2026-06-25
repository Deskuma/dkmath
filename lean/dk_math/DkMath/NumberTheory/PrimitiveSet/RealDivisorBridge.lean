/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.PrimitiveSet.DivisorTransitionKernel
import DkMath.NumberTheory.PrimitiveSet.ValuationBudget

#print "file: DkMath.NumberTheory.PrimitiveSet.RealDivisorBridge"

namespace DkMath.NumberTheory.PrimitiveSet

namespace PrimePowerWitnessProvider

/--
The base-prime reader supplied by a witness provider satisfies the real/log
nonnegativity condition on the selected sub-index.
-/
theorem basePrimeOf_realLogNonnegOn
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (n : ℕ)
    (I : Finset ℕ)
    (hI : ∀ q, q ∈ I → q ∈ T.toDivisorTransitionKernel.index n) :
    RealLogNonnegOn I (W.basePrimeOf n I hI) :=
  W.basePrimeOf_one_le n I hI

/--
Bundle the witness-provider base-prime reader into the real/log product-budget
interface, assuming the selected base product bound.
-/
theorem basePrimeOf_realLogProductBudget_of_productBound
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (n : ℕ)
    (I : Finset ℕ)
    (hI : ∀ q, q ∈ I → q ∈ T.toDivisorTransitionKernel.index n)
    (hn : 1 < n)
    (hprod : NatProductBoundOn I (W.basePrimeOf n I hI) n) :
    RealLogProductBudget I (W.basePrimeOf n I hI) n :=
  ⟨W.basePrimeOf_realLogNonnegOn n I hI, hn, hprod⟩

/--
The log-ratio real provider built from witness-provider base primes is
sub-probability under the selected base product bound.
-/
theorem basePrimeOf_realLogRatioWeightProvider_subProbability_of_productBound
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (n : ℕ)
    (I : Finset ℕ)
    (hI : ∀ q, q ∈ I → q ∈ T.toDivisorTransitionKernel.index n)
    (hn : 1 < n)
    (hprod : NatProductBoundOn I (W.basePrimeOf n I hI) n) :
    (realLogRatioWeightProvider I (W.basePrimeOf n I hI) n
      (W.basePrimeOf_realLogNonnegOn n I hI) hn).SubProbability :=
  realLogRatioWeightProvider_subProbability_of_productBudget I
    (W.basePrimeOf n I hI) n
    (W.basePrimeOf_realLogProductBudget_of_productBound n I hI hn hprod)

/--
The log-ratio real provider built from witness-provider base primes is
sub-probability when the selected base product is supplied by pairwise-coprime
divisibility into `n`.
-/
theorem basePrimeOf_realLogRatioWeightProvider_subProbability_of_pairwise_coprime_dvd
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (n : ℕ)
    (I : Finset ℕ)
    (hI : ∀ q, q ∈ I → q ∈ T.toDivisorTransitionKernel.index n)
    (hn : 1 < n)
    (hcop : NatPairwiseCoprimeOn I (W.basePrimeOf n I hI))
    (hdvd : ∀ q, q ∈ I → W.basePrimeOf n I hI q ∣ n) :
    (realLogRatioWeightProvider I (W.basePrimeOf n I hI) n
      (W.basePrimeOf_realLogNonnegOn n I hI) hn).SubProbability :=
  W.basePrimeOf_realLogRatioWeightProvider_subProbability_of_productBound n I hI hn
    (natProductBoundOn_of_pairwise_coprime_dvd I (W.basePrimeOf n I hI)
      (Nat.lt_trans Nat.zero_lt_one hn) hcop hdvd)

/--
The log-ratio real provider built from witness-provider base primes is
sub-probability under pairwise coprimality alone: itemwise divisibility into
`n` is supplied by the divisor-transition kernel and the prime-power witness.
-/
theorem basePrimeOf_realLogRatioWeightProvider_subProbability_of_pairwise_coprime
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (n : ℕ)
    (I : Finset ℕ)
    (hI : ∀ q, q ∈ I → q ∈ T.toDivisorTransitionKernel.index n)
    (hn : 1 < n)
    (hcop : NatPairwiseCoprimeOn I (W.basePrimeOf n I hI)) :
    (realLogRatioWeightProvider I (W.basePrimeOf n I hI) n
      (W.basePrimeOf_realLogNonnegOn n I hI) hn).SubProbability :=
  W.basePrimeOf_realLogRatioWeightProvider_subProbability_of_pairwise_coprime_dvd
    n I hI hn hcop (W.basePrimeOf_dvd_source_on n I hI)

/--
The log-ratio real provider built from witness-provider base primes is
sub-probability when selected base primes are pairwise distinct.
-/
theorem basePrimeOf_realLogRatioWeightProvider_subProbability_of_pairwise_distinct
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (n : ℕ)
    (I : Finset ℕ)
    (hI : ∀ q, q ∈ I → q ∈ T.toDivisorTransitionKernel.index n)
    (hn : 1 < n)
    (hdistinct : NatPairwiseDistinctOn I (W.basePrimeOf n I hI)) :
    (realLogRatioWeightProvider I (W.basePrimeOf n I hI) n
      (W.basePrimeOf_realLogNonnegOn n I hI) hn).SubProbability :=
  W.basePrimeOf_realLogRatioWeightProvider_subProbability_of_pairwise_coprime
    n I hI hn
    (natPairwiseCoprimeOn_of_pairwise_distinct_prime I (W.basePrimeOf n I hI)
      (W.basePrimeOf_prime_on n I hI) hdistinct)

/--
The witness-provider base-prime reader is prime-valued on the selected
sub-index.
-/
theorem basePrimeOf_natPrimeValuedOn
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (n : ℕ)
    (I : Finset ℕ)
    (hI : ∀ q, q ∈ I → q ∈ T.toDivisorTransitionKernel.index n) :
    NatPrimeValuedOn I (W.basePrimeOf n I hI) :=
  W.basePrimeOf_prime_on n I hI

/--
A multiplicity budget supplies the selected witness base-prime product bound.
-/
theorem basePrimeOf_natProductBoundOn_of_multiplicityBudget
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (n : ℕ)
    (I : Finset ℕ)
    (hI : ∀ q, q ∈ I → q ∈ T.toDivisorTransitionKernel.index n)
    (hn : 0 < n)
    (hbudget :
      NatBaseMultiplicityBudgetOn I (W.basePrimeOf n I hI) n) :
    NatProductBoundOn I (W.basePrimeOf n I hI) n :=
  natProductBoundOn_of_multiplicityBudget I (W.basePrimeOf n I hI) hn
    (W.basePrimeOf_natPrimeValuedOn n I hI) hbudget

/--
Bundle the witness-provider base-prime reader into the real/log product-budget
interface under a multiplicity budget.
-/
theorem basePrimeOf_realLogProductBudget_of_multiplicityBudget
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (n : ℕ)
    (I : Finset ℕ)
    (hI : ∀ q, q ∈ I → q ∈ T.toDivisorTransitionKernel.index n)
    (hn : 1 < n)
    (hbudget :
      NatBaseMultiplicityBudgetOn I (W.basePrimeOf n I hI) n) :
    RealLogProductBudget I (W.basePrimeOf n I hI) n :=
  ⟨W.basePrimeOf_realLogNonnegOn n I hI,
    hn,
    W.basePrimeOf_natProductBoundOn_of_multiplicityBudget n I hI
      (Nat.lt_trans Nat.zero_lt_one hn) hbudget⟩

/--
The log-ratio real provider built from witness-provider base primes is
sub-probability under a base-prime multiplicity budget.
-/
theorem basePrimeOf_logRatioSubProbability_of_multiplicityBudget
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (n : ℕ)
    (I : Finset ℕ)
    (hI : ∀ q, q ∈ I → q ∈ T.toDivisorTransitionKernel.index n)
    (hn : 1 < n)
    (hbudget :
      NatBaseMultiplicityBudgetOn I (W.basePrimeOf n I hI) n) :
    (realLogRatioWeightProvider I (W.basePrimeOf n I hI) n
      (W.basePrimeOf_realLogNonnegOn n I hI) hn).SubProbability :=
  realLogRatioWeightProvider_subProbability_of_productBudget I
    (W.basePrimeOf n I hI) n
    (W.basePrimeOf_realLogProductBudget_of_multiplicityBudget
      n I hI hn hbudget)

/--
On a fixed base-prime fiber, the witness exponent reader is injective.
-/
theorem baseExponentOf_injOn_filter_basePrime
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (n : ℕ)
    (I : Finset ℕ)
    (hI : ∀ q, q ∈ I → q ∈ T.toDivisorTransitionKernel.index n)
    (p : ℕ) :
    Set.InjOn (W.baseExponentOf n I hI)
      (↑(I.filter fun q => W.basePrimeOf n I hI q = p) : Set ℕ) := by
  intro q hq r hr hqr
  rcases Finset.mem_filter.mp hq with ⟨hqI, hqbase⟩
  rcases Finset.mem_filter.mp hr with ⟨hrI, hrbase⟩
  have hqpow := W.basePrimeOf_pow_baseExponentOf_eq_on n I hI q hqI
  have hrpow := W.basePrimeOf_pow_baseExponentOf_eq_on n I hI r hrI
  calc
    q = W.basePrimeOf n I hI q ^ W.baseExponentOf n I hI q := hqpow.symm
    _ = p ^ W.baseExponentOf n I hI q := by rw [hqbase]
    _ = p ^ W.baseExponentOf n I hI r := by rw [hqr]
    _ = W.basePrimeOf n I hI r ^ W.baseExponentOf n I hI r := by rw [hrbase]
    _ = r := hrpow

/--
The selected labels with a fixed base prime fit into the exponent slots of
that prime in `n`.
-/
theorem basePrimeOf_card_filter_le_factorization
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (n : ℕ)
    (I : Finset ℕ)
    (hI : ∀ q, q ∈ I → q ∈ T.toDivisorTransitionKernel.index n)
    (hn : n ≠ 0)
    (p : ℕ) :
    (I.filter fun q => W.basePrimeOf n I hI q = p).card ≤
      n.factorization p := by
  let S := I.filter fun q => W.basePrimeOf n I hI q = p
  have hcard_img :
      S.card = (S.image (W.baseExponentOf n I hI)).card := by
    symm
    exact Finset.card_image_of_injOn
      (W.baseExponentOf_injOn_filter_basePrime n I hI p)
  have himage_sub :
      S.image (W.baseExponentOf n I hI) ⊆
        Finset.Icc 1 (n.factorization p) := by
    intro k hk
    rcases Finset.mem_image.mp hk with ⟨q, hqS, rfl⟩
    rcases Finset.mem_filter.mp hqS with ⟨hqI, hqbase⟩
    have hkpos : 0 < W.baseExponentOf n I hI q :=
      W.baseExponentOf_pos_on n I hI q hqI
    have hkle :
        W.baseExponentOf n I hI q ≤ n.factorization p := by
      have hle := W.baseExponentOf_le_factorization_on n I hI hn q hqI
      simpa [hqbase] using hle
    exact Finset.mem_Icc.mpr ⟨Nat.succ_le_of_lt hkpos, hkle⟩
  calc
    (I.filter fun q => W.basePrimeOf n I hI q = p).card = S.card := rfl
    _ = (S.image (W.baseExponentOf n I hI)).card := hcard_img
    _ ≤ (Finset.Icc 1 (n.factorization p)).card := Finset.card_le_card himage_sub
    _ = n.factorization p := by simp [Nat.card_Icc]

/--
The witness-provider base-prime reader automatically satisfies the
multiplicity budget against the source state.
-/
theorem basePrimeOf_multiplicityBudgetOn
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (n : ℕ)
    (I : Finset ℕ)
    (hI : ∀ q, q ∈ I → q ∈ T.toDivisorTransitionKernel.index n)
    (hn : n ≠ 0) :
    NatBaseMultiplicityBudgetOn I (W.basePrimeOf n I hI) n := by
  intro p _hp
  exact W.basePrimeOf_card_filter_le_factorization n I hI hn p

/--
The log-ratio real provider built from witness-provider base primes is
sub-probability without an external multiplicity-budget hypothesis.
-/
theorem basePrimeOf_logRatioSubProbability
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (n : ℕ)
    (I : Finset ℕ)
    (hI : ∀ q, q ∈ I → q ∈ T.toDivisorTransitionKernel.index n)
    (hn : 1 < n) :
    (realLogRatioWeightProvider I (W.basePrimeOf n I hI) n
      (W.basePrimeOf_realLogNonnegOn n I hI) hn).SubProbability :=
  W.basePrimeOf_logRatioSubProbability_of_multiplicityBudget n I hI hn
    (W.basePrimeOf_multiplicityBudgetOn n I hI
      (Nat.ne_of_gt (Nat.lt_trans Nat.zero_lt_one hn)))

#print axioms basePrimeOf_logRatioSubProbability
-- 'DkMath.NumberTheory.PrimitiveSet
--  .PrimePowerWitnessProvider.basePrimeOf_logRatioSubProbability'
-- depends on axioms: [propext, Classical.choice, Quot.sound]

/--
Summary theorem for the duplicate-free real/log route.

If the selected witness base primes are pairwise distinct, then the finite
`log p / log n` provider is sub-probability.
-/
theorem basePrimeOf_logRatioSubProbability_of_distinctBasePrimes
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (n : ℕ)
    (I : Finset ℕ)
    (hI : ∀ q, q ∈ I → q ∈ T.toDivisorTransitionKernel.index n)
    (hn : 1 < n)
    (hdistinct : NatPairwiseDistinctOn I (W.basePrimeOf n I hI)) :
    (realLogRatioWeightProvider I (W.basePrimeOf n I hI) n
      (W.basePrimeOf_realLogNonnegOn n I hI) hn).SubProbability :=
  W.basePrimeOf_realLogRatioWeightProvider_subProbability_of_pairwise_distinct
    n I hI hn hdistinct

end PrimePowerWitnessProvider

end DkMath.NumberTheory.PrimitiveSet
