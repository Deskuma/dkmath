/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.PrimitiveSet.FullExponentSlot
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

#print "file: DkMath.NumberTheory.PrimitiveSet.FullChannelLogSum"

open scoped BigOperators

namespace DkMath.NumberTheory.PrimitiveSet

/--
Regroup a finite log sum by fibers of the base map.

This is the equality-side finite-sum counterpart of the repeated-base
multiplicity vocabulary: every occurrence of the same base contributes one
copy of `log p`.
-/
theorem sum_log_base_eq_sum_image_multiplicity_mul_log
    {ι : Type _}
    (I : Finset ι)
    (pOf : ι → ℕ) :
    (I.sum fun i => Real.log (pOf i : ℝ)) =
      (I.image pOf).sum fun p =>
        (NatBaseMultiplicityOn I pOf p : ℝ) * Real.log (p : ℝ) := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (s := I) (t := I.image pOf)
    (g := pOf) (f := fun i => Real.log (pOf i : ℝ))
    (fun i hi => Finset.mem_image_of_mem pOf hi)]
  refine Finset.sum_congr rfl ?_
  intro p _hp
  calc
    (∑ i ∈ I with pOf i = p, Real.log (pOf i : ℝ))
        = ∑ i ∈ I with pOf i = p, Real.log (p : ℝ) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          have hpi : pOf i = p := (Finset.mem_filter.mp hi).2
          rw [hpi]
    _ = (NatBaseMultiplicityOn I pOf p : ℝ) * Real.log (p : ℝ) := by
          simp [NatBaseMultiplicityOn, nsmul_eq_mul]

/--
Prime factorization log identity.

For nonzero `n`, the finite support of `n.factorization` reconstructs `log n`
as `Σ v_p(n) log p`.
-/
theorem sum_factorization_mul_log_eq_log_nat
    {n : ℕ}
    (hn : n ≠ 0) :
    (n.factorization.support.sum fun p =>
        (n.factorization p : ℝ) * Real.log (p : ℝ)) =
      Real.log (n : ℝ) := by
  have hprod_nat :
      n.factorization.support.prod (fun p => p ^ n.factorization p) = n := by
    simpa [Finsupp.prod] using Nat.prod_factorization_pow_eq_self hn
  have hprod_log :
      Real.log (n.factorization.support.prod fun p =>
          (p : ℝ) ^ n.factorization p) =
        n.factorization.support.sum fun p =>
          Real.log ((p : ℝ) ^ n.factorization p) := by
    exact Real.log_prod (by
      intro p hp
      exact pow_ne_zero _ (by
        exact_mod_cast
          (Nat.prime_of_mem_primeFactors (by
            simpa [Nat.support_factorization] using hp)).ne_zero))
  calc
    (n.factorization.support.sum fun p =>
        (n.factorization p : ℝ) * Real.log (p : ℝ))
        = n.factorization.support.sum fun p =>
          Real.log ((p : ℝ) ^ n.factorization p) := by
          refine Finset.sum_congr rfl ?_
          intro p _hp
          rw [Real.log_pow]
    _ = Real.log (n.factorization.support.prod fun p =>
          (p : ℝ) ^ n.factorization p) := hprod_log.symm
    _ = Real.log ((n.factorization.support.prod fun p =>
          p ^ n.factorization p : ℕ) : ℝ) := by
          simp
    _ = Real.log (n : ℝ) := by
          rw [hprod_nat]

namespace PrimePowerWitnessProvider

/--
Under full exponent-slot coverage, every observed base prime lies in the
factorization support of the source.
-/
theorem fullExponentSlotCoverage_image_basePrime_subset_factorization_support
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (C : FullPrimePowerChannelSet T)
    (H : FullExponentSlotCoverage W C)
    (s : LogCapacityState) :
    ((C.channels s.1).image
        (W.basePrimeOf s.1 (C.channels s.1) (C.subset_index s.1))) ⊆
      s.1.factorization.support := by
  classical
  intro p hp
  let pOf := W.basePrimeOf s.1 (C.channels s.1) (C.subset_index s.1)
  rcases Finset.mem_image.mp hp with ⟨q, hq, hqp⟩
  have hp_prime : Nat.Prime p := by
    rw [← hqp]
    exact W.basePrimeOf_prime_on s.1 (C.channels s.1) (C.subset_index s.1) q hq
  have hmem_filter : q ∈ (C.channels s.1).filter (fun r => pOf r = p) := by
    exact Finset.mem_filter.mpr ⟨hq, hqp⟩
  have hcard_pos : 0 < NatBaseMultiplicityOn (C.channels s.1) pOf p := by
    unfold NatBaseMultiplicityOn
    exact Finset.card_pos.mpr ⟨q, hmem_filter⟩
  have hcomplete := H.baseMultiplicity_complete s p hp_prime
  have hfac_pos : 0 < s.1.factorization p := by
    rwa [hcomplete] at hcard_pos
  exact Finsupp.mem_support_iff.mpr (Nat.ne_of_gt hfac_pos)

/--
Under full exponent-slot coverage, every prime in the factorization support is
observed as a base prime.
-/
theorem fullExponentSlotCoverage_factorization_support_subset_image_basePrime
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (C : FullPrimePowerChannelSet T)
    (H : FullExponentSlotCoverage W C)
    (s : LogCapacityState) :
    s.1.factorization.support ⊆
      ((C.channels s.1).image
        (W.basePrimeOf s.1 (C.channels s.1) (C.subset_index s.1))) := by
  classical
  intro p hp
  let pOf := W.basePrimeOf s.1 (C.channels s.1) (C.subset_index s.1)
  have hp_mem_primeFactors : p ∈ s.1.primeFactors := by
    simpa [Nat.support_factorization] using hp
  have hp_prime : Nat.Prime p := Nat.prime_of_mem_primeFactors hp_mem_primeFactors
  have hcomplete := H.baseMultiplicity_complete s p hp_prime
  have hfac_ne : s.1.factorization p ≠ 0 := Finsupp.mem_support_iff.mp hp
  have hmult_ne : NatBaseMultiplicityOn (C.channels s.1) pOf p ≠ 0 := by
    intro hzero
    exact hfac_ne (by rwa [hcomplete] at hzero)
  have hcard_pos : 0 < ((C.channels s.1).filter (fun q => pOf q = p)).card := by
    simpa [NatBaseMultiplicityOn] using Nat.pos_of_ne_zero hmult_ne
  rcases Finset.card_pos.mp hcard_pos with ⟨q, hqfilter⟩
  exact Finset.mem_image.mpr
    ⟨q, (Finset.mem_filter.mp hqfilter).1, (Finset.mem_filter.mp hqfilter).2⟩

/-- Full exponent-slot coverage identifies the base-prime image with factorization support. -/
theorem fullExponentSlotCoverage_image_basePrime_eq_factorization_support
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (C : FullPrimePowerChannelSet T)
    (H : FullExponentSlotCoverage W C)
    (s : LogCapacityState) :
    ((C.channels s.1).image
        (W.basePrimeOf s.1 (C.channels s.1) (C.subset_index s.1))) =
      s.1.factorization.support := by
  exact Finset.Subset.antisymm
    (W.fullExponentSlotCoverage_image_basePrime_subset_factorization_support C H s)
    (W.fullExponentSlotCoverage_factorization_support_subset_image_basePrime C H s)

/--
Full exponent-slot coverage rewrites the full-channel base-log sum as the
factorization-support sum.
-/
theorem fullExponentSlotCoverage_sum_log_base_eq_sum_factorization_support_mul_log
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (C : FullPrimePowerChannelSet T)
    (H : FullExponentSlotCoverage W C)
    (s : LogCapacityState) :
    ((C.channels s.1).sum fun q =>
        Real.log
          (W.basePrimeOf s.1 (C.channels s.1) (C.subset_index s.1) q : ℝ)) =
      s.1.factorization.support.sum fun p =>
        (s.1.factorization p : ℝ) * Real.log (p : ℝ) := by
  classical
  let pOf := W.basePrimeOf s.1 (C.channels s.1) (C.subset_index s.1)
  calc
    ((C.channels s.1).sum fun q =>
        Real.log
          (W.basePrimeOf s.1 (C.channels s.1) (C.subset_index s.1) q : ℝ))
        = ((C.channels s.1).sum fun q => Real.log (pOf q : ℝ)) := rfl
    _ = ((C.channels s.1).image pOf).sum fun p =>
        (NatBaseMultiplicityOn (C.channels s.1) pOf p : ℝ) * Real.log (p : ℝ) := by
          exact sum_log_base_eq_sum_image_multiplicity_mul_log (C.channels s.1) pOf
    _ = ((C.channels s.1).image pOf).sum fun p =>
        (s.1.factorization p : ℝ) * Real.log (p : ℝ) := by
          refine Finset.sum_congr rfl ?_
          intro p hp
          have hp_prime : Nat.Prime p := by
            rcases Finset.mem_image.mp hp with ⟨q, hq, rfl⟩
            exact W.basePrimeOf_prime_on s.1 (C.channels s.1) (C.subset_index s.1) q hq
          rw [H.baseMultiplicity_complete s p hp_prime]
    _ = s.1.factorization.support.sum fun p =>
        (s.1.factorization p : ℝ) * Real.log (p : ℝ) := by
          rw [W.fullExponentSlotCoverage_image_basePrime_eq_factorization_support C H s]

/-- Full exponent-slot coverage supplies the full-channel log-cost equality. -/
theorem fullExponentSlotCoverage_sum_log_base_eq_log_nat
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (C : FullPrimePowerChannelSet T)
    (H : FullExponentSlotCoverage W C)
    (s : LogCapacityState) :
    ((C.channels s.1).sum fun q =>
        Real.log
          (W.basePrimeOf s.1 (C.channels s.1) (C.subset_index s.1) q : ℝ)) =
      Real.log (s.1 : ℝ) := by
  calc
    ((C.channels s.1).sum fun q =>
        Real.log
          (W.basePrimeOf s.1 (C.channels s.1) (C.subset_index s.1) q : ℝ))
        = s.1.factorization.support.sum fun p =>
          (s.1.factorization p : ℝ) * Real.log (p : ℝ) :=
          W.fullExponentSlotCoverage_sum_log_base_eq_sum_factorization_support_mul_log C H s
    _ = Real.log (s.1 : ℝ) :=
          sum_factorization_mul_log_eq_log_nat (Nat.ne_of_gt (Nat.lt_trans Nat.zero_lt_one s.2))

/--
Full exponent-slot coverage proves the log-cost completeness interface used by
the Markov-shadow bridge.
-/
theorem fullChannelLogCostComplete_of_fullExponentSlotCoverage
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (C : FullPrimePowerChannelSet T)
    (H : FullExponentSlotCoverage W C) :
    FullChannelLogCostComplete W C := by
  constructor
  intro s
  simpa [vonMangoldtShadowCost, witnessLogCost] using
    W.fullExponentSlotCoverage_sum_log_base_eq_log_nat C H s

end PrimePowerWitnessProvider

end DkMath.NumberTheory.PrimitiveSet
