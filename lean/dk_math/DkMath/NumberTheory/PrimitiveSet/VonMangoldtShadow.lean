/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.PrimitiveSet.LogCapacityKernel

#print "file: DkMath.NumberTheory.PrimitiveSet.VonMangoldtShadow"

namespace DkMath.NumberTheory.PrimitiveSet

namespace PrimePowerLabel

/--
The finite real-log shadow of the von Mangoldt weight on an explicitly
witnessed prime-power label.

For a label `q = p^k`, this records the DkMath channel cost `log p`.  It is not
the analytic von Mangoldt function; it is the theorem-facing finite shadow used
by the capacity-kernel route.
-/
noncomputable def vonMangoldtLogCost (L : PrimePowerLabel) : ℝ :=
  Real.log (L.p : ℝ)

@[simp] theorem vonMangoldtLogCost_eq_log_base
    (L : PrimePowerLabel) :
    L.vonMangoldtLogCost = Real.log (L.p : ℝ) :=
  rfl

/-- The finite von-Mangoldt shadow cost is nonnegative. -/
theorem vonMangoldtLogCost_nonneg
    (L : PrimePowerLabel) :
    0 ≤ L.vonMangoldtLogCost := by
  rw [vonMangoldtLogCost_eq_log_base]
  exact real_log_nat_nonneg_of_one_le (le_of_lt L.prime.one_lt)

/--
The chosen prime-power witness reads the label as `q = p^k` and assigns cost
`log p`.
-/
theorem exists_prime_power_with_vonMangoldtLogCost
    (L : PrimePowerLabel) :
    ∃ p k,
      Nat.Prime p ∧ 0 < k ∧ L.q = p ^ k ∧
        L.vonMangoldtLogCost = Real.log (p : ℝ) :=
  ⟨L.p, L.k, L.prime, L.k_pos, L.eq_pow, rfl⟩

end PrimePowerLabel

namespace PrimePowerWitnessProvider

/--
Witness-provider real-log cost on a selected sub-index.

On selected labels, this is `log p(q)`, where `p(q)` is read from the chosen
prime-power witness.  Outside the selected finite set, `basePrimeOf` is `1`, so
the cost is harmlessly `0`.
-/
noncomputable def witnessLogCost
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (n : ℕ)
    (I : Finset ℕ)
    (hI : ∀ q, q ∈ I → q ∈ T.toDivisorTransitionKernel.index n) :
    ℕ → ℝ :=
  fun q => Real.log (W.basePrimeOf n I hI q : ℝ)

/--
Named von-Mangoldt-like shadow cost supplied by the witness provider.

This is definitionally the same as `witnessLogCost`; the separate name makes
the Markov-kernel interpretation explicit without importing an analytic
von Mangoldt function.
-/
noncomputable def vonMangoldtShadowCost
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (n : ℕ)
    (I : Finset ℕ)
    (hI : ∀ q, q ∈ I → q ∈ T.toDivisorTransitionKernel.index n) :
    ℕ → ℝ :=
  W.witnessLogCost n I hI

@[simp] theorem vonMangoldtShadowCost_eq_witnessLogCost
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (n : ℕ)
    (I : Finset ℕ)
    (hI : ∀ q, q ∈ I → q ∈ T.toDivisorTransitionKernel.index n) :
    W.vonMangoldtShadowCost n I hI = W.witnessLogCost n I hI :=
  rfl

/-- On the selected sub-index, the witness cost is the log of the chosen base. -/
theorem witnessLogCost_of_mem
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (n : ℕ)
    (I : Finset ℕ)
    (hI : ∀ q, q ∈ I → q ∈ T.toDivisorTransitionKernel.index n)
    {q : ℕ}
    (hq : q ∈ I) :
    W.witnessLogCost n I hI q =
      Real.log ((W.label n q (hI q hq)).p : ℝ) := by
  simp [witnessLogCost, basePrimeOf, hq]

/--
On the selected sub-index, the witness-provider cost agrees with the
prime-power-label von-Mangoldt shadow cost.
-/
theorem witnessLogCost_eq_label_vonMangoldtLogCost_on
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (n : ℕ)
    (I : Finset ℕ)
    (hI : ∀ q, q ∈ I → q ∈ T.toDivisorTransitionKernel.index n) :
    ∀ q, (hq : q ∈ I) →
      W.witnessLogCost n I hI q =
        (W.label n q (hI q hq)).vonMangoldtLogCost := by
  intro q hq
  rw [W.witnessLogCost_of_mem n I hI hq]
  rfl

/-- The witness-provider von-Mangoldt shadow cost is nonnegative on `I`. -/
theorem witnessLogCost_nonneg_on
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (n : ℕ)
    (I : Finset ℕ)
    (hI : ∀ q, q ∈ I → q ∈ T.toDivisorTransitionKernel.index n) :
    ∀ q, q ∈ I → 0 ≤ W.witnessLogCost n I hI q := by
  intro q hq
  rw [W.witnessLogCost_of_mem n I hI hq]
  exact (W.label n q (hI q hq)).vonMangoldtLogCost_nonneg

/-- The selected shadow cost reconstructs a prime-power witness and `log p`. -/
theorem exists_prime_power_with_witnessLogCost_on
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (n : ℕ)
    (I : Finset ℕ)
    (hI : ∀ q, q ∈ I → q ∈ T.toDivisorTransitionKernel.index n) :
    ∀ q, q ∈ I →
      ∃ p k,
        Nat.Prime p ∧ 0 < k ∧ q = p ^ k ∧
          W.witnessLogCost n I hI q = Real.log (p : ℝ) := by
  intro q hq
  let L := W.label n q (hI q hq)
  refine ⟨L.p, L.k, L.prime, L.k_pos, ?_, ?_⟩
  · exact (W.label_q n q (hI q hq)).symm.trans L.eq_pow
  · exact W.witnessLogCost_of_mem n I hI hq

/-- Normalized Markov-shadow weight `log p(q) / log n`. -/
noncomputable def normalizedVonMangoldtShadowWeight
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (n : ℕ)
    (I : Finset ℕ)
    (hI : ∀ q, q ∈ I → q ∈ T.toDivisorTransitionKernel.index n) :
    ℕ → ℝ :=
  fun q => W.vonMangoldtShadowCost n I hI q / Real.log (n : ℝ)

@[simp] theorem normalizedVonMangoldtShadowWeight_eq_logRatio
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (n : ℕ)
    (I : Finset ℕ)
    (hI : ∀ q, q ∈ I → q ∈ T.toDivisorTransitionKernel.index n) :
    W.normalizedVonMangoldtShadowWeight n I hI =
      fun q => Real.log (W.basePrimeOf n I hI q : ℝ) / Real.log (n : ℝ) :=
  rfl

/--
The local log-capacity kernel uses exactly the witness-provider shadow cost as
its channel cost.
-/
theorem logCapacityKernel_cost_eq_vonMangoldtShadowCost
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (n : ℕ)
    (I : Finset ℕ)
    (hI : ∀ q, q ∈ I → q ∈ T.toDivisorTransitionKernel.index n)
    (hn : 1 < n) :
    (W.logCapacityKernel n I hI hn).cost () =
      W.vonMangoldtShadowCost n I hI :=
  rfl

/--
The provider-facing log-capacity weight is exactly the normalized
von-Mangoldt shadow weight.
-/
theorem logCapacityKernelRealWeightProvider_weight_eq_normalizedVonMangoldtShadowWeight
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (n : ℕ)
    (I : Finset ℕ)
    (hI : ∀ q, q ∈ I → q ∈ T.toDivisorTransitionKernel.index n)
    (hn : 1 < n) :
    (W.logCapacityKernelRealWeightProvider n I hI hn).weight =
      W.normalizedVonMangoldtShadowWeight n I hI :=
  rfl

end PrimePowerWitnessProvider

end DkMath.NumberTheory.PrimitiveSet
