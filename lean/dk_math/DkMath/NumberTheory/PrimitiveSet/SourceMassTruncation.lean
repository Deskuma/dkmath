/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.PrimitiveSet.LogCapacityHittingBridge

#print "file: DkMath.NumberTheory.PrimitiveSet.SourceMassTruncation"

namespace DkMath.NumberTheory.PrimitiveSet

open DkMath.CosmicFormula.Mass

/--
Finite-window source-mass contract for the log-capacity hitting route.

This packages the source estimate layer needed by the DKMK-009 quotient-path
endpoint: a nonnegative constant, a uniform source bound on log-capacity
states, and divisibility monotonicity for descending path families.
-/
structure TailWindowSourceMassBound (M : MassSpace ℕ) (C : ℝ) : Prop where
  nonneg_const : 0 ≤ C
  source_bound : LogCapacitySourceMassBound M C
  dvd_mono : DvdMonotoneMass M

namespace TailWindowSourceMassBound

/-- Build a tail-window contract from the three existing route hypotheses. -/
theorem ofSourceBound
    {M : MassSpace ℕ} {C : ℝ}
    (hC : 0 ≤ C)
    (hsource : LogCapacitySourceMassBound M C)
    (hM : DvdMonotoneMass M) :
    TailWindowSourceMassBound M C where
  nonneg_const := hC
  source_bound := hsource
  dvd_mono := hM

/--
Finite-step tail mass supplies a tail-window source-mass contract.
-/
theorem finiteStepTail
    {ι : Type _} [DecidableEq ι]
    (steps : Finset ι) (threshold : ι → ℕ) (increment : ι → ℚ)
    (hinc : ∀ i ∈ steps, 0 ≤ increment i) :
    TailWindowSourceMassBound
      (finiteStepTailNatMassSpace steps threshold increment hinc)
      ((Finset.sum steps increment : ℚ) : ℝ) where
  nonneg_const := by
    exact_mod_cast Finset.sum_nonneg hinc
  source_bound :=
    finiteStepTailNatMassSpace_logCapacitySourceMassBound
      steps threshold increment hinc
  dvd_mono :=
    finiteStepTailNatMassSpace_dvdMonotone steps threshold increment hinc

/--
Use a tail-window source-mass contract in the DKMK-009 quotient-path capacity
route.

This theorem is intentionally a thin wrapper around
`globalLogCapacityKernel_primePowerQuotientPathFamily_weightedHitMass_le_of_sourceBound`.
-/
theorem globalLogCapacityKernel_primePowerQuotientPathFamily_weightedHitMass_le
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (IOf : ℕ → Finset ℕ)
    (hIOf :
      ∀ n q, q ∈ IOf n → q ∈ T.toDivisorTransitionKernel.index n)
    (s : LogCapacityState)
    {M : MassSpace ℕ} {C : ℝ}
    (H : TailWindowSourceMassBound M C)
    {A : Finset ℕ}
    (hA : PrimitiveOn A) :
    (W.globalLogCapacityKernel_applyAtToPrimePowerQuotientPathFamily
      IOf hIOf s H.dvd_mono).weightedHitMass A ≤ C :=
  W.globalLogCapacityKernel_primePowerQuotientPathFamily_weightedHitMass_le_of_sourceBound
    IOf hIOf s H.dvd_mono hA H.nonneg_const H.source_bound

/--
Finite-step tail source mass, applied all the way to the DKMK-009
quotient-path capacity route.

This is the concrete convenience form of `finiteStepTail` followed by
`globalLogCapacityKernel_primePowerQuotientPathFamily_weightedHitMass_le`.
-/
theorem finiteStepTail_weightedHitMass_le
    {T : PrimePowerDivisorTransitionKernel}
    {ι : Type _} [DecidableEq ι]
    (W : PrimePowerWitnessProvider T)
    (IOf : ℕ → Finset ℕ)
    (hIOf :
      ∀ n q, q ∈ IOf n → q ∈ T.toDivisorTransitionKernel.index n)
    (steps : Finset ι) (threshold : ι → ℕ) (increment : ι → ℚ)
    (hinc : ∀ i ∈ steps, 0 ≤ increment i)
    (s : LogCapacityState)
    {A : Finset ℕ}
    (hA : PrimitiveOn A) :
    (W.globalLogCapacityKernel_applyAtToPrimePowerQuotientPathFamily
      IOf hIOf s
      (finiteStepTailNatMassSpace_dvdMonotone
        steps threshold increment hinc)).weightedHitMass A ≤
      ((Finset.sum steps increment : ℚ) : ℝ) :=
  globalLogCapacityKernel_primePowerQuotientPathFamily_weightedHitMass_le
    W IOf hIOf s
    (finiteStepTail steps threshold increment hinc)
    hA

end TailWindowSourceMassBound

end DkMath.NumberTheory.PrimitiveSet
