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

/--
Analytic placeholder for a finite-step tail envelope.

This does not prove an analytic estimate.  It only records the future input
needed to turn a finite-step total increment bound into a `1 + error` bound.
-/
structure FiniteStepTailAnalyticBound
    {ι : Type _} [DecidableEq ι]
    (steps : Finset ι) (increment : ι → ℚ) (error : ℝ) : Prop where
  total_le_one_add_error :
    ((Finset.sum steps increment : ℚ) : ℝ) ≤ 1 + error

/--
Externally supplied finite-step truncation envelope estimate.

This bundles the nonnegative increment data needed to build the finite-step
source envelope with the analytic placeholder that bounds its total increment.
-/
structure TruncationEnvelopeEstimate
    {ι : Type _} [DecidableEq ι]
    (steps : Finset ι) (threshold : ι → ℕ)
    (increment : ι → ℚ) (error : ℝ) : Prop where
  increment_nonneg : ∀ i ∈ steps, 0 ≤ increment i
  analytic_bound : FiniteStepTailAnalyticBound steps increment error

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

/--
Finite-step tail route bound after supplying the analytic placeholder
`sum increment <= 1 + error`.
-/
theorem finiteStepTail_weightedHitMass_le_one_add_error
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
    (hA : PrimitiveOn A)
    {error : ℝ}
    (herror : FiniteStepTailAnalyticBound steps increment error) :
    (W.globalLogCapacityKernel_applyAtToPrimePowerQuotientPathFamily
      IOf hIOf s
      (finiteStepTailNatMassSpace_dvdMonotone
        steps threshold increment hinc)).weightedHitMass A ≤
      1 + error :=
  (finiteStepTail_weightedHitMass_le
    W IOf hIOf steps threshold increment hinc s hA).trans
    herror.total_le_one_add_error

end TailWindowSourceMassBound

namespace TruncationEnvelopeEstimate

/--
Single-window toy provider for externally supplied truncation estimates.

This uses one finite step with threshold `x` and increment `c`.  The analytic
input is kept external as `(c : ℝ) <= 1 + error`.
-/
theorem singleWindow
    (x : ℕ) (c : ℚ) (hc : 0 ≤ c)
    {error : ℝ} (hbound : (c : ℝ) ≤ 1 + error) :
    TruncationEnvelopeEstimate
      (Finset.univ : Finset Unit)
      (fun _ : Unit => x)
      (fun _ : Unit => c)
      error where
  increment_nonneg := by
    intro _i _hi
    exact hc
  analytic_bound := by
    constructor
    simpa using hbound

/--
Route theorem for externally supplied finite-step truncation estimates.

This is a packaging wrapper around
`TailWindowSourceMassBound.finiteStepTail_weightedHitMass_le_one_add_error`.
-/
theorem finiteStepTail_weightedHitMass_le_one_add_error
    {T : PrimePowerDivisorTransitionKernel}
    {ι : Type _} [DecidableEq ι]
    (W : PrimePowerWitnessProvider T)
    (IOf : ℕ → Finset ℕ)
    (hIOf :
      ∀ n q, q ∈ IOf n → q ∈ T.toDivisorTransitionKernel.index n)
    (steps : Finset ι) (threshold : ι → ℕ) (increment : ι → ℚ)
    (s : LogCapacityState)
    {A : Finset ℕ}
    (hA : PrimitiveOn A)
    {error : ℝ}
    (H : TruncationEnvelopeEstimate steps threshold increment error) :
    (W.globalLogCapacityKernel_applyAtToPrimePowerQuotientPathFamily
      IOf hIOf s
      (finiteStepTailNatMassSpace_dvdMonotone
        steps threshold increment H.increment_nonneg)).weightedHitMass A ≤
      1 + error :=
  TailWindowSourceMassBound.finiteStepTail_weightedHitMass_le_one_add_error
    W IOf hIOf steps threshold increment H.increment_nonneg s hA
    H.analytic_bound

end TruncationEnvelopeEstimate

end DkMath.NumberTheory.PrimitiveSet
