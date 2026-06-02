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

/--
Analytic-side contract for dyadic band estimates.

This records exactly the two analytic facts needed to feed the dyadic range
provider: nonnegative band increments and a total `1 + error` bound.
-/
structure DyadicBandAnalyticEstimate
    (x K : ℕ) (increment : ℕ → ℚ) (error : ℝ) : Prop where
  increment_nonneg :
    ∀ k ∈ Finset.range (K + 1), 0 ≤ increment k
  total_le_one_add_error :
    ((Finset.sum (Finset.range (K + 1)) increment : ℚ) : ℝ) ≤
      1 + error

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
Dyadic range provider for externally supplied truncation estimates.

This fixes the finite step set as `Finset.range (K + 1)` and the threshold as
`x * 2^k`, while keeping the analytic increment estimate external.
-/
theorem dyadicRange
    (x K : ℕ) (increment : ℕ → ℚ)
    (hinc : ∀ k ∈ Finset.range (K + 1), 0 ≤ increment k)
    {error : ℝ}
    (hbound :
      ((Finset.sum (Finset.range (K + 1)) increment : ℚ) : ℝ) ≤
        1 + error) :
    TruncationEnvelopeEstimate
      (Finset.range (K + 1))
      (fun k : ℕ => x * 2^k)
      increment
      error where
  increment_nonneg := hinc
  analytic_bound := by
    constructor
    exact hbound

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

namespace DyadicBandAnalyticEstimate

/--
Constant-band provider for dyadic analytic estimates.

This keeps the finite-sum bound external, avoiding finite-sum simplification
and Nat/Rat/Real coercion work in the first provider theorem.
-/
theorem constantBand
    (x K : ℕ) (c : ℚ)
    (hc : 0 ≤ c)
    {error : ℝ}
    (hbound :
      ((Finset.sum (Finset.range (K + 1)) (fun _ : ℕ => c) : ℚ) : ℝ) ≤
        1 + error) :
    DyadicBandAnalyticEstimate x K (fun _ : ℕ => c) error where
  increment_nonneg := by
    intro _k _hk
    exact hc
  total_le_one_add_error := hbound

/--
Constant-band provider from the caller-facing bound
`((K + 1 : ℚ) * c : ℝ) <= 1 + error`.
-/
theorem constantBand_of_natCastMulBound
    (x K : ℕ) (c : ℚ)
    (hc : 0 ≤ c)
    {error : ℝ}
    (hbound :
      ((((K + 1 : ℕ) : ℚ) * c : ℚ) : ℝ) ≤ 1 + error) :
    DyadicBandAnalyticEstimate x K (fun _ : ℕ => c) error := by
  apply constantBand x K c hc
  simpa [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using hbound

/--
Majorant-envelope provider for dyadic analytic estimates.

The actual increment only needs nonnegativity.  Its total estimate is obtained
by comparing it with a caller-supplied majorant on the same finite dyadic range.
-/
theorem ofMajorant
    (x K : ℕ)
    (increment majorant : ℕ → ℚ)
    (hinc_nonneg :
      ∀ k ∈ Finset.range (K + 1), 0 ≤ increment k)
    (hle :
      ∀ k ∈ Finset.range (K + 1), increment k ≤ majorant k)
    {error : ℝ}
    (hmajorant_bound :
      ((Finset.sum (Finset.range (K + 1)) majorant : ℚ) : ℝ) ≤
        1 + error) :
    DyadicBandAnalyticEstimate x K increment error where
  increment_nonneg := hinc_nonneg
  total_le_one_add_error := by
    have hsum :
        Finset.sum (Finset.range (K + 1)) increment ≤
          Finset.sum (Finset.range (K + 1)) majorant := by
      exact Finset.sum_le_sum hle
    have hsumR :
        ((Finset.sum (Finset.range (K + 1)) increment : ℚ) : ℝ) ≤
          ((Finset.sum (Finset.range (K + 1)) majorant : ℚ) : ℝ) := by
      exact_mod_cast hsum
    exact le_trans hsumR hmajorant_bound

/--
Turn an analytic dyadic band estimate into the truncation envelope consumed by
the existing finite-step route theorem.
-/
theorem toTruncationEnvelopeEstimate
    {x K : ℕ} {increment : ℕ → ℚ} {error : ℝ}
    (H : DyadicBandAnalyticEstimate x K increment error) :
    TruncationEnvelopeEstimate
      (Finset.range (K + 1))
      (fun k : ℕ => x * 2^k)
      increment
      error :=
  TruncationEnvelopeEstimate.dyadicRange
    x K increment H.increment_nonneg H.total_le_one_add_error

end DyadicBandAnalyticEstimate

end DkMath.NumberTheory.PrimitiveSet
