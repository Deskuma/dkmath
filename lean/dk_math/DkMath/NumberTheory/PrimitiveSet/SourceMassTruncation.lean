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

/--
Denominator-cleared finite geometric-sum identity over the dyadic range length.

This is the algebraic form used before introducing any division side condition
such as `ratio != 1`.
-/
theorem geomSum_range_mul_one_sub
    (ratio : ℝ) (K : ℕ) :
    (1 - ratio) *
      (Finset.sum (Finset.range (K + 1))
        (fun k : ℕ => ratio ^ k))
      =
    1 - ratio ^ (K + 1) := by
  exact mul_neg_geom_sum ratio (K + 1)

/--
Finite geometric-sum upper bound over the dyadic range length.

This is the order form needed by the source-mass truncation layer; it avoids a
separate division-form equality and uses only the positivity supplied by
`ratio < 1`.
-/
theorem geomSum_range_le_one_div_one_sub
    {ratio : ℝ} (K : ℕ)
    (hr0 : 0 ≤ ratio)
    (hr1 : ratio < 1) :
    (Finset.sum (Finset.range (K + 1))
      (fun k : ℕ => ratio ^ k))
      ≤
    1 / (1 - ratio) := by
  have hpos : 0 < 1 - ratio := sub_pos.mpr hr1
  have hpow_nonneg : 0 ≤ ratio ^ (K + 1) :=
    pow_nonneg hr0 (K + 1)
  have hnum_le : 1 - ratio ^ (K + 1) ≤ 1 :=
    sub_le_self 1 hpow_nonneg
  have hmul_eq :
      (1 - ratio) *
        (Finset.sum (Finset.range (K + 1))
          (fun k : ℕ => ratio ^ k))
        =
      1 - ratio ^ (K + 1) :=
    geomSum_range_mul_one_sub ratio K
  have hmul_le :
      (1 - ratio) *
        (Finset.sum (Finset.range (K + 1))
          (fun k : ℕ => ratio ^ k))
        ≤
      1 := by
    simpa [hmul_eq] using hnum_le
  rw [le_div_iff₀ hpos]
  simpa [mul_comm] using hmul_le

/--
Scale the finite geometric-sum upper bound by a nonnegative base.

This is the caller-facing bound shape needed before plugging the estimate into
the dyadic source-mass provider layer.
-/
theorem base_mul_geomSum_range_le_of_base_mul_one_div_le
    {base ratio error : ℝ} (K : ℕ)
    (hbase : 0 ≤ base)
    (hr0 : 0 ≤ ratio)
    (hr1 : ratio < 1)
    (hbudget : base * (1 / (1 - ratio)) ≤ 1 + error) :
    base *
      (Finset.sum (Finset.range (K + 1))
        (fun k : ℕ => ratio ^ k))
      ≤
    1 + error := by
  have hsum :
      (Finset.sum (Finset.range (K + 1))
        (fun k : ℕ => ratio ^ k))
        ≤
      1 / (1 - ratio) :=
    geomSum_range_le_one_div_one_sub K hr0 hr1
  have hscaled :
      base *
        (Finset.sum (Finset.range (K + 1))
          (fun k : ℕ => ratio ^ k))
        ≤
      base * (1 / (1 - ratio)) :=
    mul_le_mul_of_nonneg_left hsum hbase
  exact le_trans hscaled hbudget

/--
Pointwise geometric majorant from a first-band bound and uniform step decay.

This only builds the geometric pointwise control.  The provider's separate
nonnegativity hypothesis stays outside this theorem.
-/
theorem pointwiseGeometricMajorant_of_firstBand_decay
    (K : ℕ)
    (increment : ℕ → ℚ)
    (base ratio : ℚ)
    (hbase0 : increment 0 ≤ base)
    (hdecay :
      ∀ k ∈ Finset.range K,
        increment (k + 1) ≤ ratio * increment k)
    (hr0 : 0 ≤ ratio) :
    ∀ k ∈ Finset.range (K + 1),
      increment k ≤ base * ratio ^ k := by
  have hmain :
      ∀ k, k ≤ K → increment k ≤ base * ratio ^ k := by
    intro k
    induction k with
    | zero =>
        intro _hk
        simpa using hbase0
    | succ k ih =>
        intro hk_succ
        have hk_le : k ≤ K :=
          le_trans (Nat.le_succ k) hk_succ
        have hk_lt : k < K :=
          Nat.lt_of_succ_le hk_succ
        have hstep :
            increment (k + 1) ≤ ratio * increment k :=
          hdecay k (Finset.mem_range.mpr hk_lt)
        have hmul :
            ratio * increment k ≤ ratio * (base * ratio ^ k) :=
          mul_le_mul_of_nonneg_left (ih hk_le) hr0
        calc
          increment (k + 1) ≤ ratio * increment k := hstep
          _ ≤ ratio * (base * ratio ^ k) := hmul
          _ = base * ratio ^ (k + 1) := by
            ring_nf
  intro k hk
  have hk_le : k ≤ K :=
    Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  exact hmain k hk_le

/--
Abstract source of the one-over-one-minus geometric budget.

This package separates the analytic origin of `base` and `ratio` from the
dyadic provider route.
-/
structure GeometricBudgetSource where
  base : ℚ
  ratio : ℚ
  error : ℝ
  hbase : 0 ≤ (base : ℝ)
  hr0 : 0 ≤ (ratio : ℝ)
  hr1 : (ratio : ℝ) < 1
  hbudget : (base : ℝ) * (1 / (1 - (ratio : ℝ))) ≤ 1 + error

/--
Analytic input package for the first-band and uniform-decay route.

This does not replace the DKMK-016 responsibility split.  It packages the
remaining caller-side analytic inputs that are consumed together by
`DyadicBandAnalyticEstimate.ofFirstBandDecayBudgetSource`.
-/
structure FirstBandDecayBudgetSource
    (K : ℕ) (increment : ℕ → ℚ) where
  budget : GeometricBudgetSource
  hinc_nonneg :
    ∀ k ∈ Finset.range (K + 1), 0 ≤ increment k
  hbase0 :
    increment 0 ≤ budget.base
  hdecay :
    ∀ k ∈ Finset.range K,
      increment (k + 1) ≤ budget.ratio * increment k

namespace GeometricBudgetSource

/--
Build a geometric budget source from an explicit one-over-one-minus budget.

This is a readability constructor, not an analytic estimate.
-/
def ofBudget
    (base ratio : ℚ)
    (error : ℝ)
    (hbase : 0 ≤ (base : ℝ))
    (hr0 : 0 ≤ (ratio : ℝ))
    (hr1 : (ratio : ℝ) < 1)
    (hbudget :
      (base : ℝ) * (1 / (1 - (ratio : ℝ))) ≤ 1 + error) :
    GeometricBudgetSource where
  base := base
  ratio := ratio
  error := error
  hbase := hbase
  hr0 := hr0
  hr1 := hr1
  hbudget := hbudget

/--
Build a geometric budget source with zero ratio.

This is an API sanity constructor, not an analytic estimate.  With ratio zero,
the one-over-one-minus budget reduces to the caller-supplied `base <= 1 + error`.
-/
def ofZeroRatio
    (base : ℚ)
    (error : ℝ)
    (hbase : 0 ≤ (base : ℝ))
    (hbudget : (base : ℝ) ≤ 1 + error) :
    GeometricBudgetSource where
  base := base
  ratio := 0
  error := error
  hbase := hbase
  hr0 := by norm_num
  hr1 := by norm_num
  hbudget := by
    simpa using hbudget

end GeometricBudgetSource

namespace FirstBandDecayBudgetSource

/--
Build a first-band / uniform-decay source from an already packaged geometric
budget.

This is the minimal constructor for the DKMK-017 analytic-input package.
-/
def ofBudgetSource
    {K : ℕ} {increment : ℕ → ℚ}
    (B : GeometricBudgetSource)
    (hinc_nonneg :
      ∀ k ∈ Finset.range (K + 1), 0 ≤ increment k)
    (hbase0 : increment 0 ≤ B.base)
    (hdecay :
      ∀ k ∈ Finset.range K,
        increment (k + 1) ≤ B.ratio * increment k) :
    FirstBandDecayBudgetSource K increment where
  budget := B
  hinc_nonneg := hinc_nonneg
  hbase0 := hbase0
  hdecay := hdecay

/--
Build a first-band / uniform-decay source from an explicit geometric budget.

This keeps the concrete one-over-one-minus budget proof at the analytic-input
boundary while producing the package consumed by the dyadic provider route.
-/
def ofBudgetAndDecay
    {K : ℕ} {increment : ℕ → ℚ}
    (base ratio : ℚ)
    (error : ℝ)
    (hbase : 0 ≤ (base : ℝ))
    (hr0 : 0 ≤ (ratio : ℝ))
    (hr1 : (ratio : ℝ) < 1)
    (hbudget :
      (base : ℝ) * (1 / (1 - (ratio : ℝ))) ≤ 1 + error)
    (hinc_nonneg :
      ∀ k ∈ Finset.range (K + 1), 0 ≤ increment k)
    (hbase0 : increment 0 ≤ base)
    (hdecay :
      ∀ k ∈ Finset.range K,
        increment (k + 1) ≤ ratio * increment k) :
    FirstBandDecayBudgetSource K increment :=
  ofBudgetSource
    (GeometricBudgetSource.ofBudget
      base ratio error hbase hr0 hr1 hbudget)
    hinc_nonneg hbase0 hdecay

end FirstBandDecayBudgetSource

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
Pointwise geometric-majorant provider for dyadic analytic estimates.

This exposes the concrete majorant `base * ratio^k`, while leaving its finite
sum estimate external.
-/
theorem ofPointwiseGeometricMajorant
    (x K : ℕ)
    (increment : ℕ → ℚ)
    (base ratio : ℚ)
    (hinc_nonneg :
      ∀ k ∈ Finset.range (K + 1), 0 ≤ increment k)
    (hgeom :
      ∀ k ∈ Finset.range (K + 1), increment k ≤ base * ratio ^ k)
    {error : ℝ}
    (hgeom_bound :
      ((Finset.sum (Finset.range (K + 1))
          (fun k : ℕ => base * ratio ^ k) : ℚ) : ℝ) ≤
        1 + error) :
    DyadicBandAnalyticEstimate x K increment error := by
  exact
    ofMajorant x K increment
      (fun k : ℕ => base * ratio ^ k)
      hinc_nonneg hgeom hgeom_bound

/--
Pointwise geometric-majorant provider from the caller-facing finite-sum bound
`base * sum ratio^k <= 1 + error`.

This only factors the constant `base` out of the finite sum.  It does not prove
a closed form for the geometric sum.
-/
theorem ofPointwiseGeometricMajorant_of_geomSumBound
    (x K : ℕ)
    (increment : ℕ → ℚ)
    (base ratio : ℚ)
    (hinc_nonneg :
      ∀ k ∈ Finset.range (K + 1), 0 ≤ increment k)
    (hgeom :
      ∀ k ∈ Finset.range (K + 1), increment k ≤ base * ratio ^ k)
    {error : ℝ}
    (hgeom_sum_bound :
      ((base * Finset.sum (Finset.range (K + 1))
          (fun k : ℕ => ratio ^ k) : ℚ) : ℝ) ≤
        1 + error) :
    DyadicBandAnalyticEstimate x K increment error := by
  apply ofPointwiseGeometricMajorant x K increment base ratio hinc_nonneg hgeom
  simpa [Finset.mul_sum] using hgeom_sum_bound

/--
Pointwise geometric-majorant provider from the one-over-one-minus budget.

This is the convenience wrapper that crosses from the Real geometric-sum
budget theorem back into the rational-valued dyadic provider layer.
-/
theorem ofPointwiseGeometricMajorant_of_baseGeomBudget
    (x K : ℕ)
    (increment : ℕ → ℚ)
    (base ratio : ℚ)
    (hinc_nonneg :
      ∀ k ∈ Finset.range (K + 1), 0 ≤ increment k)
    (hgeom :
      ∀ k ∈ Finset.range (K + 1), increment k ≤ base * ratio ^ k)
    (hbase : 0 ≤ (base : ℝ))
    (hr0 : 0 ≤ (ratio : ℝ))
    (hr1 : (ratio : ℝ) < 1)
    {error : ℝ}
    (hbudget : (base : ℝ) * (1 / (1 - (ratio : ℝ))) ≤ 1 + error) :
    DyadicBandAnalyticEstimate x K increment error := by
  have hreal :
      (base : ℝ) *
        (Finset.sum (Finset.range (K + 1))
          (fun k : ℕ => (ratio : ℝ) ^ k))
        ≤
      1 + error :=
    base_mul_geomSum_range_le_of_base_mul_one_div_le
      K hbase hr0 hr1 hbudget
  have hcast :
      ((base * Finset.sum (Finset.range (K + 1))
          (fun k : ℕ => ratio ^ k) : ℚ) : ℝ)
        =
      (base : ℝ) *
        (Finset.sum (Finset.range (K + 1))
          (fun k : ℕ => (ratio : ℝ) ^ k)) := by
    simp
  exact
    ofPointwiseGeometricMajorant_of_geomSumBound
      x K increment base ratio hinc_nonneg hgeom
      (by simpa [hcast] using hreal)

/--
Pointwise geometric-majorant provider from a packaged geometric budget source.

This wrapper keeps callers from passing the budget side conditions separately.
-/
theorem ofPointwiseGeometricMajorant_of_budgetSource
    (x K : ℕ)
    (increment : ℕ → ℚ)
    (B : GeometricBudgetSource)
    (hinc_nonneg :
      ∀ k ∈ Finset.range (K + 1), 0 ≤ increment k)
    (hgeom :
      ∀ k ∈ Finset.range (K + 1),
        increment k ≤ B.base * B.ratio ^ k) :
    DyadicBandAnalyticEstimate x K increment B.error :=
  ofPointwiseGeometricMajorant_of_baseGeomBudget
    x K increment B.base B.ratio
    hinc_nonneg hgeom
    B.hbase B.hr0 B.hr1 B.hbudget

/--
Provider wrapper from first-band control and uniform step decay.

This builds the pointwise geometric majorant and then applies the packaged
budget-source provider wrapper.
-/
theorem ofFirstBandDecayBudgetSource
    (x K : ℕ)
    (increment : ℕ → ℚ)
    (B : GeometricBudgetSource)
    (hinc_nonneg :
      ∀ k ∈ Finset.range (K + 1), 0 ≤ increment k)
    (hbase0 : increment 0 ≤ B.base)
    (hdecay :
      ∀ k ∈ Finset.range K,
        increment (k + 1) ≤ B.ratio * increment k) :
    DyadicBandAnalyticEstimate x K increment B.error := by
  have hr0_rat : 0 ≤ B.ratio := by
    exact_mod_cast B.hr0
  have hgeom :
      ∀ k ∈ Finset.range (K + 1),
        increment k ≤ B.base * B.ratio ^ k :=
    pointwiseGeometricMajorant_of_firstBand_decay
      K increment B.base B.ratio hbase0 hdecay hr0_rat
  exact
    ofPointwiseGeometricMajorant_of_budgetSource
      x K increment B hinc_nonneg hgeom

/--
Provider wrapper from a packaged first-band / uniform-decay analytic source.

This is the DKMK-017-A ergonomics test for `FirstBandDecayBudgetSource`: the
combined source is accepted only as an input package and still delegates to the
DKMK-016 provider route.
-/
theorem ofFirstBandDecayBudgetSourcePackage
    (x K : ℕ)
    (increment : ℕ → ℚ)
    (S : FirstBandDecayBudgetSource K increment) :
    DyadicBandAnalyticEstimate x K increment S.budget.error :=
  ofFirstBandDecayBudgetSource
    x K increment S.budget S.hinc_nonneg S.hbase0 S.hdecay

/--
Usage wrapper for the zero-ratio budget source.

This checks the caller path
`GeometricBudgetSource.ofZeroRatio ->
ofPointwiseGeometricMajorant_of_budgetSource`.
-/
theorem ofPointwiseZeroRatioMajorant
    (x K : ℕ)
    (increment : ℕ → ℚ)
    (base : ℚ)
    (hinc_nonneg :
      ∀ k ∈ Finset.range (K + 1), 0 ≤ increment k)
    (hgeom :
      ∀ k ∈ Finset.range (K + 1),
        increment k ≤ base * (0 : ℚ) ^ k)
    {error : ℝ}
    (hbase : 0 ≤ (base : ℝ))
    (hbudget : (base : ℝ) ≤ 1 + error) :
    DyadicBandAnalyticEstimate x K increment error := by
  exact
    ofPointwiseGeometricMajorant_of_budgetSource
      x K increment
      (GeometricBudgetSource.ofZeroRatio base error hbase hbudget)
      hinc_nonneg
      (by
        simpa [GeometricBudgetSource.ofZeroRatio] using hgeom)

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
