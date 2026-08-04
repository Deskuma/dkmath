/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameRotatedTailIntegral
import Mathlib.Analysis.PSeries
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameEtaTailEulerHalf"

set_option linter.style.longLine false

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open MeasureTheory
open scoped Topology
open DkMath.RH.Weave.Analytic

/-- Difference of two consecutive unsigned eta samples. -/
noncomputable def etaAdjacentDifference
    (z : ℂ) (n : ℕ) : ℂ :=
  etaUnsignedVector z n - etaUnsignedVector z (n + 1)

/-- Every adjacent eta difference is the integral over the corresponding unit interval. -/
theorem etaAdjacentDifference_eq_intervalIntegral
    {z : ℂ} (hz : z ≠ 0) (n : ℕ) :
    etaAdjacentDifference z n =
      ∫ x : ℝ in (((n + 1 : ℕ) : ℝ))..(((n + 2 : ℕ) : ℝ)),
        etaPairIntegralKernel z x := by
  let a : ℝ := ((n + 1 : ℕ) : ℝ)
  let b : ℝ := ((n + 2 : ℕ) : ℝ)
  have ha : 0 < a := by
    dsimp [a]
    positivity
  have hab : a ≤ b := by
    dsimp [a, b]
    exact_mod_cast (by omega : n + 1 ≤ n + 2)
  have hcont :
      ContinuousOn (fun x : ℝ => -etaRealKernel z x) (Set.Icc a b) := by
    intro x hx
    exact
      (hasDerivAt_neg_etaRealKernel hz (ha.trans_le hx.1)).continuousAt.continuousWithinAt
  have hderiv :
      ∀ x ∈ Set.Ioo a b,
        HasDerivAt (fun y : ℝ => -etaRealKernel z y)
          (etaPairIntegralKernel z x) x := by
    intro x hx
    exact hasDerivAt_neg_etaRealKernel hz (ha.trans hx.1)
  have hint :
      IntervalIntegrable (etaPairIntegralKernel z) volume a b :=
    etaPairIntegralKernel_intervalIntegrable z ha hab
  have hFTC :
      (∫ x : ℝ in a..b, etaPairIntegralKernel z x) =
        (-etaRealKernel z b) - (-etaRealKernel z a) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
      hab hcont hderiv hint
  have hA : etaRealKernel z a = etaUnsignedVector z n := by
    dsimp [a]
    simpa using etaRealKernel_nat z n
  have hB : etaRealKernel z b = etaUnsignedVector z (n + 1) := by
    dsimp [b]
    simpa [Nat.add_assoc] using etaRealKernel_nat z (n + 1)
  unfold etaAdjacentDifference
  change etaUnsignedVector z n - etaUnsignedVector z (n + 1) =
    ∫ x : ℝ in a..b, etaPairIntegralKernel z x
  rw [hFTC, hA, hB]
  ring

/-- The eta integral kernel is the coefficient times the successor real kernel. -/
theorem etaPairIntegralKernel_eq_mul_etaRealKernel_succ
    (z : ℂ) (x : ℝ) :
    etaPairIntegralKernel z x =
      z * etaRealKernel (z + 1) x := by
  unfold etaPairIntegralKernel etaRealKernel
  congr 1
  ring

/-- Difference of adjacent eta differences, i.e. the discrete second difference. -/
noncomputable def etaPairEulerSecondDifferenceTerm
    (z : ℂ) (j : ℕ) : ℂ :=
  etaAdjacentDifference z (2 * j) -
    etaAdjacentDifference z (2 * j + 1)

/-- The second difference is one integral of the shifted kernel difference. -/
theorem etaPairEulerSecondDifferenceTerm_eq_intervalIntegral
    {z : ℂ} (hz : z ≠ 0) (j : ℕ) :
    etaPairEulerSecondDifferenceTerm z j =
      ∫ x : ℝ in
          (((2 * j + 1 : ℕ) : ℝ))..(((2 * j + 2 : ℕ) : ℝ)),
        etaPairIntegralKernel z x - etaPairIntegralKernel z (x + 1) := by
  let a : ℝ := ((2 * j + 1 : ℕ) : ℝ)
  have ha : 0 < a := by
    dsimp [a]
    positivity
  have hab : a ≤ a + 1 := by linarith
  have hfirst :
      IntervalIntegrable (etaPairIntegralKernel z) volume a (a + 1) :=
    etaPairIntegralKernel_intervalIntegrable z ha hab
  have hsecond :
      IntervalIntegrable (etaPairIntegralKernel z) volume (a + 1) (a + 2) :=
    etaPairIntegralKernel_intervalIntegrable z (by linarith) (by linarith)
  have hshiftInt :
      IntervalIntegrable
        (fun x : ℝ => etaPairIntegralKernel z (x + 1)) volume a (a + 1) := by
    have h := hsecond.comp_add_right (1 : ℝ)
    convert h using 1 <;> ring
  have hshift :
      (∫ x : ℝ in a..(a + 1), etaPairIntegralKernel z (x + 1)) =
        ∫ x : ℝ in (a + 1)..(a + 2), etaPairIntegralKernel z x := by
    simpa [add_assoc] using
      (intervalIntegral.integral_comp_add_right
        (etaPairIntegralKernel z) (1 : ℝ) :
        (∫ x : ℝ in a..(a + 1), etaPairIntegralKernel z (x + 1)) =
          ∫ x : ℝ in (a + 1)..(a + 1 + 1), etaPairIntegralKernel z x)
  rw [etaPairEulerSecondDifferenceTerm]
  rw [etaAdjacentDifference_eq_intervalIntegral hz]
  rw [etaAdjacentDifference_eq_intervalIntegral hz]
  change
    (∫ x : ℝ in a..(a + 1), etaPairIntegralKernel z x) -
        (∫ x : ℝ in (a + 1)..(a + 2), etaPairIntegralKernel z x) = _
  rw [← hshift]
  exact (intervalIntegral.integral_sub hfirst hshiftInt).symm

/-- Pointwise one-extra-power bound for the shifted eta-kernel difference. -/
theorem norm_etaPairIntegralKernel_sub_shift_le
    {z : ℂ} (hzre : 0 < z.re) {x : ℝ} (hx : 0 < x) :
    ‖etaPairIntegralKernel z x - etaPairIntegralKernel z (x + 1)‖ ≤
      ‖z‖ * ‖z + 1‖ * x ^ (-z.re - 2) := by
  have hz1re : 0 < (z + 1).re := by
    simp
    linarith
  have hraw :=
    norm_etaRealKernel_sub_le
      (s := z + 1) hz1re hx (by linarith : x ≤ x + 1)
  have hstep : x + 1 - x = 1 := by ring
  rw [hstep, mul_one] at hraw
  have hrev :
      ‖etaRealKernel (z + 1) x - etaRealKernel (z + 1) (x + 1)‖ ≤
        ‖z + 1‖ * x ^ (-z.re - 2) := by
    convert hraw using 1
    · rw [norm_sub_rev]
    · simp
      ring
  rw [etaPairIntegralKernel_eq_mul_etaRealKernel_succ]
  rw [etaPairIntegralKernel_eq_mul_etaRealKernel_succ]
  rw [← mul_sub, norm_mul]
  exact mul_le_mul_of_nonneg_left hrev (norm_nonneg z)

/-- The discrete second difference gains two powers locally. -/
theorem norm_etaPairEulerSecondDifferenceTerm_le
    {z : ℂ} (hzre : 0 < z.re) (j : ℕ) :
    ‖etaPairEulerSecondDifferenceTerm z j‖ ≤
      ‖z‖ * ‖z + 1‖ *
        (((2 * j + 1 : ℕ) : ℝ) ^ (-z.re - 2)) := by
  have hz : z ≠ 0 := by
    intro hzero
    simp [hzero] at hzre
  let a : ℝ := ((2 * j + 1 : ℕ) : ℝ)
  have ha : 0 < a := by
    dsimp [a]
    positivity
  have hab : a ≤ a + 1 := by linarith
  rw [etaPairEulerSecondDifferenceTerm_eq_intervalIntegral hz]
  change
    ‖∫ x : ℝ in a..(a + 1),
        etaPairIntegralKernel z x - etaPairIntegralKernel z (x + 1)‖ ≤ _
  have hbound :=
    intervalIntegral.norm_integral_le_of_norm_le_const
      (a := a) (b := a + 1)
      (C := ‖z‖ * ‖z + 1‖ * a ^ (-z.re - 2))
      (f := fun x : ℝ =>
        etaPairIntegralKernel z x - etaPairIntegralKernel z (x + 1))
      (fun x hxmem => by
        rw [Set.uIoc_of_le hab] at hxmem
        have hxpos : 0 < x := ha.trans hxmem.1
        have hpoint := norm_etaPairIntegralKernel_sub_shift_le hzre hxpos
        have hexp : -z.re - 2 ≤ 0 := by linarith
        have hrpow :
            x ^ (-z.re - 2) ≤ a ^ (-z.re - 2) :=
          Real.antitoneOn_rpow_Ioi_of_exponent_nonpos hexp
            ha hxpos hxmem.1.le
        exact hpoint.trans
          (mul_le_mul_of_nonneg_left hrpow
            (mul_nonneg (norm_nonneg z) (norm_nonneg (z + 1)))))
  simpa [a] using hbound

/-- Half of the second difference, the Euler half-endpoint remainder term. -/
noncomputable def etaPairEulerRemainderTerm
    (z : ℂ) (j : ℕ) : ℂ :=
  ((1 : ℂ) / 2) * etaPairEulerSecondDifferenceTerm z j

/-- Explicit local bound for one Euler remainder term. -/
theorem norm_etaPairEulerRemainderTerm_le
    {z : ℂ} (hzre : 0 < z.re) (j : ℕ) :
    ‖etaPairEulerRemainderTerm z j‖ ≤
      (‖z‖ * ‖z + 1‖ / 2) *
        (((2 * j + 1 : ℕ) : ℝ) ^ (-z.re - 2)) := by
  have hsecond := norm_etaPairEulerSecondDifferenceTerm_le hzre j
  unfold etaPairEulerRemainderTerm
  rw [norm_mul]
  have hhalf : ‖((1 : ℂ) / 2)‖ = (1 : ℝ) / 2 := by norm_num
  rw [hhalf]
  calc
    (1 / 2 : ℝ) * ‖etaPairEulerSecondDifferenceTerm z j‖ ≤
        (1 / 2 : ℝ) *
          (‖z‖ * ‖z + 1‖ *
            (((2 * j + 1 : ℕ) : ℝ) ^ (-z.re - 2))) :=
      mul_le_mul_of_nonneg_left hsecond (by norm_num)
    _ = (‖z‖ * ‖z + 1‖ / 2) *
          (((2 * j + 1 : ℕ) : ℝ) ^ (-z.re - 2)) := by ring

/-- Coarser successor-index bound used for summability and tail integration. -/
theorem norm_etaPairEulerRemainderTerm_le_shifted
    {z : ℂ} (hzre : 0 < z.re) (j : ℕ) :
    ‖etaPairEulerRemainderTerm z j‖ ≤
      (‖z‖ * ‖z + 1‖ / 2) *
        (((j + 1 : ℕ) : ℝ) ^ (-z.re - 2)) := by
  have hlocal := norm_etaPairEulerRemainderTerm_le hzre j
  have hExp : -z.re - 2 ≤ 0 := by linarith
  have hjpos : 0 < (((j + 1 : ℕ) : ℝ)) := by positivity
  have h2jpos : 0 < (((2 * j + 1 : ℕ) : ℝ)) := by positivity
  have hle :
      (((j + 1 : ℕ) : ℝ)) ≤ (((2 * j + 1 : ℕ) : ℝ)) := by
    exact_mod_cast (by omega : j + 1 ≤ 2 * j + 1)
  have hrpow :
      (((2 * j + 1 : ℕ) : ℝ) ^ (-z.re - 2)) ≤
        (((j + 1 : ℕ) : ℝ) ^ (-z.re - 2)) :=
    Real.antitoneOn_rpow_Ioi_of_exponent_nonpos hExp
      hjpos h2jpos hle
  exact hlocal.trans
    (mul_le_mul_of_nonneg_left hrpow
      (div_nonneg
        (mul_nonneg (norm_nonneg z) (norm_nonneg (z + 1)))
        (by norm_num)))

/-- Shifted two-extra-power sequence is summable on the open right half-plane. -/
private theorem summable_etaPairEuler_shifted_power
    {a : ℝ} (ha : 0 < a) :
    Summable
      (fun j : ℕ => (((j + 1 : ℕ) : ℝ) ^ (-a - 2))) := by
  have hp : 1 < a + 2 := by linarith
  have hbase :
      Summable (fun n : ℕ => (n : ℝ) ^ (-(a + 2))) := by
    simpa only [one_div, Real.rpow_neg (Nat.cast_nonneg _)] using
      (Real.summable_one_div_nat_rpow.2 hp)
  have hshift := (summable_nat_add_iff 1).2 hbase
  simpa [show -a - 2 = -(a + 2) by ring] using hshift

/-- The complete Euler remainder series is absolutely summable. -/
theorem summable_etaPairEulerRemainderTerm
    {z : ℂ} (hzre : 0 < z.re) :
    Summable (etaPairEulerRemainderTerm z) := by
  have hpow := summable_etaPairEuler_shifted_power hzre
  have hmajorant := hpow.mul_left (‖z‖ * ‖z + 1‖ / 2)
  exact hmajorant.of_norm_bounded
    (norm_etaPairEulerRemainderTerm_le_shifted hzre)

/-- Euler remainder tail beginning at pair index `K`. -/
noncomputable def etaPairEulerRemainderTail
    (K : ℕ) (z : ℂ) : ℂ :=
  ∑' j : ℕ, etaPairEulerRemainderTerm z (j + K)

/-- Every shifted Euler remainder tail is summable. -/
theorem summable_etaPairEulerRemainderTail
    {z : ℂ} (hzre : 0 < z.re) (K : ℕ) :
    Summable (fun j : ℕ => etaPairEulerRemainderTerm z (j + K)) :=
  (summable_nat_add_iff K).2 (summable_etaPairEulerRemainderTerm hzre)

/-- The Euler remainder tail has one extra power after summation. -/
theorem norm_etaPairEulerRemainderTail_le
    {z : ℂ} (hzre : 0 < z.re)
    {K : ℕ} (hK : 1 ≤ K) :
    ‖etaPairEulerRemainderTail K z‖ ≤
      (‖z‖ * ‖z + 1‖ / 2) *
        (((K : ℝ) ^ (-z.re - 1)) / (z.re + 1)) := by
  let C : ℝ := ‖z‖ * ‖z + 1‖ / 2
  have hpow := summable_etaPairEuler_shifted_power hzre
  have hshiftPow :
      Summable
        (fun j : ℕ =>
          (((j + K + 1 : ℕ) : ℝ) ^ (-z.re - 2))) :=
    (summable_nat_add_iff K).2 hpow
  have hmajorant := hshiftPow.mul_left C
  have hnorm :
      ‖etaPairEulerRemainderTail K z‖ ≤
        ∑' j : ℕ,
          C * (((j + K + 1 : ℕ) : ℝ) ^ (-z.re - 2)) := by
    unfold etaPairEulerRemainderTail
    exact
      tsum_of_norm_bounded hmajorant.hasSum
        (fun j => by
          dsimp [C]
          simpa [Nat.add_assoc] using
            norm_etaPairEulerRemainderTerm_le_shifted hzre (j + K))
  have hfactor :
      (∑' j : ℕ,
        C * (((j + K + 1 : ℕ) : ℝ) ^ (-z.re - 2))) =
        C *
          (∑' j : ℕ,
            (((j + K + 1 : ℕ) : ℝ) ^ (-z.re - 2))) :=
    (hshiftPow.hasSum.mul_left C).tsum_eq
  rw [hfactor] at hnorm
  have htail := shifted_rpow_tail_le (by linarith : 0 < z.re + 1) hK
  have htail' :
      (∑' j : ℕ,
        (((j + K + 1 : ℕ) : ℝ) ^ (-z.re - 2))) ≤
        ((K : ℝ) ^ (-z.re - 1)) / (z.re + 1) := by
    convert htail using 1
    · apply tsum_congr
      intro j
      congr 1
      ring
    · ring_nf
  exact hnorm.trans
    (mul_le_mul_of_nonneg_left htail'
      (by
        dsimp [C]
        positivity))

/-- The half-endpoint telescoping term in one eta pair. -/
noncomputable def etaPairEulerMainDifferenceTerm
    (z : ℂ) (j : ℕ) : ℂ :=
  ((1 : ℂ) / 2) *
    (etaUnsignedVector z (2 * j) -
      etaUnsignedVector z (2 * (j + 1)))

/-- Exact termwise Euler split of one eta pair. -/
theorem etaPairTerm_eq_eulerMainDifference_add_remainder
    (z : ℂ) (j : ℕ) :
    etaPairTerm z j =
      etaPairEulerMainDifferenceTerm z j +
        etaPairEulerRemainderTerm z j := by
  unfold etaPairTerm etaPairEulerMainDifferenceTerm
  unfold etaPairEulerRemainderTerm etaPairEulerSecondDifferenceTerm
  unfold etaAdjacentDifference
  ring

/-- The shifted half-endpoint difference series is summable. -/
theorem summable_etaPairEulerMainDifferenceTail
    {z : ℂ} (hzre : 0 < z.re) (K : ℕ) :
    Summable (fun j : ℕ => etaPairEulerMainDifferenceTerm z (j + K)) := by
  have hpair := summable_etaPairTail hzre K
  have hrem := summable_etaPairEulerRemainderTail hzre K
  have hsub := hpair.sub hrem
  refine hsub.congr ?_
  intro j
  rw [etaPairTerm_eq_eulerMainDifference_add_remainder]
  ring

/-- Cofinality of a fixed natural successor shift. -/
private theorem tendsto_nat_add_const_atTop_euler
    (K : ℕ) :
    Tendsto (fun N : ℕ => N + K) atTop atTop := by
  refine tendsto_atTop.2 ?_
  intro n
  exact eventually_atTop.2 ⟨n, by
    intro N hN
    omega⟩

/-- The shifted half-endpoint difference series telescopes exactly. -/
theorem tsum_etaPairEulerMainDifferenceTail
    {z : ℂ} (hzre : 0 < z.re) (K : ℕ) :
    (∑' j : ℕ, etaPairEulerMainDifferenceTerm z (j + K)) =
      ((1 : ℂ) / 2) * etaUnsignedVector z (2 * K) := by
  have hsum := summable_etaPairEulerMainDifferenceTail hzre K
  have hfinite :
      ∀ N : ℕ,
        (Finset.range N).sum
            (fun j : ℕ => etaPairEulerMainDifferenceTerm z (j + K)) =
          ((1 : ℂ) / 2) *
            (etaUnsignedVector z (2 * K) -
              etaUnsignedVector z (2 * (N + K))) := by
    intro N
    induction N with
    | zero => simp [etaPairEulerMainDifferenceTerm]
    | succ N ih =>
        rw [Finset.sum_range_succ, ih]
        unfold etaPairEulerMainDifferenceTerm
        have hidx : 2 * (N + K + 1) = 2 * (N + 1 + K) := by omega
        rw [hidx]
        ring
  have hrem :
      Tendsto
        (fun N : ℕ => etaUnsignedVector z (2 * (N + K)))
        atTop (nhds 0) := by
    have htwo := etaUnsignedVector_two_mul_tendsto_zero_of_pos_re hzre
    exact htwo.comp (tendsto_nat_add_const_atTop_euler K)
  have htend :
      Tendsto
        (fun N : ℕ =>
          ((1 : ℂ) / 2) *
            (etaUnsignedVector z (2 * K) -
              etaUnsignedVector z (2 * (N + K))))
        atTop
        (nhds (((1 : ℂ) / 2) * etaUnsignedVector z (2 * K))) := by
    simpa using
      tendsto_const_nhds.mul
        (tendsto_const_nhds.sub hrem)
  have hpartial :
      Tendsto
        (fun N : ℕ =>
          (Finset.range N).sum
            (fun j : ℕ => etaPairEulerMainDifferenceTerm z (j + K)))
        atTop
        (nhds (((1 : ℂ) / 2) * etaUnsignedVector z (2 * K))) := by
    refine htend.congr' (Eventually.of_forall fun N => ?_)
    exact (hfinite N).symm
  exact ((hsum.hasSum_iff_tendsto_nat).2 hpartial).tsum_eq

/-- Exact Euler half-endpoint decomposition of every paired eta tail. -/
theorem etaPairTail_eq_half_endpoint_add_eulerRemainderTail
    {z : ℂ} (hzre : 0 < z.re) (K : ℕ) :
    etaPairTail K z =
      ((1 : ℂ) / 2) * etaUnsignedVector z (2 * K) +
        etaPairEulerRemainderTail K z := by
  have hmain := summable_etaPairEulerMainDifferenceTail hzre K
  have hrem := summable_etaPairEulerRemainderTail hzre K
  have hsum :
      HasSum
        (fun j : ℕ => etaPairTerm z (j + K))
        ((∑' j : ℕ, etaPairEulerMainDifferenceTerm z (j + K)) +
          ∑' j : ℕ, etaPairEulerRemainderTerm z (j + K)) := by
    refine (hmain.hasSum.add hrem.hasSum).congr ?_
    intro j
    exact (etaPairTerm_eq_eulerMainDifference_add_remainder z (j + K)).symm
  unfold etaPairTail etaPairEulerRemainderTail
  rw [hsum.tsum_eq]
  rw [tsum_etaPairEulerMainDifferenceTail hzre K]

end DkMath.RH.CFBRCProjection
