/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.PascalCenteredXiMultiplicityLocalChargeBridge
import DkMath.RH.CFBRC.CriticalMirrorZeroBridge
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.PascalCenteredXiGlobalZeroDiskBridge"

/-!
# Global centered-Xi zero classification and boundary-safe disks

This module closes the zero-set audit needed before an outer contour is used.
It proves that the fixed Xi kernel has exactly the nontrivial Riemann-zeta
zeros, transports that classification to the coordinate centered at `1 / 2`,
and identifies a closed centered disk with the corresponding PPW window.

The module does **not** identify an outer contour integral with a sum of local
circle integrals.  That is a separate residue-theoretic construction: the
pinned Mathlib version supplies Cauchy-Goursat and Cauchy formula tools, but
not a general argument-principle API.  Accordingly, the outer observables
defined here are only theorem-facing integral definitions and their boundary
regularity facts.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open scoped Topology

/-! ## Phase A: every uncentered Xi zero lies in the open critical strip -/

@[simp] theorem pascalRiemannXiKernel_zero :
    pascalRiemannXiKernel 0 = -1 := by
  simp [pascalRiemannXiKernel]

@[simp] theorem pascalRiemannXiKernel_one :
    pascalRiemannXiKernel 1 = -1 := by
  calc
    pascalRiemannXiKernel 1 = pascalRiemannXiKernel (1 - 0) := by norm_num
    _ = pascalRiemannXiKernel 0 := pascalRiemannXiKernel_one_sub 0
    _ = -1 := pascalRiemannXiKernel_zero

/- The right half-plane exclusion uses only the endpoint value, the
   pole-killed Xi identity, and Mathlib's zeta nonvanishing theorem. -/
theorem pascalRiemannXiKernel_zero_re_lt_one
    {s : ℂ} (hXi : pascalRiemannXiKernel s = 0) :
    s.re < 1 := by
  by_contra hlt
  have hsge : 1 ≤ s.re := le_of_not_gt hlt
  have hs0 : s ≠ 0 := by
    intro hs
    subst s
    norm_num at hXi
  have hs1 : s ≠ 1 := by
    intro hs
    subst s
    norm_num at hXi
  have hspos : 0 < s.re := lt_of_lt_of_le zero_lt_one hsge
  have hfactor : s * (1 - s) ≠ 0 := mul_ne_zero hs0 (sub_ne_zero.mpr hs1.symm)
  have hcompleted : completedRiemannZeta s = 0 := by
    have hmul := pascalRiemannXiKernel_eq_mul_completedRiemannZeta hs0 hs1
    rw [hmul] at hXi
    exact (mul_eq_zero.mp hXi).resolve_left hfactor
  have hzeta : riemannZeta s = 0 :=
    (riemannZeta_eq_zero_iff_completedRiemannZeta_eq_zero hs0
      (gammaR_ne_zero_of_pos_re hspos)).mpr hcompleted
  exact (riemannZeta_ne_zero_of_one_le_re hsge) hzeta

/- The left half-plane exclusion is obtained by reflecting completed zeta;
   no direct expansion of the trivial zeros is used. -/
theorem pascalRiemannXiKernel_zero_re_pos
    {s : ℂ} (hXi : pascalRiemannXiKernel s = 0) :
    0 < s.re := by
  by_contra hpos
  have hsle : s.re ≤ 0 := le_of_not_gt hpos
  have hs0 : s ≠ 0 := by
    intro hs
    subst s
    norm_num at hXi
  have hs1 : s ≠ 1 := by
    intro hs
    subst s
    norm_num at hXi
  have hfactor : s * (1 - s) ≠ 0 := mul_ne_zero hs0 (sub_ne_zero.mpr hs1.symm)
  have hcompleted : completedRiemannZeta s = 0 := by
    have hmul := pascalRiemannXiKernel_eq_mul_completedRiemannZeta hs0 hs1
    rw [hmul] at hXi
    exact (mul_eq_zero.mp hXi).resolve_left hfactor
  have hreflect : completedRiemannZeta (1 - s) = 0 := by
    rw [completedRiemannZeta_one_sub]
    exact hcompleted
  have hReReflect : 1 ≤ (1 - s).re := by
    simp
    linarith
  have hzetaReflect : riemannZeta (1 - s) = 0 :=
    (riemannZeta_eq_zero_iff_completedRiemannZeta_eq_zero
      (by intro h; have := congrArg Complex.re h; norm_num at this
          linarith [hsle])
      (gammaR_ne_zero_of_pos_re (lt_of_lt_of_le zero_lt_one hReReflect))).mpr
      hreflect
  exact (riemannZeta_ne_zero_of_one_le_re hReReflect) hzetaReflect

theorem pascalRiemannXiKernel_zero_mem_openCriticalStrip
    {s : ℂ} (hXi : pascalRiemannXiKernel s = 0) :
    0 < s.re ∧ s.re < 1 :=
  ⟨pascalRiemannXiKernel_zero_re_pos hXi,
    pascalRiemannXiKernel_zero_re_lt_one hXi⟩

/-! ## Phase B: the uncentered global zero classification -/

/- The endpoint exclusions above are what make the open-strip equivalence
   applicable to an arbitrary Xi zero. -/
theorem nontrivialRiemannZetaZero_of_pascalRiemannXiKernel_eq_zero
    {s : ℂ} (hXi : pascalRiemannXiKernel s = 0) :
    NontrivialRiemannZetaZero s := by
  have hstrip := pascalRiemannXiKernel_zero_mem_openCriticalStrip hXi
  have hzeta :=
    (pascalRiemannXiKernel_eq_zero_iff_riemannZeta_eq_zero_of_openCriticalStrip
      hstrip.1 hstrip.2).mp hXi
  refine ⟨hzeta, ?_, ?_⟩
  · rintro ⟨n, hn⟩
    have hre := congrArg Complex.re hn
    simp only [neg_mul, Complex.neg_re, Complex.mul_re, Complex.re_ofNat, Complex.add_re,
      Complex.natCast_re, Complex.one_re, Complex.im_ofNat, Complex.add_im, Complex.natCast_im,
      Complex.one_im, add_zero, mul_zero, sub_zero] at hre
    have hnonpos : s.re ≤ 0 := by
      rw [hre]
      exact neg_nonpos.mpr (mul_nonneg (by norm_num) (by positivity))
    exact (not_lt_of_ge hnonpos) hstrip.1
  · intro hone
    have hre := congrArg Complex.re hone
    simp at hre
    linarith [hstrip.2]

@[simp] theorem pascalRiemannXiKernel_eq_zero_iff_nontrivialRiemannZetaZero
    (s : ℂ) :
    pascalRiemannXiKernel s = 0 ↔ NontrivialRiemannZetaZero s := by
  constructor
  · exact nontrivialRiemannZetaZero_of_pascalRiemannXiKernel_eq_zero
  · exact pascalRiemannXiKernel_eq_zero_of_nontrivialRiemannZetaZero

/-! ## Phase C: the centered global classification -/

@[simp] theorem mem_pascalCenteredXiZeros_iff_nontrivial_shift
    (z : ℂ) :
    z ∈ pascalCenteredXiZeros ↔
      NontrivialRiemannZetaZero (criticalLineCenter + z) := by
  change pascalRiemannXiKernel (criticalLineCenter + z) = 0 ↔ _
  exact pascalRiemannXiKernel_eq_zero_iff_nontrivialRiemannZetaZero _

@[simp] theorem sub_center_mem_pascalCenteredXiZeros_iff_nontrivial
    (s : ℂ) :
    s - criticalLineCenter ∈ pascalCenteredXiZeros ↔
      NontrivialRiemannZetaZero s := by
  rw [mem_pascalCenteredXiZeros_iff_nontrivial_shift]
  rw [show criticalLineCenter + (s - criticalLineCenter) = s by ring]

/-! ## Phase D: finite centered Xi disks -/

/-- The centered closed disk cut out by the global centered Xi zero set. -/
noncomputable def pascalCenteredXiZeroDisk (R : ℝ) : Set ℂ :=
  {z | z ∈ Metric.closedBall 0 R ∧ z ∈ pascalCenteredXiZeros}

@[simp] theorem mem_pascalCenteredXiZeroDisk_iff
    {R : ℝ} {z : ℂ} :
    z ∈ pascalCenteredXiZeroDisk R ↔
      z ∈ Metric.closedBall 0 R ∧ z ∈ pascalCenteredXiZeros := Iff.rfl

theorem finite_pascalCenteredXiZeroDisk (R : ℝ) :
    (pascalCenteredXiZeroDisk R).Finite := by
  change (Metric.closedBall (0 : ℂ) R ∩ pascalCenteredXiZeros).Finite
  exact
    finite_pascalCenteredXiZeros_in_compact (isCompact_closedBall (0 : ℂ) R)

noncomputable def pascalCenteredXiZeroDiskFinset (R : ℝ) : Finset ℂ :=
  (finite_pascalCenteredXiZeroDisk R).toFinset

@[simp] theorem mem_pascalCenteredXiZeroDiskFinset_iff
    {R : ℝ} {z : ℂ} :
    z ∈ pascalCenteredXiZeroDiskFinset R ↔ z ∈ pascalCenteredXiZeroDisk R := by
  simp [pascalCenteredXiZeroDiskFinset]

/-! ## Phase E: exact translation of the PPW window -/

/-- Translate an uncentered zeta zero into the `1 / 2`-centered coordinate. -/
noncomputable def pascalCenterZeroShift (s : ℂ) : ℂ :=
  s - criticalLineCenter

/-- Translate a centered coordinate back to the original zeta coordinate. -/
noncomputable def pascalUncenterZeroShift (z : ℂ) : ℂ :=
  criticalLineCenter + z

@[simp] theorem pascalUncenterZeroShift_centerZeroShift (s : ℂ) :
    pascalUncenterZeroShift (pascalCenterZeroShift s) = s := by
  simp [pascalUncenterZeroShift, pascalCenterZeroShift]

@[simp] theorem pascalCenterZeroShift_uncenterZeroShift (z : ℂ) :
    pascalCenterZeroShift (pascalUncenterZeroShift z) = z := by
  simp [pascalCenterZeroShift, pascalUncenterZeroShift]

@[simp] theorem dist_sub_criticalLineCenter_zero (s : ℂ) :
    dist (s - criticalLineCenter) 0 = dist s criticalLineCenter := by
  simp [dist_eq_norm]

theorem image_pascalCenterZeroShift_window_eq_centeredXiDisk
    (R : ℝ) :
    (pascalCriticalMirrorZeroWindowFinset R).image pascalCenterZeroShift =
      pascalCenteredXiZeroDiskFinset R := by
  classical
  ext z
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨s, hs, rfl⟩
    rw [mem_pascalCenteredXiZeroDiskFinset_iff]
    refine ⟨?_, ?_⟩
    · change dist (s - criticalLineCenter) 0 ≤ R
      rw [dist_sub_criticalLineCenter_zero]
      exact (mem_pascalCriticalMirrorZeroWindowFinset_iff.mp hs).1
    · exact (sub_center_mem_pascalCenteredXiZeros_iff_nontrivial s).mpr
        ((mem_pascalCriticalMirrorZeroWindowFinset_iff.mp hs).2)
  · intro hz
    rw [mem_pascalCenteredXiZeroDiskFinset_iff] at hz
    refine ⟨pascalUncenterZeroShift z, ?_, ?_⟩
    · rw [mem_pascalCriticalMirrorZeroWindowFinset_iff]
      refine ⟨?_, ?_⟩
      · rw [Metric.mem_closedBall]
        have hdist : dist (pascalUncenterZeroShift z) criticalLineCenter = dist z 0 := by
          simp [pascalUncenterZeroShift, dist_eq_norm]
        rw [hdist]
        exact (Metric.mem_closedBall.mp hz.1)
      · exact (mem_pascalCenteredXiZeros_iff_nontrivial_shift z).mp hz.2
    · simp [pascalCenterZeroShift, pascalUncenterZeroShift]

/-! ## Phase F: multiplicity and second-moment transport -/

/-- The intrinsic Xi multiplicity mass of a centered closed disk. -/
noncomputable def pascalCenteredXiZeroDiskMultiplicity (R : ℝ) : ℕ :=
  (pascalCenteredXiZeroDiskFinset R).sum pascalCenteredXiZeroMultiplicity

@[simp] theorem pascalCenteredXiZeroDiskMultiplicity_eq_windowMultiplicity
    (R : ℝ) :
    pascalCenteredXiZeroDiskMultiplicity R =
      pascalCriticalMirrorZeroWindowMultiplicity R := by
  classical
  rw [pascalCenteredXiZeroDiskMultiplicity,
    ← image_pascalCenterZeroShift_window_eq_centeredXiDisk R]
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro s hs
    exact pascalCenteredXiZeroMultiplicity_sub_center_eq_riemannZetaZeroMultiplicity
      ((mem_pascalCriticalMirrorZeroWindowFinset_iff.mp hs).2)
  · intro s hs t ht hst
    have h := congrArg pascalUncenterZeroShift hst
    simpa using h

/-- The holomorphic centered second moment of the disk's Xi zeros. -/
noncomputable def pascalCenteredXiZeroDiskSecondMoment (R : ℝ) : ℂ :=
  ∑ z ∈ pascalCenteredXiZeroDiskFinset R,
    (pascalCenteredXiZeroMultiplicity z : ℂ) * z ^ 2

@[simp] theorem pascalCenteredXiZeroDiskSecondMoment_eq_windowCenteredSecondMoment
    (R : ℝ) :
    pascalCenteredXiZeroDiskSecondMoment R =
      pascalCriticalMirrorZeroWindowCenteredSecondMoment R := by
  classical
  rw [pascalCenteredXiZeroDiskSecondMoment,
    ← image_pascalCenterZeroShift_window_eq_centeredXiDisk R]
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro s hs
    change (pascalCenteredXiZeroMultiplicity (s - criticalLineCenter) : ℂ) *
      (s - criticalLineCenter) ^ 2 = _
    rw [pascalCenteredXiZeroMultiplicity_sub_center_eq_riemannZetaZeroMultiplicity
      ((mem_pascalCriticalMirrorZeroWindowFinset_iff.mp hs).2)]
  · intro s hs t ht hst
    have h := congrArg pascalUncenterZeroShift hst
    simpa using h

/-! ## Phase G: radii whose outer sphere contains no Xi zero -/

/-- A positive radius whose outer sphere contains no centered Xi zero. -/
def IsPascalCenteredXiBoundarySafeRadius (R : ℝ) : Prop :=
  0 < R ∧ ∀ z ∈ Metric.sphere (0 : ℂ) R,
    pascalCenteredRiemannXiKernel z ≠ 0

theorem isPascalCenteredXiBoundarySafeRadius_iff_no_zero_on_sphere
    (R : ℝ) :
    IsPascalCenteredXiBoundarySafeRadius R ↔
      0 < R ∧ ∀ z ∈ Metric.sphere (0 : ℂ) R,
        z ∉ pascalCenteredXiZeros := by
  simp [IsPascalCenteredXiBoundarySafeRadius]

theorem mem_centeredXiZeroDiskFinset_iff_mem_ball_of_boundarySafe
    {R : ℝ} (hR : IsPascalCenteredXiBoundarySafeRadius R) {z : ℂ} :
    z ∈ pascalCenteredXiZeroDiskFinset R ↔
      z ∈ Metric.ball 0 R ∧ z ∈ pascalCenteredXiZeros := by
  rw [mem_pascalCenteredXiZeroDiskFinset_iff]
  constructor
  · rintro ⟨hzball, hzzero⟩
    refine ⟨?_, hzzero⟩
    apply Metric.mem_ball.mpr
    have hzle : dist z 0 ≤ R := Metric.mem_closedBall.mp hzball
    have hne : dist z 0 ≠ R := by
      intro heq
      have hsphere : z ∈ Metric.sphere (0 : ℂ) R := Metric.mem_sphere.mpr heq
      exact hR.2 z hsphere (mem_pascalCenteredXiZeros.mp hzzero)
    exact lt_of_le_of_ne hzle hne
  · rintro ⟨hzball, hzzero⟩
    exact ⟨Metric.mem_closedBall.mpr (le_of_lt (Metric.mem_ball.mp hzball)), hzzero⟩

/-- Every lower threshold has a larger boundary-safe radius. -/
theorem exists_isPascalCenteredXiBoundarySafeRadius_gt
    (A : ℝ) :
    ∃ R : ℝ, A < R ∧ IsPascalCenteredXiBoundarySafeRadius R := by
  let L : ℝ := max A 0
  let U : ℝ := L + 1
  have hLU : L < U := by dsimp [U]; linarith
  let K : Set ℂ := Metric.closedBall (0 : ℂ) U
  let Z : Set ℝ := (K ∩ pascalCenteredXiZeros).image (fun z : ℂ => dist z 0)
  have hZfinite : Z.Finite := by
    exact (finite_pascalCenteredXiZeros_in_compact (isCompact_closedBall (0 : ℂ) U)).image _
  obtain ⟨R, hRinterval, hRnot⟩ :=
    Set.Infinite.exists_notMem_finite (Set.Ioo_infinite hLU) hZfinite
  refine ⟨R, ?_, ?_⟩
  · exact lt_of_le_of_lt (le_max_left A 0) hRinterval.1
  · refine ⟨lt_of_le_of_lt (le_max_right A 0) hRinterval.1, ?_⟩
    intro z hz hXi
    have hzdist : dist z 0 = R := Metric.mem_sphere.mp hz
    have hzzero : z ∈ pascalCenteredXiZeros := mem_pascalCenteredXiZeros.mpr hXi
    have hzK : z ∈ K := by
      rw [Metric.mem_closedBall]
      have hdist' : dist z 0 < U := by linarith [hRinterval.2]
      exact le_of_lt hdist'
    have hzZ : dist z 0 ∈ Z := by
      exact ⟨z, ⟨hzK, hzzero⟩, rfl⟩
    rw [hzdist] at hzZ
    exact hRnot hzZ

/-!
The existence proof above uses only compact finiteness of the discrete zero set:
inside a slightly larger compact disk there are finitely many forbidden radii,
while the open interval between `max A 0` and `max A 0 + 1` is infinite.
-/

/-! ## Phase H: theorem-facing outer contour observables -/

/-- The unweighted centered Xi outer-circle observable.

This definition is intentionally not accompanied by a residue-sum theorem in
this checkpoint; the contour deformation is reserved for the next bridge. -/
noncomputable def pascalCenteredXiOuterContourMass (R : ℝ) : ℂ :=
  circleIntegral pascalCenteredXiNegLogDeriv 0 R

/-- The `z ^ 2`-weighted centered Xi outer-circle observable. -/
noncomputable def pascalCenteredXiSecondOuterContourMass (R : ℝ) : ℂ :=
  circleIntegral (fun z => z ^ 2 * pascalCenteredXiNegLogDeriv z) 0 R

theorem pascalCenteredXiNegLogDeriv_continuousOn_sphere
    {R : ℝ} (hR : IsPascalCenteredXiBoundarySafeRadius R) :
    ContinuousOn pascalCenteredXiNegLogDeriv (Metric.sphere 0 R) := by
  intro z hz
  have hzero : pascalCenteredRiemannXiKernel z ≠ 0 := hR.2 z hz
  change ContinuousWithinAt (fun w => -logDeriv pascalCenteredRiemannXiKernel w)
    (Metric.sphere 0 R) z
  exact ((((analyticAt_pascalCenteredRiemannXiKernel z).deriv.differentiableAt.div
    (analyticAt_pascalCenteredRiemannXiKernel z).differentiableAt hzero).neg).continuousAt
    ).continuousWithinAt

theorem pascalCenteredXiSecondWeightedNegLogDeriv_continuousOn_sphere
    {R : ℝ} (hR : IsPascalCenteredXiBoundarySafeRadius R) :
    ContinuousOn
      (fun z => z ^ 2 * pascalCenteredXiNegLogDeriv z) (Metric.sphere 0 R) := by
  exact (continuousOn_pow 2).mul (pascalCenteredXiNegLogDeriv_continuousOn_sphere hR)

theorem pascalCenteredXiNegLogDeriv_circleIntegrable_of_boundarySafe
    {R : ℝ} (hR : IsPascalCenteredXiBoundarySafeRadius R) :
    CircleIntegrable pascalCenteredXiNegLogDeriv 0 R :=
  ContinuousOn.circleIntegrable hR.1.le
    (pascalCenteredXiNegLogDeriv_continuousOn_sphere hR)

theorem pascalCenteredXiSecondWeightedNegLogDeriv_circleIntegrable_of_boundarySafe
    {R : ℝ} (hR : IsPascalCenteredXiBoundarySafeRadius R) :
    CircleIntegrable
      (fun z => z ^ 2 * pascalCenteredXiNegLogDeriv z) 0 R :=
  ContinuousOn.circleIntegrable hR.1.le
    (pascalCenteredXiSecondWeightedNegLogDeriv_continuousOn_sphere hR)

end DkMath.RH.CFBRCProjection
