/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.RH.CFBRC.PascalCenteredXiPrimeSideFiniteResidualMirrorPairedHalfIntervalAudit
import Mathlib.Tactic

/-!
# CS36: the finite mirror pair and the completed-zeta fold

This file records the exact finite functional-equation representation carried
by the CS35 mirror pair.  The Euler object is a finite sum, and every use of
the zeta functional equation is pointwise.  No infinite Euler product,
limiting interchange, sign provider, or RH conclusion is introduced.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open DkMath.Analysis
open DkMath.NumberTheory
open DkMath.NumberTheory.PrimitiveSet
open Filter
open MeasureTheory
open Set
open scoped ComplexConjugate Interval Topology

/-! ## CS36-A/B: ordinary mirror geometry and finite potential -/

theorem pascalCenteredXiPrimeSideFiniteResidualMirror_conj_top_eq_one_sub
    (u T : ℝ) :
    starRingEnd ℂ
        (pascalSymmetricRectangleTopEdge (1 - u) T) =
      1 - pascalSymmetricRectangleTopEdge u T := by
  rw [pascalCenteredXiPrimeSideFiniteResidualTopEdge_mirror]
  simp

private theorem eulerPrimePowerMode_conj_cs36
    {p j : ℕ} (hp : Nat.Prime p) (s : ℂ) :
    eulerPrimePowerMode p j (starRingEnd ℂ s) =
      starRingEnd ℂ (eulerPrimePowerMode p j s) := by
  rw [eulerPrimePowerMode_eq_primePower_cpow_neg hp,
    eulerPrimePowerMode_eq_primePower_cpow_neg hp]
  by_cases hj : j = 0
  · subst j
    simp
  · have harg : ((p ^ j : ℕ) : ℂ).arg ≠ Real.pi := by
      rw [Complex.natCast_arg]
      exact ne_of_lt Real.pi_pos
    simpa [Complex.natCast_arg] using
      (Complex.conj_cpow ((p ^ j : ℕ) : ℂ)
        (-(starRingEnd ℂ s)) harg)

theorem pascalCenteredXiPrimeSideFiniteEulerLogPotential_conj
    (X : ℕ) (s : ℂ) :
    pascalCenteredXiPrimeSideFiniteEulerLogPotential X
        (starRingEnd ℂ s) =
      starRingEnd ℂ
        (pascalCenteredXiPrimeSideFiniteEulerLogPotential X s) := by
  classical
  unfold pascalCenteredXiPrimeSideFiniteEulerLogPotential
  simp only [map_sum, map_mul, map_inv₀]
  apply Finset.sum_congr rfl
  intro pk hpk
  have hs := mem_pascalPrimePowerPairSupportUpTo_iff.mp hpk
  have hp : Nat.Prime pk.1 :=
    (mem_pascalPrimeCoordinateSupportUpTo_iff.mp hs.1).1
  rw [eulerPrimePowerMode_conj_cs36 hp]
  norm_num

theorem pascalCenteredXiPrimeSideFiniteEulerCompensator_conj
    (X : ℕ) (s : ℂ) :
    starRingEnd ℂ
        (pascalCenteredXiPrimeSideFiniteEulerCompensator X
          (starRingEnd ℂ s)) =
      pascalCenteredXiPrimeSideFiniteEulerCompensator X s := by
  unfold pascalCenteredXiPrimeSideFiniteEulerCompensator
  rw [← Complex.exp_conj]
  congr 1
  rw [map_neg, pascalCenteredXiPrimeSideFiniteEulerLogPotential_conj]
  simp

theorem pascalCenteredXiPrimeSideFiniteEulerRenormalizedZetaResidual_conj
    (X : ℕ) (s : ℂ) :
    starRingEnd ℂ
        (pascalCenteredXiPrimeSideFiniteEulerRenormalizedZetaResidual X
          (starRingEnd ℂ s)) =
      pascalCenteredXiPrimeSideFiniteEulerRenormalizedZetaResidual X s := by
  unfold pascalCenteredXiPrimeSideFiniteEulerRenormalizedZetaResidual
  rw [map_mul, riemannZeta_conj,
    pascalCenteredXiPrimeSideFiniteEulerCompensator_conj]
  simp only [starRingEnd_apply, star_star]

/-! ## CS36-C/D: exact finite paired factorisation -/

noncomputable def pascalCenteredXiPrimeSideFiniteEulerSymmetricPotential
    (X : ℕ) (s : ℂ) : ℂ :=
  pascalCenteredXiPrimeSideFiniteEulerLogPotential X s +
    pascalCenteredXiPrimeSideFiniteEulerLogPotential X (1 - s)

theorem pascalCenteredXiPrimeSideFiniteEulerSymmetricPotential_mirror
    (X : ℕ) (s : ℂ) :
    pascalCenteredXiPrimeSideFiniteEulerSymmetricPotential X (1 - s) =
      pascalCenteredXiPrimeSideFiniteEulerSymmetricPotential X s := by
  unfold pascalCenteredXiPrimeSideFiniteEulerSymmetricPotential
  have h : 1 - (1 - s) = s := by ring
  rw [h]
  ring

theorem pascalCenteredXiPrimeSideFiniteEulerSymmetricCompensator_ne_zero
    (X : ℕ) (s : ℂ) :
    Complex.exp
        (-pascalCenteredXiPrimeSideFiniteEulerSymmetricPotential X s) ≠ 0 := by
  exact Complex.exp_ne_zero _

theorem pascalCenteredXiPrimeSideFiniteResidualMirrorPair_factorization
    (X : ℕ) (W : PascalCenteredXiResidueTransportWindow) (u : ℝ) :
    pascalCenteredXiPrimeSideFiniteResidualMirrorPair X W u =
      riemannZeta (pascalSymmetricRectangleTopEdge u W.rectangle.T) *
        riemannZeta (1 - pascalSymmetricRectangleTopEdge u W.rectangle.T) *
        Complex.exp
          (-pascalCenteredXiPrimeSideFiniteEulerSymmetricPotential X
            (pascalSymmetricRectangleTopEdge u W.rectangle.T)) := by
  unfold pascalCenteredXiPrimeSideFiniteResidualMirrorPair
    pascalCenteredXiPrimeSideFiniteResidualTopPath
  have hres :=
    pascalCenteredXiPrimeSideFiniteEulerRenormalizedZetaResidual_conj X
      (starRingEnd ℂ
        (pascalSymmetricRectangleTopEdge (1 - u) W.rectangle.T))
  have hmirror :=
    pascalCenteredXiPrimeSideFiniteResidualMirror_conj_top_eq_one_sub
      u W.rectangle.T
  have hres' :
      starRingEnd ℂ
          (pascalCenteredXiPrimeSideFiniteEulerRenormalizedZetaResidual X
            (pascalSymmetricRectangleTopEdge (1 - u) W.rectangle.T)) =
        pascalCenteredXiPrimeSideFiniteEulerRenormalizedZetaResidual X
          (1 - pascalSymmetricRectangleTopEdge u W.rectangle.T) := by
    calc
      _ = pascalCenteredXiPrimeSideFiniteEulerRenormalizedZetaResidual X
          (starRingEnd ℂ
            (pascalSymmetricRectangleTopEdge (1 - u) W.rectangle.T)) := by
              simpa only [starRingEnd_apply, star_star] using hres
      _ = _ := by rw [hmirror]
  rw [hres']
  unfold pascalCenteredXiPrimeSideFiniteEulerRenormalizedZetaResidual
    pascalCenteredXiPrimeSideFiniteEulerCompensator
    pascalCenteredXiPrimeSideFiniteEulerSymmetricPotential
  calc
    _ = riemannZeta (pascalSymmetricRectangleTopEdge u W.rectangle.T) *
        riemannZeta (1 - pascalSymmetricRectangleTopEdge u W.rectangle.T) *
        (Complex.exp
          (-pascalCenteredXiPrimeSideFiniteEulerLogPotential X
            (pascalSymmetricRectangleTopEdge u W.rectangle.T)) *
          Complex.exp
            (-pascalCenteredXiPrimeSideFiniteEulerLogPotential X
              (1 - pascalSymmetricRectangleTopEdge u W.rectangle.T))) := by
          ring
    _ = riemannZeta (pascalSymmetricRectangleTopEdge u W.rectangle.T) *
        riemannZeta (1 - pascalSymmetricRectangleTopEdge u W.rectangle.T) *
        Complex.exp
          (-pascalCenteredXiPrimeSideFiniteEulerLogPotential X
              (pascalSymmetricRectangleTopEdge u W.rectangle.T) +
            -pascalCenteredXiPrimeSideFiniteEulerLogPotential X
              (1 - pascalSymmetricRectangleTopEdge u W.rectangle.T)) := by
          rw [← Complex.exp_add]
    _ = _ := by congr 3; ring

theorem pascalCenteredXiPrimeSideFiniteResidualMirrorPair_factorization_ne_zero
    {W : PascalCenteredXiResidueTransportWindow}
    (hSafe : IsPascalCenteredXiTopLogDerivDecompositionSafe W)
    {X : ℕ} {u : ℝ}
    (hu : u ∈ Set.uIcc W.rectangle.σ (1 - W.rectangle.σ)) :
    riemannZeta (pascalSymmetricRectangleTopEdge u W.rectangle.T) *
        riemannZeta (1 - pascalSymmetricRectangleTopEdge u W.rectangle.T) *
        Complex.exp
          (-pascalCenteredXiPrimeSideFiniteEulerSymmetricPotential X
            (pascalSymmetricRectangleTopEdge u W.rectangle.T)) ≠ 0 := by
  rw [← pascalCenteredXiPrimeSideFiniteResidualMirrorPair_factorization]
  exact pascalCenteredXiPrimeSideFiniteResidualMirrorPair_ne_zero hSafe hu

/-! ## CS36-E: the installed completed-zeta normalisation -/

theorem riemannZeta_mul_one_sub_eq_completedRiemannZeta_sq_div_GammaR_pair
    {s : ℂ} (hs0 : s ≠ 0) (h1s0 : 1 - s ≠ 0) :
    riemannZeta s * riemannZeta (1 - s) =
      completedRiemannZeta s ^ 2 /
        (Complex.Gammaℝ s * Complex.Gammaℝ (1 - s)) := by
  rw [riemannZeta_def_of_ne_zero hs0,
    riemannZeta_def_of_ne_zero h1s0,
    completedRiemannZeta_one_sub]
  ring

theorem pascalCenteredXiPrimeSideFiniteResidualMirrorPair_factorization_completed
    (X : ℕ) (W : PascalCenteredXiResidueTransportWindow) (u : ℝ)
    (hs0 : pascalSymmetricRectangleTopEdge u W.rectangle.T ≠ 0)
    (h1s0 : 1 - pascalSymmetricRectangleTopEdge u W.rectangle.T ≠ 0) :
    pascalCenteredXiPrimeSideFiniteResidualMirrorPair X W u =
      (completedRiemannZeta
          (pascalSymmetricRectangleTopEdge u W.rectangle.T) ^ 2 /
        (Complex.Gammaℝ (pascalSymmetricRectangleTopEdge u W.rectangle.T) *
          Complex.Gammaℝ
            (1 - pascalSymmetricRectangleTopEdge u W.rectangle.T))) *
        Complex.exp
          (-pascalCenteredXiPrimeSideFiniteEulerSymmetricPotential X
            (pascalSymmetricRectangleTopEdge u W.rectangle.T)) := by
  rw [pascalCenteredXiPrimeSideFiniteResidualMirrorPair_factorization,
    riemannZeta_mul_one_sub_eq_completedRiemannZeta_sq_div_GammaR_pair
      hs0 h1s0]

/-! ## CS36-F/G: center consistency and the remaining source frontier -/

theorem pascalCenteredXiPrimeSideFiniteResidualMirrorPair_center_factorization_consistent
    {W : PascalCenteredXiResidueTransportWindow}
    (hSafe : IsPascalCenteredXiTopLogDerivDecompositionSafe W)
    {X : ℕ} :
    pascalCenteredXiPrimeSideFiniteResidualMirrorPair X W (1 / 2 : ℝ) =
      Complex.normSq
        (pascalCenteredXiPrimeSideFiniteResidualTopPath X W (1 / 2 : ℝ)) :=
  pascalCenteredXiPrimeSideFiniteResidualMirrorPair_center hSafe

theorem pascalCenteredXiPrimeSideFiniteResidualMirrorPair_center_factorization_re
    {W : PascalCenteredXiResidueTransportWindow}
    (hSafe : IsPascalCenteredXiTopLogDerivDecompositionSafe W)
    {X : ℕ} :
    0 <
      (pascalCenteredXiPrimeSideFiniteResidualMirrorPair X W
        (1 / 2 : ℝ)).re :=
  pascalCenteredXiPrimeSideFiniteResidualMirrorPair_center_re_pos hSafe

inductive PascalCenteredXiPrimeSideFiniteResidualMirrorFunctionalEquationReachGap : Prop
  | no_independent_paired_functional_equation_reach_estimate

end DkMath.RH.CFBRCProjection
