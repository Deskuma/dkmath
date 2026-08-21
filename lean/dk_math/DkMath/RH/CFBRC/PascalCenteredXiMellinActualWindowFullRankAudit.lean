/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.PascalCenteredXiMellinFiniteEvaluationRankAudit
import DkMath.RH.CFBRC.PascalCenteredXiActualWindowVariableWeightRankTransfer
import DkMath.RH.CFBRC.PascalCenteredXiMellinArithmeticSpecialization
import DkMath.RH.CFBRC.PascalCenteredXiMellinLowRankAudit
import Mathlib.Tactic

/-!
# Actual-window full Mellin rank on squared Xi orbits

This module transfers the general finite-evaluation theorem to the actual
finite centered-Xi zero window.  The finite coordinate space is the image of
the window under `z ↦ z ^ 2`; one representative is chosen only to present
that finite space on a `Fin` index type.  The canonical Mellin family is then
obtained from the bare kernel by exact nonzero column scaling for sufficiently
small positive box widths.

The zero moment is handled by the same squared-orbit carrier: even weights
are constant on equal-square fibers, so the actual weighted moment is the
canonical Mellin evaluation matrix applied to the vector of orbit masses.
No Xi representative is promoted to an independent analytic family, and no
actual-window claim is made for `z` and `-z` separately.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open DkMath.Analysis
open Filter
open scoped BigOperators Matrix

/-! ## C2-A: squared-orbit carrier and representatives -/

/-- The finite carrier of distinct squared centered-Xi coordinates in the
actual radius-`R` window. -/
noncomputable def pascalCenteredXiSquaredOrbitFinset (R : ℝ) : Finset ℂ :=
  (pascalCenteredXiZeroDiskFinset R).image (fun z => z ^ 2)

/-- Membership in the squared-orbit carrier is witnessed by an actual window
point with the indicated square. -/
theorem mem_pascalCenteredXiSquaredOrbitFinset_iff
    {R : ℝ} {q : ℂ} :
    q ∈ pascalCenteredXiSquaredOrbitFinset R ↔
      ∃ z ∈ pascalCenteredXiZeroDiskFinset R, z ^ 2 = q := by
  simp [pascalCenteredXiSquaredOrbitFinset]

/-- Every actual squared orbit is nonzero. -/
theorem pascalCenteredXiSquaredOrbitFinset_sq_ne_zero
    {R : ℝ} {q : ℂ}
    (hq : q ∈ pascalCenteredXiSquaredOrbitFinset R) :
    q ≠ 0 := by
  rcases (mem_pascalCenteredXiSquaredOrbitFinset_iff.mp hq) with ⟨z, hz, rfl⟩
  exact pascalCenteredXiZeroDiskFinset_sq_ne_zero hz

/-- A classical representative of an actual squared orbit.  This is only a
finite coordinate presentation of the image carrier. -/
noncomputable def pascalCenteredXiSquaredOrbitRepresentative
    (R : ℝ) (q : ↥(pascalCenteredXiSquaredOrbitFinset R)) : ℂ :=
  Classical.choose (mem_pascalCenteredXiSquaredOrbitFinset_iff.mp q.property)

/-- The chosen squared-orbit representative lies in the actual window. -/
theorem pascalCenteredXiSquaredOrbitRepresentative_mem
    {R : ℝ} (q : ↥(pascalCenteredXiSquaredOrbitFinset R)) :
    pascalCenteredXiSquaredOrbitRepresentative R q ∈
      pascalCenteredXiZeroDiskFinset R := by
  exact (Classical.choose_spec
    (mem_pascalCenteredXiSquaredOrbitFinset_iff.mp q.property)).1

/-- The chosen representative has the squared orbit represented by `q`. -/
theorem pascalCenteredXiSquaredOrbitRepresentative_sq
    {R : ℝ} (q : ↥(pascalCenteredXiSquaredOrbitFinset R)) :
    pascalCenteredXiSquaredOrbitRepresentative R q ^ 2 = q.1 := by
  exact (Classical.choose_spec
    (mem_pascalCenteredXiSquaredOrbitFinset_iff.mp q.property)).2

private noncomputable def pascalCenteredXiSquaredOrbitRepresentativeAt
    (R : ℝ) (q : ℂ) : ℂ :=
  if hq : q ∈ pascalCenteredXiSquaredOrbitFinset R then
    pascalCenteredXiSquaredOrbitRepresentative R ⟨q, hq⟩
  else 0

private theorem pascalCenteredXiSquaredOrbitRepresentativeAt_eq
    {R : ℝ} {q : ℂ} (hq : q ∈ pascalCenteredXiSquaredOrbitFinset R) :
    pascalCenteredXiSquaredOrbitRepresentativeAt R q =
      pascalCenteredXiSquaredOrbitRepresentative R ⟨q, hq⟩ := by
  simp [pascalCenteredXiSquaredOrbitRepresentativeAt, hq]

/-- The finite index cardinality of the actual squared-orbit carrier. -/
noncomputable def pascalCenteredXiSquaredOrbitIndexCard (R : ℝ) : ℕ :=
  Fintype.card (↥(pascalCenteredXiSquaredOrbitFinset R))

private noncomputable def pascalCenteredXiSquaredOrbitIndexEquiv (R : ℝ) :
    (↥(pascalCenteredXiSquaredOrbitFinset R)) ≃
      Fin (pascalCenteredXiSquaredOrbitIndexCard R) :=
  Fintype.equivFin _

/-- The `Fin`-indexed squared-orbit coordinates. -/
noncomputable def pascalCenteredXiSquaredOrbitCoordinate
    (R : ℝ) (j : Fin (pascalCenteredXiSquaredOrbitIndexCard R)) : ℂ :=
  (pascalCenteredXiSquaredOrbitIndexEquiv R).symm j

/-- The `Fin`-indexed actual representative attached to each squared orbit. -/
noncomputable def pascalCenteredXiSquaredOrbitRepresentativeFin
    (R : ℝ) (j : Fin (pascalCenteredXiSquaredOrbitIndexCard R)) : ℂ :=
  pascalCenteredXiSquaredOrbitRepresentative R
    ((pascalCenteredXiSquaredOrbitIndexEquiv R).symm j)

theorem pascalCenteredXiSquaredOrbitRepresentativeFin_mem
    (R : ℝ) (j : Fin (pascalCenteredXiSquaredOrbitIndexCard R)) :
    pascalCenteredXiSquaredOrbitRepresentativeFin R j ∈
      pascalCenteredXiZeroDiskFinset R := by
  exact pascalCenteredXiSquaredOrbitRepresentative_mem
    ((pascalCenteredXiSquaredOrbitIndexEquiv R).symm j)

theorem pascalCenteredXiSquaredOrbitRepresentativeFin_sq
    (R : ℝ) (j : Fin (pascalCenteredXiSquaredOrbitIndexCard R)) :
    pascalCenteredXiSquaredOrbitRepresentativeFin R j ^ 2 =
      pascalCenteredXiSquaredOrbitCoordinate R j := by
  exact pascalCenteredXiSquaredOrbitRepresentative_sq
    ((pascalCenteredXiSquaredOrbitIndexEquiv R).symm j)

private theorem pascalCenteredXiSquaredOrbitRepresentativeFin_sq_ne_zero
    (R : ℝ) (j : Fin (pascalCenteredXiSquaredOrbitIndexCard R)) :
    pascalCenteredXiSquaredOrbitRepresentativeFin R j ^ 2 ≠ 0 := by
  rw [pascalCenteredXiSquaredOrbitRepresentativeFin_sq]
  exact pascalCenteredXiSquaredOrbitFinset_sq_ne_zero
    ((pascalCenteredXiSquaredOrbitIndexEquiv R).symm j).property

private theorem pascalCenteredXiSquaredOrbitRepresentativeFin_pairwise_sq_ne
    (R : ℝ) :
    Pairwise (fun i j =>
      pascalCenteredXiSquaredOrbitRepresentativeFin R i ^ 2 ≠
        pascalCenteredXiSquaredOrbitRepresentativeFin R j ^ 2) := by
  intro i j hij heq
  apply hij
  apply (pascalCenteredXiSquaredOrbitIndexEquiv R).symm.injective
  apply Subtype.ext
  rw [pascalCenteredXiSquaredOrbitRepresentativeFin_sq,
    pascalCenteredXiSquaredOrbitRepresentativeFin_sq] at heq
  exact heq

/-! ## C2-B/C: bare-kernel rank and canonical Mellin column scaling -/

/-- The actual squared-orbit representatives admit a nonzero, injective set
of real dilation parameters whose bare Mellin evaluation matrix is invertible.
This is a direct application of the C1E theorem after finite-carrier
enumeration. -/
theorem exists_pascalCenteredXiActualWindow_bareKernel_evaluation_rank
    (R : ℝ) :
    ∃ τ : Fin (pascalCenteredXiSquaredOrbitIndexCard R) → ℝ,
      (∀ i, τ i ≠ 0) ∧
      Function.Injective τ ∧
      Matrix.det
        ((fun i j => complexExpSecondDifferenceKernel (τ i)
          (pascalCenteredXiSquaredOrbitRepresentativeFin R j)) :
          Matrix (Fin (pascalCenteredXiSquaredOrbitIndexCard R))
            (Fin (pascalCenteredXiSquaredOrbitIndexCard R)) ℂ) ≠ 0 := by
  let z : Fin (pascalCenteredXiSquaredOrbitIndexCard R) → ℂ :=
    pascalCenteredXiSquaredOrbitRepresentativeFin R
  have hq : ∀ j, z j ^ 2 ≠ 0 := by
    intro j
    exact pascalCenteredXiSquaredOrbitRepresentativeFin_sq_ne_zero R j
  have hpair : Pairwise (fun i j => z i ^ 2 ≠ z j ^ 2) := by
    exact pascalCenteredXiSquaredOrbitRepresentativeFin_pairwise_sq_ne R
  obtain ⟨τ, hτ, hinj, hdet⟩ :=
    exists_complexExpSecondDifferenceKernel_evaluation_det_ne_zero hq hpair
  exact ⟨τ, hτ, hinj, by simpa [z] using hdet⟩

/-- The canonical Mellin evaluation matrix is eventually full rank on the
actual squared-orbit representatives as the positive box width tends to
zero.  The only new factors are the already-proved spectral factors. -/
theorem eventually_pascalCenteredXiActualWindow_mellin_evaluation_det_ne_zero
    (R : ℝ) :
    ∃ τ : Fin (pascalCenteredXiSquaredOrbitIndexCard R) → ℝ,
      (∀ i, τ i ≠ 0) ∧
      Function.Injective τ ∧
      ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
        Matrix.det
          ((fun i j => pascalCenteredXiMellinSecondDifferenceWeight ε
            (τ i) (pascalCenteredXiSquaredOrbitRepresentativeFin R j)) :
            Matrix (Fin (pascalCenteredXiSquaredOrbitIndexCard R))
              (Fin (pascalCenteredXiSquaredOrbitIndexCard R)) ℂ) ≠ 0 := by
  obtain ⟨τ, hτ, hinj, hK⟩ :=
    exists_pascalCenteredXiActualWindow_bareKernel_evaluation_rank R
  let z : Fin (pascalCenteredXiSquaredOrbitIndexCard R) → ℂ :=
    pascalCenteredXiSquaredOrbitRepresentativeFin R
  let K : Matrix (Fin (pascalCenteredXiSquaredOrbitIndexCard R))
      (Fin (pascalCenteredXiSquaredOrbitIndexCard R)) ℂ :=
    fun i j => complexExpSecondDifferenceKernel (τ i) (z j)
  have hspec :
      ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
        ∀ j, centeredMellinSpectralWeight
          (centeredMellinBoxApprox ε) (z j) ≠ 0 := by
    filter_upwards [
      eventually_pascalCenteredXiMellinSpectralWeight_ne_zero_on_actual_window R]
      with ε hε j
    exact hε (z j) (pascalCenteredXiSquaredOrbitRepresentativeFin_mem R j)
  have hdet_event :
      ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
        Matrix.det
          ((fun i j => pascalCenteredXiMellinSecondDifferenceWeight ε
            (τ i) (z j)) :
            Matrix (Fin (pascalCenteredXiSquaredOrbitIndexCard R))
              (Fin (pascalCenteredXiSquaredOrbitIndexCard R)) ℂ) ≠ 0 := by
    filter_upwards [hspec] with ε hε
    let H : Matrix (Fin (pascalCenteredXiSquaredOrbitIndexCard R))
        (Fin (pascalCenteredXiSquaredOrbitIndexCard R)) ℂ :=
      fun i j => pascalCenteredXiMellinSecondDifferenceWeight ε (τ i) (z j)
    let S : Fin (pascalCenteredXiSquaredOrbitIndexCard R) → ℂ :=
      fun j => centeredMellinSpectralWeight
        (centeredMellinBoxApprox ε) (z j)
    have hmatrix : H = K * Matrix.diagonal S := by
      ext i j
      simp only [H, Matrix.mul_diagonal, K, S]
      rw [pascalCenteredXiMellinSecondDifferenceWeight_eq_kernel_mul
        (hτ i)]
      simp [complexExpSecondDifferenceKernel, hτ i]
    have hscale : ∏ j, S j ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr
      intro j hj
      exact hε j
    have hfactor : H.det = K.det * ∏ j, S j := by
      rw [hmatrix, Matrix.det_mul, Matrix.det_diagonal]
    have hH : H.det ≠ 0 := by
      rw [hfactor]
      exact mul_ne_zero hK hscale
    simpa [H, z] using hH
  exact ⟨τ, hτ, hinj, hdet_event⟩

/-! ## C2-D: squared-orbit masses and moment aggregation -/

/-- The multiplicity-weighted mass of one squared orbit in the actual finite
Xi window.  The filtered sum is the canonical definition and does not assume
that an orbit has exactly two representatives. -/
noncomputable def pascalCenteredXiSquaredOrbitMass
    (R : ℝ) (q : ℂ) : ℂ :=
  ∑ z ∈ (pascalCenteredXiZeroDiskFinset R).filter (fun z => z ^ 2 = q),
    (pascalCenteredXiZeroMultiplicity z : ℂ)

private theorem complex_sq_eq_sq_iff
    {a b : ℂ} (h : a ^ 2 = b ^ 2) : a = b ∨ a = -b := by
  have hfac : (a - b) * (a + b) = 0 := by
    calc
      (a - b) * (a + b) = a ^ 2 - b ^ 2 := by ring
      _ = 0 := by rw [h, sub_self]
  rcases mul_eq_zero.mp hfac with hab | hab
  · exact Or.inl (sub_eq_zero.mp hab)
  · exact Or.inr (eq_neg_of_add_eq_zero_left hab)

private theorem pascalCenteredXiMellinSecondDifferenceWeight_eq_of_sq_eq
    {ε τ : ℝ} (hε : 0 < ε) {a b : ℂ}
    (hsq : a ^ 2 = b ^ 2) :
    pascalCenteredXiMellinSecondDifferenceWeight ε τ a =
      pascalCenteredXiMellinSecondDifferenceWeight ε τ b := by
  rcases complex_sq_eq_sq_iff hsq with rfl | rfl
  · rfl
  · exact pascalCenteredXiMellinSecondDifferenceWeight_even hε b

/-- The actual canonical Mellin moment is the squared-orbit mass sum of the
even Mellin weight.  This is the finite fiberwise regrouping used by C2-D. -/
theorem pascalCenteredXiZeroDiskMellinSecondDifferenceZeroMoment_eq_squaredOrbitMass_sum
    {R ε τ : ℝ} (hε : 0 < ε) :
    pascalCenteredXiZeroDiskWeightedMoment
        (pascalCenteredXiMellinSecondDifferenceWeight ε τ) R =
      ∑ q : ↥(pascalCenteredXiSquaredOrbitFinset R),
        pascalCenteredXiSquaredOrbitMass R q.1 *
          pascalCenteredXiMellinSecondDifferenceWeight ε τ
            (pascalCenteredXiSquaredOrbitRepresentative R q) := by
  let S := pascalCenteredXiZeroDiskFinset R
  let Q := pascalCenteredXiSquaredOrbitFinset R
  let w : ℂ → ℂ := pascalCenteredXiMellinSecondDifferenceWeight ε τ
  have hmap : ∀ a ∈ S, a ^ 2 ∈ Q := by
    intro a ha
    exact Finset.mem_image.mpr ⟨a, ha, rfl⟩
  have hfiber :
      (∑ q ∈ Q,
        ∑ a ∈ S.filter (fun a => a ^ 2 = q),
          (pascalCenteredXiZeroMultiplicity a : ℂ) * w a) =
        ∑ a ∈ S,
          (pascalCenteredXiZeroMultiplicity a : ℂ) * w a := by
    exact Finset.sum_fiberwise_of_maps_to hmap
      (fun a => (pascalCenteredXiZeroMultiplicity a : ℂ) * w a)
  have hgroup :
      (∑ q ∈ Q,
        ∑ a ∈ S.filter (fun a => a ^ 2 = q),
          (pascalCenteredXiZeroMultiplicity a : ℂ) * w a) =
        ∑ q ∈ Q,
          pascalCenteredXiSquaredOrbitMass R q *
            w (pascalCenteredXiSquaredOrbitRepresentativeAt R q) := by
    apply Finset.sum_congr rfl
    intro q hq
    let qr : ↥Q := ⟨q, hq⟩
    rw [pascalCenteredXiSquaredOrbitRepresentativeAt_eq hq]
    have hrep := pascalCenteredXiSquaredOrbitRepresentative_sq qr
    have hconst : ∀ a ∈ S.filter (fun a => a ^ 2 = q), w a = w (pascalCenteredXiSquaredOrbitRepresentative R qr) := by
      intro a ha
      apply pascalCenteredXiMellinSecondDifferenceWeight_eq_of_sq_eq hε
      exact (Finset.mem_filter.mp ha).2.trans hrep.symm
    calc
      ∑ a ∈ S.filter (fun a => a ^ 2 = q),
          (pascalCenteredXiZeroMultiplicity a : ℂ) * w a =
          ∑ a ∈ S.filter (fun a => a ^ 2 = q),
            (pascalCenteredXiZeroMultiplicity a : ℂ) *
              w (pascalCenteredXiSquaredOrbitRepresentative R qr) := by
                apply Finset.sum_congr rfl
                intro a ha
                rw [hconst a ha]
      _ = pascalCenteredXiSquaredOrbitMass R q *
          w (pascalCenteredXiSquaredOrbitRepresentative R qr) := by
            simp only [pascalCenteredXiSquaredOrbitMass, S]
            rw [Finset.sum_mul]
  unfold pascalCenteredXiZeroDiskWeightedMoment
  change (∑ a ∈ S, (pascalCenteredXiZeroMultiplicity a : ℂ) * w a) = _
  rw [← hfiber, hgroup]
  rw [← Finset.sum_coe_sort]
  apply Fintype.sum_congr
  intro q
  simp [w, pascalCenteredXiSquaredOrbitRepresentativeAt_eq]

/-- The squared-orbit mass vector in the `Fin` presentation of the actual
window carrier. -/
noncomputable def pascalCenteredXiSquaredOrbitMassVec
    (R : ℝ) : Fin (pascalCenteredXiSquaredOrbitIndexCard R) → ℂ :=
  fun j => pascalCenteredXiSquaredOrbitMass
    R (pascalCenteredXiSquaredOrbitCoordinate R j)

/-- The vector of actual finite canonical Mellin moments at a finite family of
dilation parameters. -/
noncomputable def pascalCenteredXiMellinMomentVec
    (R ε : ℝ) (τ : Fin (pascalCenteredXiSquaredOrbitIndexCard R) → ℝ) :
    Fin (pascalCenteredXiSquaredOrbitIndexCard R) → ℂ :=
  fun i => pascalCenteredXiZeroDiskWeightedMoment
    (pascalCenteredXiMellinSecondDifferenceWeight ε (τ i)) R

/-- The canonical Mellin evaluation matrix on the finite actual squared-orbit
carrier. -/
noncomputable def pascalCenteredXiMellinEvaluationMatrix
    (R ε : ℝ) (τ : Fin (pascalCenteredXiSquaredOrbitIndexCard R) → ℝ) :
    Matrix (Fin (pascalCenteredXiSquaredOrbitIndexCard R))
      (Fin (pascalCenteredXiSquaredOrbitIndexCard R)) ℂ :=
  fun i j => pascalCenteredXiMellinSecondDifferenceWeight ε (τ i)
    (pascalCenteredXiSquaredOrbitRepresentativeFin R j)

/-! The finite source equation is written with the same row/column convention
as the canonical Mellin evaluation matrix. -/

/-- The actual canonical Mellin moment vector is the Mellin evaluation matrix
applied to the squared-orbit mass vector.  Equal-square fibers are grouped
before the finite `Fin` reindexing, so the equation is valid for the actual
window rather than for a selected list of individual zeros. -/
theorem pascalCenteredXiMellinMomentVec_eq_mellinEvaluation_mulVec_massVec
    {R ε : ℝ} (hε : 0 < ε)
    (τ : Fin (pascalCenteredXiSquaredOrbitIndexCard R) → ℝ) :
    pascalCenteredXiMellinMomentVec R ε τ =
      ((fun i j => pascalCenteredXiMellinSecondDifferenceWeight ε
          (τ i) (pascalCenteredXiSquaredOrbitRepresentativeFin R j)) :
        Matrix (Fin (pascalCenteredXiSquaredOrbitIndexCard R))
          (Fin (pascalCenteredXiSquaredOrbitIndexCard R)) ℂ) *ᵥ
        pascalCenteredXiSquaredOrbitMassVec R := by
  funext i
  change pascalCenteredXiZeroDiskWeightedMoment
      (pascalCenteredXiMellinSecondDifferenceWeight ε (τ i)) R =
    ∑ j, pascalCenteredXiMellinSecondDifferenceWeight ε (τ i)
        (pascalCenteredXiSquaredOrbitRepresentativeFin R j) *
      pascalCenteredXiSquaredOrbitMassVec R j
  have hagg :=
    pascalCenteredXiZeroDiskMellinSecondDifferenceZeroMoment_eq_squaredOrbitMass_sum
      (R := R) (ε := ε) (τ := τ i) hε
  let e := pascalCenteredXiSquaredOrbitIndexEquiv R
  have hsum :
      (∑ j : Fin (pascalCenteredXiSquaredOrbitIndexCard R),
        pascalCenteredXiSquaredOrbitMass R ((e.symm j).1) *
          pascalCenteredXiMellinSecondDifferenceWeight ε (τ i)
            (pascalCenteredXiSquaredOrbitRepresentative R (e.symm j))) =
        ∑ q : ↥(pascalCenteredXiSquaredOrbitFinset R),
          pascalCenteredXiSquaredOrbitMass R q.1 *
            pascalCenteredXiMellinSecondDifferenceWeight ε (τ i)
              (pascalCenteredXiSquaredOrbitRepresentative R q) := by
    apply Fintype.sum_equiv e.symm
    intro j
    rfl
  rw [hagg, ← hsum]
  apply Fintype.sum_congr
  intro j
  simp [pascalCenteredXiSquaredOrbitMassVec,
    pascalCenteredXiSquaredOrbitRepresentativeFin,
    pascalCenteredXiSquaredOrbitCoordinate, e]
  ring

/-- For every positive box width and the C2 dilation parameters, equality of
two Mellin moment vectors implies equality of their squared-orbit mass
vectors whenever the canonical Mellin evaluation determinant is nonzero. -/
theorem pascalCenteredXiMellinEvaluation_mulVec_injective_of_det_ne_zero
    {R ε : ℝ} {τ : Fin (pascalCenteredXiSquaredOrbitIndexCard R) → ℝ}
    (hdet : (pascalCenteredXiMellinEvaluationMatrix R ε τ).det ≠ 0) :
    Function.Injective (pascalCenteredXiMellinEvaluationMatrix R ε τ).mulVec := by
  intro m₁ m₂ h12
  have hzero :
      pascalCenteredXiMellinEvaluationMatrix R ε τ *ᵥ (m₁ - m₂) = 0 := by
    rw [Matrix.mulVec_sub]
    rw [h12, sub_self]
  have hz := Matrix.eq_zero_of_mulVec_eq_zero hdet hzero
  exact sub_eq_zero.mp hz

end DkMath.RH.CFBRCProjection
