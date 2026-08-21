/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.PascalCenteredXiMellinActualWindowFullRankAudit
import Mathlib.Tactic

/-!
# Off-critical finite Mellin witnesses

This module closes the GWSS-002 zero-side construction.  An actual centered-Xi
zero with nonzero real part gives a squared orbit with nonzero imaginary part;
the existing multiplicity API makes every occupied orbit mass nonzero.  The
full-rank C2 Mellin matrix is then inverted only as a finite matrix: one row of
its inverse extracts a chosen orbit mass.  The row is scaled by the imaginary
part of the target squared coordinate, so the resulting finite linear
combination has the exact off-critical detector value
`q.im * orbitMass q`.

The result is a target-dependent finite witness on a fixed actual window.  It
does not remove the top-horizontal term, pass to infinite height, assert Weil
positivity, or provide arithmetic control of the witness.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open DkMath.Analysis
open Filter
open scoped BigOperators Matrix

/-! ## GWSS-002-A: off-critical squared-orbit geometry -/

/-- The imaginary part of a complex square is twice the product of the real
and imaginary parts. -/
theorem complex_sq_im_eq_two_mul_re_mul_im (z : ℂ) :
    (z ^ 2).im = 2 * z.re * z.im := by
  simp [pow_two, Complex.mul_im]
  ring

/-- Every actual centered Xi zero has nonzero centered imaginary coordinate.
This uses the unconditional nonrealness theorem for nontrivial zeta zeros. -/
theorem pascalCenteredXiZeroDiskFinset_im_ne_zero
    {R : ℝ} {z : ℂ}
    (hz : z ∈ pascalCenteredXiZeroDiskFinset R) :
    z.im ≠ 0 := by
  have hzero : z ∈ pascalCenteredXiZeros :=
    (mem_pascalCenteredXiZeroDiskFinset_iff.mp hz).2
  have hnontriv : NontrivialRiemannZetaZero (criticalLineCenter + z) :=
    (mem_pascalCenteredXiZeros_iff_nontrivial_shift z).mp hzero
  have him : (criticalLineCenter + z).im ≠ 0 :=
    nontrivialRiemannZetaZero_im_ne_zero hnontriv
  simpa [criticalLineCenter] using him

/-- For an actual centered zero, vanishing imaginary part of its square is
equivalent to lying on the centered critical line. -/
theorem pascalCenteredXiZeroDiskFinset_re_eq_zero_iff_sq_im_eq_zero
    {R : ℝ} {z : ℂ}
    (hz : z ∈ pascalCenteredXiZeroDiskFinset R) :
    z.re = 0 ↔ (z ^ 2).im = 0 := by
  have him : z.im ≠ 0 := pascalCenteredXiZeroDiskFinset_im_ne_zero hz
  constructor
  · intro hre
    simp [complex_sq_im_eq_two_mul_re_mul_im, hre]
  · intro hsq
    have hprod : 2 * z.re * z.im = 0 := by
      rw [← complex_sq_im_eq_two_mul_re_mul_im]
      exact hsq
    rcases mul_eq_zero.mp hprod with htwo | himul
    · norm_num at htwo
      exact htwo
    · exact (him himul).elim

/-- An off-critical actual centered zero has a genuinely off-axis squared
coordinate. -/
theorem pascalCenteredXiZeroDiskFinset_sq_im_ne_zero
    {R : ℝ} {z : ℂ}
    (hz : z ∈ pascalCenteredXiZeroDiskFinset R)
    (hre : z.re ≠ 0) :
    (z ^ 2).im ≠ 0 := by
  intro hsq
  apply hre
  exact (pascalCenteredXiZeroDiskFinset_re_eq_zero_iff_sq_im_eq_zero hz).mpr hsq

/-! ## GWSS-002-B: positive occupied-orbit mass -/

/-- The multiplicity-weighted mass of an occupied squared orbit is nonzero.
The proof is a finite natural-number positivity argument before casting to
`ℂ`; no sign assertion about a global explicit-formula sum is involved. -/
theorem pascalCenteredXiSquaredOrbitMass_ne_zero
    {R : ℝ} {q : ℂ}
    (hq : q ∈ pascalCenteredXiSquaredOrbitFinset R) :
    pascalCenteredXiSquaredOrbitMass R q ≠ 0 := by
  rcases mem_pascalCenteredXiSquaredOrbitFinset_iff.mp hq with ⟨z, hz, hsq⟩
  have hmem : z ∈ (pascalCenteredXiZeroDiskFinset R).filter (fun z => z ^ 2 = q) :=
    Finset.mem_filter.mpr ⟨hz, hsq⟩
  let S := (pascalCenteredXiZeroDiskFinset R).filter (fun a => a ^ 2 = q)
  have hsum_pos :
      0 < ∑ a ∈ S, pascalCenteredXiZeroMultiplicity a := by
    apply Finset.sum_pos'
    · intro a ha
      exact Nat.zero_le _
    · exact ⟨z, hmem, pascalCenteredXiZeroMultiplicity_pos
        (mem_pascalCenteredXiZeroDiskFinset_iff.mp hz).2⟩
  have hsum_ne :
      (∑ a ∈ S, pascalCenteredXiZeroMultiplicity a) ≠ 0 :=
    Nat.ne_of_gt hsum_pos
  have hcast :
      ((∑ a ∈ S, pascalCenteredXiZeroMultiplicity a : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast hsum_ne
  simpa [pascalCenteredXiSquaredOrbitMass, S] using hcast

/-! ## GWSS-002-C: finite dual coordinate extraction -/

/-- A row of the nonsingular inverse extracts one coordinate after applying a
finite square matrix. -/
theorem exists_matrix_coordinate_extractor
    {n : Type*} [Fintype n] [DecidableEq n]
    (H : Matrix n n ℂ) (hdet : H.det ≠ 0) (j0 : n) :
    ∃ c : n → ℂ, ∀ m : n → ℂ,
      ∑ i, c i * (H *ᵥ m) i = m j0 := by
  let c : n → ℂ := fun i => H⁻¹ j0 i
  have hunit : IsUnit H.det := isUnit_iff_ne_zero.mpr hdet
  have hrow : c ᵥ* H = fun j => if j0 = j then (1 : ℂ) else 0 := by
    ext j
    calc
      (c ᵥ* H) j = (H⁻¹ * H) j0 j := rfl
      _ = (1 : Matrix n n ℂ) j0 j := by
        rw [Matrix.nonsing_inv_mul H hunit]
      _ = if j0 = j then (1 : ℂ) else 0 := by
        simp [Matrix.one_apply]
  refine ⟨c, ?_⟩
  intro m
  change c ⬝ᵥ (H *ᵥ m) = m j0
  rw [Matrix.dotProduct_mulVec, hrow]
  simp [dotProduct]

/-- The C2 Mellin moment vector admits a target-coordinate extractor whenever
the canonical evaluation matrix has nonzero determinant. -/
theorem exists_pascalCenteredXiMellinMoment_coordinate_extractor
    {R ε : ℝ}
    {τ : Fin (pascalCenteredXiSquaredOrbitIndexCard R) → ℝ}
    (hε : 0 < ε)
    (hdet : (pascalCenteredXiMellinEvaluationMatrix R ε τ).det ≠ 0)
    (j0 : Fin (pascalCenteredXiSquaredOrbitIndexCard R)) :
    ∃ c : Fin (pascalCenteredXiSquaredOrbitIndexCard R) → ℂ,
      ∑ i, c i * pascalCenteredXiMellinMomentVec R ε τ i =
        pascalCenteredXiSquaredOrbitMassVec R j0 := by
  let H := pascalCenteredXiMellinEvaluationMatrix R ε τ
  obtain ⟨c, hc⟩ := exists_matrix_coordinate_extractor H hdet j0
  refine ⟨c, ?_⟩
  have hmoment := pascalCenteredXiMellinMomentVec_eq_mellinEvaluation_mulVec_massVec
    hε τ
  calc
    ∑ i, c i * pascalCenteredXiMellinMomentVec R ε τ i =
        ∑ i, c i * (H *ᵥ pascalCenteredXiSquaredOrbitMassVec R) i := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [congrFun hmoment i]
      rfl
    _ = pascalCenteredXiSquaredOrbitMassVec R j0 := hc _

/-! ## GWSS-002-D: off-critical scalar detector -/

/-- The off-critical squared-orbit scalar detector is nonzero.  Both its
imaginary-coordinate factor and its occupied-orbit mass are load-bearing. -/
theorem pascalCenteredXiOffCriticalOrbitScalarDetector_ne_zero
    {R : ℝ}
    (j0 : Fin (pascalCenteredXiSquaredOrbitIndexCard R))
    (hoff : (pascalCenteredXiSquaredOrbitCoordinate R j0).im ≠ 0)
    (hmass : pascalCenteredXiSquaredOrbitMassVec R j0 ≠ 0) :
    ((pascalCenteredXiSquaredOrbitCoordinate R j0).im : ℂ) *
        pascalCenteredXiSquaredOrbitMassVec R j0 ≠ 0 := by
  exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hoff) hmass

/-- Scaling a finite Mellin coordinate extractor by the target squared
coordinate's imaginary part produces the exact off-critical detector scalar. -/
theorem exists_pascalCenteredXiMellin_offCritical_detector_coefficients
    {R ε : ℝ}
    (hε : 0 < ε)
    {τ : Fin (pascalCenteredXiSquaredOrbitIndexCard R) → ℝ}
    (hdet : (pascalCenteredXiMellinEvaluationMatrix R ε τ).det ≠ 0)
    (j0 : Fin (pascalCenteredXiSquaredOrbitIndexCard R)) :
    ∃ c : Fin (pascalCenteredXiSquaredOrbitIndexCard R) → ℂ,
      (∑ i, c i * pascalCenteredXiMellinMomentVec R ε τ i) =
        ((pascalCenteredXiSquaredOrbitCoordinate R j0).im : ℂ) *
          pascalCenteredXiSquaredOrbitMassVec R j0 := by
  obtain ⟨c₀, hc₀⟩ :=
    exists_pascalCenteredXiMellinMoment_coordinate_extractor hε hdet j0
  let qIm : ℂ := (pascalCenteredXiSquaredOrbitCoordinate R j0).im
  refine ⟨fun i => qIm * c₀ i, ?_⟩
  have hmul (a : ℂ) (f : Fin (pascalCenteredXiSquaredOrbitIndexCard R) → ℂ) :
      a * (∑ i, f i) = ∑ i, a * f i := by
    simpa using (Finset.mul_sum
      (Finset.univ : Finset (Fin (pascalCenteredXiSquaredOrbitIndexCard R))) f a)
  calc
    ∑ i, (qIm * c₀ i) * pascalCenteredXiMellinMomentVec R ε τ i =
        ∑ i, qIm * (c₀ i * pascalCenteredXiMellinMomentVec R ε τ i) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = qIm * (∑ i, c₀ i * pascalCenteredXiMellinMomentVec R ε τ i) := by
      rw [hmul]
    _ = qIm * pascalCenteredXiSquaredOrbitMassVec R j0 := by
      rw [hc₀]
    _ = ((pascalCenteredXiSquaredOrbitCoordinate R j0).im : ℂ) *
        pascalCenteredXiSquaredOrbitMassVec R j0 := by
      rfl

/-- On the centered critical line, the squared-orbit scalar detector vanishes.
This is a semantic sanity check, not an equivalence theorem. -/
theorem pascalCenteredXiCriticalOrbitScalarDetector_eq_zero
    {R : ℝ} {z : ℂ}
    (hz : z ∈ pascalCenteredXiZeroDiskFinset R)
    (hre : z.re = 0) :
    ((z ^ 2).im : ℂ) * pascalCenteredXiSquaredOrbitMass R (z ^ 2) = 0 := by
  have hqim : (z ^ 2).im = 0 :=
    (pascalCenteredXiZeroDiskFinset_re_eq_zero_iff_sq_im_eq_zero hz).mp hre
  rw [hqim]
  simp

/-! ## GWSS-002-D/E: finite admissible witness synthesis -/

/-- A finite target-dependent linear combination of the canonical Mellin
second-difference family. -/
noncomputable def pascalCenteredXiMellinWitnessWeight
    (ε : ℝ) (τ : Fin n → ℝ) (c : Fin n → ℂ) : ℂ → ℂ :=
  fun z => ∑ i, c i * pascalCenteredXiMellinSecondDifferenceWeight ε (τ i) z

/-- Positive box width makes a synthesized witness holomorphic. -/
theorem pascalCenteredXiMellinWitnessWeight_differentiable
    {ε : ℝ} (hε : 0 < ε) (τ : Fin n → ℝ) (c : Fin n → ℂ) :
    Differentiable ℂ (pascalCenteredXiMellinWitnessWeight ε τ c) := by
  unfold pascalCenteredXiMellinWitnessWeight
  apply Differentiable.fun_sum (u := (Finset.univ : Finset (Fin n)))
  intro i hi
  exact (differentiable_const (c := c i)).mul
    (pascalCenteredXiMellinSecondDifferenceWeight_differentiable hε)

/-- A synthesized witness remains even, so it is admissible for the centered
finite explicit-formula surface. -/
theorem pascalCenteredXiMellinWitnessWeight_even
    {ε : ℝ} (hε : 0 < ε) (τ : Fin n → ℝ) (c : Fin n → ℂ) :
    PascalCenteredEvenWeight (pascalCenteredXiMellinWitnessWeight ε τ c) := by
  intro z
  unfold pascalCenteredXiMellinWitnessWeight
  apply Finset.sum_congr rfl
  intro i hi
  exact congrArg (fun x => c i * x)
    (pascalCenteredXiMellinSecondDifferenceWeight_even hε (τ := τ i) z)

/-- The zero-side moment of a synthesized witness is the same finite linear
combination of the canonical Mellin moments. -/
theorem pascalCenteredXiMellinWitnessWeight_moment_eq
    {R ε : ℝ} (τ : Fin n → ℝ) (c : Fin n → ℂ) :
    pascalCenteredXiZeroDiskWeightedMoment
        (pascalCenteredXiMellinWitnessWeight ε τ c) R =
      ∑ i, c i * pascalCenteredXiZeroDiskWeightedMoment
        (pascalCenteredXiMellinSecondDifferenceWeight ε (τ i)) R := by
  unfold pascalCenteredXiMellinWitnessWeight pascalCenteredXiZeroDiskWeightedMoment
  change
    (∑ a ∈ pascalCenteredXiZeroDiskFinset R,
      (pascalCenteredXiZeroMultiplicity a : ℂ) *
        (∑ i ∈ (Finset.univ : Finset (Fin n)),
          c i * pascalCenteredXiMellinSecondDifferenceWeight ε (τ i) a)) =
      ∑ i ∈ (Finset.univ : Finset (Fin n)), c i *
        (∑ a ∈ pascalCenteredXiZeroDiskFinset R,
          (pascalCenteredXiZeroMultiplicity a : ℂ) *
            pascalCenteredXiMellinSecondDifferenceWeight ε (τ i) a)
  have hmul (a : ℂ) (f : Fin n → ℂ) :
      a * (∑ i, f i) = ∑ i, a * f i := by
    simpa using (Finset.mul_sum (Finset.univ : Finset (Fin n)) f a)
  calc
    (∑ a ∈ pascalCenteredXiZeroDiskFinset R,
        (pascalCenteredXiZeroMultiplicity a : ℂ) *
          (∑ i, c i * pascalCenteredXiMellinSecondDifferenceWeight ε (τ i) a)) =
      ∑ a ∈ pascalCenteredXiZeroDiskFinset R, ∑ i,
        (pascalCenteredXiZeroMultiplicity a : ℂ) *
          (c i * pascalCenteredXiMellinSecondDifferenceWeight ε (τ i) a) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [hmul]
    _ = ∑ i, ∑ a ∈ pascalCenteredXiZeroDiskFinset R,
        (pascalCenteredXiZeroMultiplicity a : ℂ) *
          (c i * pascalCenteredXiMellinSecondDifferenceWeight ε (τ i) a) := by
      rw [Finset.sum_comm]
    _ = ∑ i, c i *
        (∑ a ∈ pascalCenteredXiZeroDiskFinset R,
          (pascalCenteredXiZeroMultiplicity a : ℂ) *
            pascalCenteredXiMellinSecondDifferenceWeight ε (τ i) a) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      ring

/-- A nonzero occupied target mass yields an admissible finite Mellin witness
whose actual zero-side moment is nonzero. -/
theorem exists_pascalCenteredXiMellinWitness_of_full_rank_target
    {R ε : ℝ}
    (hε : 0 < ε)
    {τ : Fin (pascalCenteredXiSquaredOrbitIndexCard R) → ℝ}
    (hdet : (pascalCenteredXiMellinEvaluationMatrix R ε τ).det ≠ 0)
    (j0 : Fin (pascalCenteredXiSquaredOrbitIndexCard R))
    (hmass : pascalCenteredXiSquaredOrbitMassVec R j0 ≠ 0) :
    ∃ c : Fin (pascalCenteredXiSquaredOrbitIndexCard R) → ℂ,
      Differentiable ℂ (pascalCenteredXiMellinWitnessWeight ε τ c) ∧
      PascalCenteredEvenWeight (pascalCenteredXiMellinWitnessWeight ε τ c) ∧
      pascalCenteredXiZeroDiskWeightedMoment
          (pascalCenteredXiMellinWitnessWeight ε τ c) R ≠ 0 := by
  obtain ⟨c, hc⟩ := exists_pascalCenteredXiMellinMoment_coordinate_extractor
    hε hdet j0
  refine ⟨c, pascalCenteredXiMellinWitnessWeight_differentiable hε τ c,
    pascalCenteredXiMellinWitnessWeight_even hε τ c, ?_⟩
  rw [pascalCenteredXiMellinWitnessWeight_moment_eq]
  have hlinear :
      (∑ i, c i * pascalCenteredXiZeroDiskWeightedMoment
        (pascalCenteredXiMellinSecondDifferenceWeight ε (τ i)) R) =
        pascalCenteredXiSquaredOrbitMassVec R j0 := by
    simpa [pascalCenteredXiMellinMomentVec] using hc
  rw [hlinear]
  exact hmass

/-- A full-rank target with nonzero squared-coordinate imaginary part admits
an admissible Mellin witness whose moment is exactly the off-critical scalar
detector, and hence is nonzero. -/
theorem exists_pascalCenteredXiMellinOffCriticalWitness_of_full_rank_target
    {R ε : ℝ}
    (hε : 0 < ε)
    {τ : Fin (pascalCenteredXiSquaredOrbitIndexCard R) → ℝ}
    (hdet : (pascalCenteredXiMellinEvaluationMatrix R ε τ).det ≠ 0)
    (j0 : Fin (pascalCenteredXiSquaredOrbitIndexCard R))
    (hoff : (pascalCenteredXiSquaredOrbitCoordinate R j0).im ≠ 0)
    (hmass : pascalCenteredXiSquaredOrbitMassVec R j0 ≠ 0) :
    ∃ c : Fin (pascalCenteredXiSquaredOrbitIndexCard R) → ℂ,
      Differentiable ℂ (pascalCenteredXiMellinWitnessWeight ε τ c) ∧
      PascalCenteredEvenWeight (pascalCenteredXiMellinWitnessWeight ε τ c) ∧
      pascalCenteredXiZeroDiskWeightedMoment
          (pascalCenteredXiMellinWitnessWeight ε τ c) R =
        ((pascalCenteredXiSquaredOrbitCoordinate R j0).im : ℂ) *
          pascalCenteredXiSquaredOrbitMassVec R j0 ∧
      pascalCenteredXiZeroDiskWeightedMoment
          (pascalCenteredXiMellinWitnessWeight ε τ c) R ≠ 0 := by
  obtain ⟨c, hc⟩ :=
    exists_pascalCenteredXiMellin_offCritical_detector_coefficients hε hdet j0
  refine ⟨c, pascalCenteredXiMellinWitnessWeight_differentiable hε τ c,
    pascalCenteredXiMellinWitnessWeight_even hε τ c, ?_, ?_⟩
  · rw [pascalCenteredXiMellinWitnessWeight_moment_eq]
    simpa [pascalCenteredXiMellinMomentVec] using hc
  · rw [show pascalCenteredXiZeroDiskWeightedMoment
        (pascalCenteredXiMellinWitnessWeight ε τ c) R =
        ((pascalCenteredXiSquaredOrbitCoordinate R j0).im : ℂ) *
          pascalCenteredXiSquaredOrbitMassVec R j0 by
      rw [pascalCenteredXiMellinWitnessWeight_moment_eq]
      simpa [pascalCenteredXiMellinMomentVec] using hc]
    exact pascalCenteredXiOffCriticalOrbitScalarDetector_ne_zero j0 hoff hmass

/-! ## Final GWSS-002 witness theorem -/

/-- An off-critical actual centered-Xi zero admits a target-dependent finite
canonical Mellin witness on the same actual window.  The positive width is
selected from the C2 eventual full-rank theorem. -/
theorem exists_pascalCenteredXiMellinOffCriticalWitness
    {R : ℝ} {z : ℂ}
    (hz : z ∈ pascalCenteredXiZeroDiskFinset R)
    (hre : z.re ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧
      (z ^ 2).im ≠ 0 ∧
      ∃ τ : Fin (pascalCenteredXiSquaredOrbitIndexCard R) → ℝ,
        (∀ i, τ i ≠ 0) ∧ Function.Injective τ ∧
        ∃ c : Fin (pascalCenteredXiSquaredOrbitIndexCard R) → ℂ,
          Differentiable ℂ (pascalCenteredXiMellinWitnessWeight ε τ c) ∧
          PascalCenteredEvenWeight (pascalCenteredXiMellinWitnessWeight ε τ c) ∧
          pascalCenteredXiZeroDiskWeightedMoment
              (pascalCenteredXiMellinWitnessWeight ε τ c) R =
            ((z ^ 2).im : ℂ) * pascalCenteredXiSquaredOrbitMass R (z ^ 2) ∧
          pascalCenteredXiZeroDiskWeightedMoment
              (pascalCenteredXiMellinWitnessWeight ε τ c) R ≠ 0 := by
  have hq : z ^ 2 ∈ pascalCenteredXiSquaredOrbitFinset R :=
    (mem_pascalCenteredXiSquaredOrbitFinset_iff).2 ⟨z, hz, rfl⟩
  have hqim : (z ^ 2).im ≠ 0 :=
    pascalCenteredXiZeroDiskFinset_sq_im_ne_zero hz hre
  obtain ⟨τ, hτ, hinj, hdet⟩ :=
    eventually_pascalCenteredXiActualWindow_mellin_evaluation_det_ne_zero R
  letI : NeBot (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))) :=
    nhdsWithin_Ioi_neBot le_rfl
  obtain ⟨ε, hεdet, hεmem⟩ :=
    (hdet.and self_mem_nhdsWithin).exists
  have hε : 0 < ε := hεmem
  obtain ⟨j0, hjcoord⟩ :=
    exists_pascalCenteredXiSquaredOrbitCoordinate_eq R ⟨z ^ 2, hq⟩
  have hmass : pascalCenteredXiSquaredOrbitMassVec R j0 ≠ 0 := by
    rw [pascalCenteredXiSquaredOrbitMassVec, hjcoord]
    exact pascalCenteredXiSquaredOrbitMass_ne_zero hq
  have hjoff : (pascalCenteredXiSquaredOrbitCoordinate R j0).im ≠ 0 := by
    simpa [hjcoord] using hqim
  obtain ⟨c, hcdiff, hceven, hcmoment, hcmoment_ne⟩ :=
    exists_pascalCenteredXiMellinOffCriticalWitness_of_full_rank_target
      hε hεdet j0 hjoff hmass
  have hcmoment_target :
      pascalCenteredXiZeroDiskWeightedMoment
          (pascalCenteredXiMellinWitnessWeight ε τ c) R =
        ((z ^ 2).im : ℂ) * pascalCenteredXiSquaredOrbitMass R (z ^ 2) := by
    calc
      pascalCenteredXiZeroDiskWeightedMoment
          (pascalCenteredXiMellinWitnessWeight ε τ c) R =
          ((pascalCenteredXiSquaredOrbitCoordinate R j0).im : ℂ) *
            pascalCenteredXiSquaredOrbitMassVec R j0 := hcmoment
      _ = ((z ^ 2).im : ℂ) * pascalCenteredXiSquaredOrbitMass R (z ^ 2) := by
        simp [pascalCenteredXiSquaredOrbitMassVec, hjcoord]
  exact ⟨ε, hε, hqim, τ, hτ, hinj, c, hcdiff, hceven,
    hcmoment_target, hcmoment_ne⟩

end DkMath.RH.CFBRCProjection
