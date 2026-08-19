/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPrimeFactorCoercivityAudit
import DkMath.RH.CFBRC.PrimeMirrorFiniteEnergy
import Mathlib.Tactic

/-!
# ZDI-011: prime-factor coordinate certificate re-entry audit

The existing P2-F source is finite and genuinely prime-factorized, but its
zero-derived value is exactly the previously audited Eta defect partial.  This
module records the strongest source-preserving endpoint decomposition and a
small cancellation firewall.  It does not manufacture a centered-coordinate
certificate or reopen the closed positive-density/current-majorant route.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open scoped BigOperators
open DkMath.RH.Weave.Analytic

/-! ## Separate endpoint inventory -/

/--
The finite prime-factor source retains the two endpoint Eta partials as a
mirror-minus-original difference.  This is an exact finite identity, before
using any zero hypothesis; it does not assert that either endpoint partial
vanishes separately.
-/
theorem etaPrimeFactorMirrorDefectPairedPartial_eq_separate_endpoint_difference
    (K : ℕ) (s : ℂ) :
    etaPrimeFactorMirrorDefectPairedPartial K s =
      (Finset.range K).sum (etaPairTerm (criticalMirror s)) -
        (Finset.range K).sum (etaPairTerm s) := by
  rw [etaPrimeFactorMirrorDefectPairedPartial_eq_etaCriticalMirrorDefectPairedPartial]
  unfold etaCriticalMirrorDefectPairedPartial
  rw [show etaCriticalMirrorDefectPairTerm s =
      fun k : ℕ => etaPairTerm (criticalMirror s) k - etaPairTerm s k by
    funext k
    exact etaCriticalMirrorDefectPairTerm_eq_etaPairTerm_sub s k]
  rw [Finset.sum_sub_distrib]

/-- The separate endpoint identity remains available at a standard zero. -/
theorem etaPrimeFactorMirrorDefectPairedPartial_eq_separate_endpoint_difference_of_zero
    {s : ℂ} (_hs : NontrivialRiemannZetaZero s) (_him : s.im ≠ 0)
    (K : ℕ) :
    etaPrimeFactorMirrorDefectPairedPartial K s =
      (Finset.range K).sum (etaPairTerm (criticalMirror s)) -
        (Finset.range K).sum (etaPairTerm s) :=
  etaPrimeFactorMirrorDefectPairedPartial_eq_separate_endpoint_difference K s

/-! ## Whole-sum information firewall -/

/--
Any functional depending only on the finite prime-factor whole-sum value is
also a functional of the old Eta defect partial.  Thus norm, projection, and
other post-processing of that single value cannot by itself create a new
coordinate certificate.
-/
theorem congrArg_of_etaPrimeFactorMirrorDefectPairedPartial_eq_etaDefect
    {α : Type*} (F : ℂ → α) (K : ℕ) (s : ℂ) :
    F (etaPrimeFactorMirrorDefectPairedPartial K s) =
      F (etaCriticalMirrorDefectPairedPartial K s) := by
  exact congrArg F
    (etaPrimeFactorMirrorDefectPairedPartial_eq_etaCriticalMirrorDefectPairedPartial
      K s)

/--
The zero-derived P2-F equality transports the whole-sum functional directly
to the Eta tail.  This is a provenance transport theorem, not a coercive
lower bound for `centeredSigma`.
-/
theorem congrArg_of_etaPrimeFactorMirrorDefectPairedPartial_eq_neg_tail_of_zero
    {α : Type*} (F : ℂ → α)
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) (him : s.im ≠ 0)
    (K : ℕ) :
    F (etaPrimeFactorMirrorDefectPairedPartial K s) =
      F (-etaCriticalMirrorDefectPairTail K s) := by
  exact congrArg F
    (etaPrimeFactorMirrorDefectPairedPartial_eq_neg_tail_of_nontrivialRiemannZetaZero
      hs him K)

/--
Smallness of a complex whole sum does not control the sum of mode energies:
two opposite unit modes have zero sum but strictly positive norm-square
energy.  This concrete countermodel is only an information firewall; it is
not a statement about the Eta source family.
-/
theorem norm_zero_sum_does_not_control_mode_norm_square_energy :
    ∃ z₁ z₂ : ℂ,
      ‖z₁ + z₂‖ = 0 ∧
        0 < ‖z₁‖ ^ 2 + ‖z₂‖ ^ 2 := by
  refine ⟨1, -1, ?_, ?_⟩
  · norm_num
  · norm_num

/-!
The historical finite prime-mirror energy remains a valid coordinate-lower
candidate.  Its existing API proves nonnegativity and centered-coordinate
rigidity, but no theorem in this audit identifies it with the zero-derived
P2-F source or supplies the required zero-derived upper control.
-/

/-- A finite positive-weight mirror energy is nonnegative. -/
theorem primeMirrorEnergy_candidate_nonneg
    {S : Finset ℕ} {weight : ℕ → ℝ}
    (hweight : ∀ n ∈ S, 0 ≤ weight n) (δ : ℝ) :
    0 ≤ primeMirrorEnergy S weight δ :=
  primeMirrorEnergy_nonneg hweight δ

end DkMath.RH.CFBRCProjection
