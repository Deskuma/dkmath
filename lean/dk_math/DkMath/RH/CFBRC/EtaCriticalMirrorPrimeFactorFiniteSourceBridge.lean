/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedTail
import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameGrowingBlockTailRemainder
import DkMath.NumberTheory.PrimitiveSet.FullChannelLogSum
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Tactic

/-!
# ZDI-005: Eta prime-factor finite source bridge

This module exposes the finite Eta main term through the genuine prime-factor
supports of its natural bases.  It uses only finite factorization logarithms
and the already proved zero-derived Eta finite-partial-plus-tail identity.
No Euler-product convergence, zero-point logarithmic derivative, or RH
provider is introduced.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open DkMath.NumberTheory.PrimitiveSet
open DkMath.RH.Weave.Analytic

/--
The negative complex power of a positive natural base is the exponential of
the finite prime-factor logarithm sum.  This is an exact finite identity; it
does not use a Dirichlet-series convergence domain.
-/
theorem natCpowNeg_eq_exp_factorization_logSum
    {n : ℕ} (hn : 0 < n) (s : ℂ) :
    (n : ℂ) ^ (-s) =
      Complex.exp
        (-s *
          (((n.factorization.support.sum fun p =>
              (n.factorization p : ℝ) * Real.log (p : ℝ)) : ℝ) : ℂ)) := by
  have hn0 : (n : ℂ) ≠ 0 := by
    exact_mod_cast hn.ne'
  rw [Complex.cpow_def_of_ne_zero hn0]
  rw [← Complex.natCast_log]
  rw [sum_factorization_mul_log_eq_log_nat hn.ne']
  congr 1
  ring

/--
Each unsigned Eta natural-index mode has an exact finite prime-factor
logarithmic representation.  Positivity of `m + 1` supplies the nonzero
condition required by the factorization theorem.
-/
theorem etaUnsignedVector_eq_primeFactorLogExp
    (s : ℂ) (m : ℕ) :
    etaUnsignedVector s m =
      Complex.exp
        (-s *
          (((((m + 1).factorization.support.sum fun p =>
              ((m + 1).factorization p : ℝ) * Real.log (p : ℝ)) : ℝ)) : ℂ)) := by
  unfold etaUnsignedVector
  exact natCpowNeg_eq_exp_factorization_logSum (by omega) s

/-
The following pair-level statement is deliberately kept as a finite sum of
factorization-log exponentials.  It records the source coordinates without
introducing a von Mangoldt series or an infinite Euler-product observable.
-/
/-- The two natural bases in one Eta pair admit exact prime-factor forms. -/
theorem etaPairTerm_eq_primeFactorLogExp_sub
    (s : ℂ) (k : ℕ) :
    etaPairTerm s k =
      Complex.exp
          (-s *
            (((((2 * k + 1).factorization.support.sum fun p =>
                ((2 * k + 1).factorization p : ℝ) * Real.log (p : ℝ)) : ℝ)) : ℂ)) -
        Complex.exp
          (-s *
            (((((2 * k + 2).factorization.support.sum fun p =>
                ((2 * k + 2).factorization p : ℝ) * Real.log (p : ℝ)) : ℝ)) : ℂ)) := by
  unfold etaPairTerm
  rw [etaUnsignedVector_eq_primeFactorLogExp,
    etaUnsignedVector_eq_primeFactorLogExp]

/-- The critical-mirror Eta defect pair is a finite prime-factor expression. -/
theorem etaCriticalMirrorDefectPairTerm_eq_primeFactorLogExp_sub
    (s : ℂ) (k : ℕ) :
    etaCriticalMirrorDefectPairTerm s k =
      (Complex.exp
          (-criticalMirror s *
            (((((2 * k + 1).factorization.support.sum fun p =>
                ((2 * k + 1).factorization p : ℝ) * Real.log (p : ℝ)) : ℝ)) : ℂ)) -
        Complex.exp
          (-criticalMirror s *
            (((((2 * k + 2).factorization.support.sum fun p =>
                ((2 * k + 2).factorization p : ℝ) * Real.log (p : ℝ)) : ℝ)) : ℂ))) -
      (Complex.exp
          (-s *
            (((((2 * k + 1).factorization.support.sum fun p =>
                ((2 * k + 1).factorization p : ℝ) * Real.log (p : ℝ)) : ℝ)) : ℂ)) -
        Complex.exp
          (-s *
            (((((2 * k + 2).factorization.support.sum fun p =>
                ((2 * k + 2).factorization p : ℝ) * Real.log (p : ℝ)) : ℝ)) : ℂ))) := by
  rw [etaCriticalMirrorDefectPairTerm_eq_etaPairTerm_sub,
    etaPairTerm_eq_primeFactorLogExp_sub,
    etaPairTerm_eq_primeFactorLogExp_sub]

/--
The finite prime-factor source coordinate for one critical-mirror Eta pair.
The immediately following characterization theorem identifies it exactly with
the already defined Eta defect pair; this definition introduces no new tail.
-/
noncomputable def etaPrimeFactorMirrorDefectPairTerm
    (s : ℂ) (k : ℕ) : ℂ :=
  (Complex.exp
      (-criticalMirror s *
        (((((2 * k + 1).factorization.support.sum fun p =>
            ((2 * k + 1).factorization p : ℝ) * Real.log (p : ℝ)) : ℝ)) : ℂ)) -
    Complex.exp
      (-criticalMirror s *
        (((((2 * k + 2).factorization.support.sum fun p =>
            ((2 * k + 2).factorization p : ℝ) * Real.log (p : ℝ)) : ℝ)) : ℂ))) -
  (Complex.exp
      (-s *
        (((((2 * k + 1).factorization.support.sum fun p =>
            ((2 * k + 1).factorization p : ℝ) * Real.log (p : ℝ)) : ℝ)) : ℂ)) -
    Complex.exp
      (-s *
        (((((2 * k + 2).factorization.support.sum fun p =>
            ((2 * k + 2).factorization p : ℝ) * Real.log (p : ℝ)) : ℝ)) : ℂ)))

/-- The finite prime-factor pair coordinate is the exact Eta defect pair. -/
theorem etaPrimeFactorMirrorDefectPairTerm_eq_etaCriticalMirrorDefectPairTerm
    (s : ℂ) (k : ℕ) :
    etaPrimeFactorMirrorDefectPairTerm s k =
      etaCriticalMirrorDefectPairTerm s k := by
  unfold etaPrimeFactorMirrorDefectPairTerm
  exact (etaCriticalMirrorDefectPairTerm_eq_primeFactorLogExp_sub s k).symm

/-- Finite sum of the prime-factor Eta source coordinates up to pair index `K`. -/
noncomputable def etaPrimeFactorMirrorDefectPairedPartial
    (K : ℕ) (s : ℂ) : ℂ :=
  (Finset.range K).sum (etaPrimeFactorMirrorDefectPairTerm s)

/-- The finite prime-factor source sum is the existing Eta defect partial sum. -/
theorem etaPrimeFactorMirrorDefectPairedPartial_eq_etaCriticalMirrorDefectPairedPartial
    (K : ℕ) (s : ℂ) :
    etaPrimeFactorMirrorDefectPairedPartial K s =
      etaCriticalMirrorDefectPairedPartial K s := by
  unfold etaPrimeFactorMirrorDefectPairedPartial etaCriticalMirrorDefectPairedPartial
  apply Finset.sum_congr rfl
  intro k hk
  exact etaPrimeFactorMirrorDefectPairTerm_eq_etaCriticalMirrorDefectPairTerm s k

/--
At a nonreal nontrivial zeta zero, the finite prime-factor source sum is the
negative of the existing Eta defect tail.  This is the ZDI-005 P2-F bridge:
the left side is finite and prime-factorized, while the zero provenance enters
only through the already proved Eta partial-plus-tail identity.
-/
theorem etaPrimeFactorMirrorDefectPairedPartial_eq_neg_tail_of_nontrivialRiemannZetaZero
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) (him : s.im ≠ 0)
    (K : ℕ) :
    etaPrimeFactorMirrorDefectPairedPartial K s =
      -etaCriticalMirrorDefectPairTail K s := by
  calc
    etaPrimeFactorMirrorDefectPairedPartial K s =
        etaCriticalMirrorDefectPairedPartial K s :=
      etaPrimeFactorMirrorDefectPairedPartial_eq_etaCriticalMirrorDefectPairedPartial K s
    _ = -etaCriticalMirrorDefectPairTail K s :=
      etaCriticalMirrorDefectPairedPartial_eq_neg_tail_of_nontrivialRiemannZetaZero
        hs him K

/--
The P2-F finite source inherits the existing explicit p-series tail majorant.
This is a transport of the established Q2 tail estimate, not a new estimate
for the factorization-log sum and not a bound on `centeredSigma`.
-/
theorem norm_etaPrimeFactorMirrorDefectPairedPartial_le_powerBound
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) (him : s.im ≠ 0)
    {K : ℕ} (hK : 1 ≤ K) :
    ‖etaPrimeFactorMirrorDefectPairedPartial K s‖ ≤
      etaCriticalMirrorDefectPairTailPowerBound s K := by
  rw [etaPrimeFactorMirrorDefectPairedPartial_eq_neg_tail_of_nontrivialRiemannZetaZero
    hs him K]
  simpa only [norm_neg] using
    (norm_etaCriticalMirrorDefectPairTail_le_powerBound
      (nontrivialRiemannZetaZero_re_pos hs)
      (criticalMirror_re_pos_of_nontrivialRiemannZetaZero hs) hK)

end DkMath.RH.CFBRCProjection
