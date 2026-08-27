/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.StandardZetaBridge
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.ZeroLocusFactorBridge"

namespace DkMath.RH.CFBRCProjection

/--
Two functions have the same zero locus on `Domain` when nonvanishing left and
right multipliers identify them.

The equation is deliberately symmetric:

`leftMultiplier s * F s = rightMultiplier s * G s`.
-/
structure TwoSidedNonzeroFactorBridge
    (Domain : ℂ → Prop) (F G : ℂ → ℂ) where
  leftMultiplier : ℂ → ℂ
  rightMultiplier : ℂ → ℂ
  factor_eq : ∀ {s : ℂ}, Domain s →
    leftMultiplier s * F s = rightMultiplier s * G s
  leftMultiplier_ne_zero : ∀ {s : ℂ}, Domain s → leftMultiplier s ≠ 0
  rightMultiplier_ne_zero : ∀ {s : ℂ}, Domain s → rightMultiplier s ≠ 0

/-- A two-sided nonzero factor bridge gives exact zero-locus equivalence. -/
theorem TwoSidedNonzeroFactorBridge.zero_iff
    {Domain : ℂ → Prop} {F G : ℂ → ℂ}
    (bridge : TwoSidedNonzeroFactorBridge Domain F G)
    {s : ℂ} (hs : Domain s) :
    F s = 0 ↔ G s = 0 := by
  have hEq := bridge.factor_eq hs
  constructor
  · intro hF
    have hright : bridge.rightMultiplier s * G s = 0 := by
      simpa [hF] using hEq.symm
    exact (mul_eq_zero.mp hright).resolve_left
      (bridge.rightMultiplier_ne_zero hs)
  · intro hG
    have hleft : bridge.leftMultiplier s * F s = 0 := by
      simpa [hG] using hEq
    exact (mul_eq_zero.mp hleft).resolve_left
      (bridge.leftMultiplier_ne_zero hs)

/-- Domain excluding the trivial negative-even zeros and the pole point. -/
def RiemannZetaNontrivialDomain (s : ℂ) : Prop :=
  (¬∃ n : ℕ, s = -2 * (n + 1)) ∧ s ≠ 1

/-- The local nontrivial-zero predicate is zeta vanishing inside that domain. -/
theorem nontrivialRiemannZetaZero_iff
    (s : ℂ) :
    NontrivialRiemannZetaZero s ↔
      riemannZeta s = 0 ∧ RiemannZetaNontrivialDomain s := by
  rfl

/-- Standard CFBRC value viewed as a complex function of `s`. -/
noncomputable def standardCFBRCValue
    (d : ℕ) (phase : ℂ → ℝ) (s : ℂ) : ℂ :=
  offCriticalCFBRC d s.re (phase s)

/--
A precise zero-locus-factorization formulation of the desired standard-zeta to
CFBRC bridge.
-/
abbrev StandardZetaCFBRCFactorization
    (d : ℕ) (phase : ℂ → ℝ) :=
  TwoSidedNonzeroFactorBridge
    RiemannZetaNontrivialDomain
    riemannZeta
    (standardCFBRCValue d phase)

/-- A standard factorization bridge supplies the direct `map_zero` obligation. -/
theorem standardZeta_map_zero_of_factorization
    {d : ℕ} {phase : ℂ → ℝ}
    (bridge : StandardZetaCFBRCFactorization d phase)
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) :
    offCriticalCFBRC d s.re (phase s) = 0 := by
  have hDomain : RiemannZetaNontrivialDomain s := hs.2
  have hzero : standardCFBRCValue d phase s = 0 :=
    (bridge.zero_iff hDomain).mp hs.1
  exact hzero

/--
Any positive-degree two-sided nonzero factorization of standard zeta by the
standard CFBRC value proves Mathlib's formal Riemann hypothesis.
-/
theorem riemannHypothesis_of_standardZetaCFBRCFactorization
    {d : ℕ} (hd : 0 < d) (phase : ℂ → ℝ)
    (bridge : StandardZetaCFBRCFactorization d phase) :
    RiemannHypothesis := by
  exact riemannHypothesis_of_standardZeta_map_zero hd phase
    (fun hs => standardZeta_map_zero_of_factorization bridge hs)

end DkMath.RH.CFBRCProjection
