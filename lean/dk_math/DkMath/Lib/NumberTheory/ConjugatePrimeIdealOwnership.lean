/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib

#print "file: DkMath.Lib.NumberTheory.ConjugatePrimeIdealOwnership"

/-!
# Conjugate-prime ideal ownership

This module isolates the elementary ideal-theoretic transport behind a
conjugate pair.  It deliberately takes the conjugation transport, the mapped
power factorization, and contraction as hypotheses, so it is independent of a
particular number field or involution.
-/

namespace DkMath.Lib.NumberTheory

/-- A conjugate pair whose product descends through a contracted ideal power
cannot have its first factor in the corresponding successor power when the
base factor is not in that power. -/
theorem not_mem_primePower_succ_of_conjugate_norm_cutoff
    {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (Q : Ideal A) (P Pbar : Ideal B)
    (alpha alphaBar : B) (beta : A) (m : ℕ)
    (hstarMem : alpha ∈ P ^ (m + 1) → alphaBar ∈ Pbar ^ (m + 1))
    (hpair : alpha * alphaBar = f beta)
    (hmapPow : Ideal.map f (Q ^ (m + 1)) = P ^ (m + 1) * Pbar ^ (m + 1))
    (hcontract : Ideal.comap f (Ideal.map f (Q ^ (m + 1))) = Q ^ (m + 1))
    (hBetaNot : beta ∉ Q ^ (m + 1)) :
    alpha ∉ P ^ (m + 1) := by
  intro hAlpha
  have hAlphaBar : alphaBar ∈ Pbar ^ (m + 1) := hstarMem hAlpha
  have hProduct : alpha * alphaBar ∈ P ^ (m + 1) * Pbar ^ (m + 1) :=
    Ideal.mul_mem_mul hAlpha hAlphaBar
  have hImage : f beta ∈ Ideal.map f (Q ^ (m + 1)) := by
    rw [hmapPow]
    simpa only [hpair] using hProduct
  have hBase : beta ∈ Ideal.comap f (Ideal.map f (Q ^ (m + 1))) := by
    change f beta ∈ Ideal.map f (Q ^ (m + 1))
    exact hImage
  rw [hcontract] at hBase
  exact hBetaNot hBase

end DkMath.Lib.NumberTheory
