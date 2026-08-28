/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.PascalPrimePowerCanonicalFold
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.PascalVonMangoldtLSeriesBridge"

/-!
# The finite Pascal prime-power shadow and the von Mangoldt L-series

This is the PPW-011 bridge.  It identifies the finite canonical coefficient
with Mathlib's classical von Mangoldt function, and only then passes to the
usual L-series on its domain of convergence `s.re > 1`.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open DkMath.NumberTheory
open DkMath.NumberTheory.PrimitiveSet
open Filter

/-- DkMath's positive prime-power labels agree with Mathlib's predicate. -/
theorem isPrimePowerLabel_iff_isPrimePow (q : ℕ) :
    IsPrimePowerLabel q ↔ IsPrimePow q := by
  constructor
  · rintro ⟨p, k, hp, hk, hq⟩
    exact (isPrimePow_nat_iff q).mpr ⟨p, k, hp, hk, hq.symm⟩
  · rintro hq
    rcases (isPrimePow_nat_iff q).mp hq with ⟨p, k, hp, hk, hpq⟩
    exact ⟨p, k, hp, hk, hpq.symm⟩

/-- The PPW canonical coefficient is exactly the classical von Mangoldt value. -/
theorem canonicalPrimePowerShadowCost_eq_vonMangoldt (q : ℕ) :
    canonicalPrimePowerShadowCost q = ArithmeticFunction.vonMangoldt q := by
  by_cases hq : IsPrimePowerLabel q
  · rcases hq with ⟨p, k, hp, hk, hpq⟩
    rw [canonicalPrimePowerShadowCost_eq_log_of_witness hp hk hpq]
    calc
      Real.log (p : ℝ) = ArithmeticFunction.vonMangoldt (p ^ k) := by
        rw [ArithmeticFunction.vonMangoldt_apply_pow (Nat.ne_of_gt hk),
          ArithmeticFunction.vonMangoldt_apply_prime hp]
      _ = ArithmeticFunction.vonMangoldt q := by rw [hpq]
  · have hq' : ¬ IsPrimePow q := by
      simpa [isPrimePowerLabel_iff_isPrimePow q] using hq
    rw [ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hq']
    simp [canonicalPrimePowerShadowCost, hq]

/-- The canonical finite PHZ is the finite von Mangoldt Dirichlet sum. -/
theorem pascalPrimePowerPHZCanonicalUpTo_eq_vonMangoldt_sum
    (X : ℕ) (s : ℂ) :
    pascalPrimePowerPHZCanonicalUpTo X s =
      ∑ q ∈ Finset.range (X + 1),
        (ArithmeticFunction.vonMangoldt q : ℂ) * ((q : ℂ) ^ (-s)) := by
  unfold pascalPrimePowerPHZCanonicalUpTo
  apply Finset.sum_congr rfl
  intro q hq
  rw [canonicalPrimePowerShadowCost_eq_vonMangoldt]

/-- The original pair-indexed finite PHZ is the finite von Mangoldt sum. -/
theorem pascalPrimePowerPHZFiniteUpTo_eq_vonMangoldt_sum
    (X : ℕ) (s : ℂ) :
    pascalPrimePowerPHZFiniteUpTo X s =
      ∑ q ∈ Finset.range (X + 1),
        (ArithmeticFunction.vonMangoldt q : ℂ) * ((q : ℂ) ^ (-s)) := by
  rw [pascalPrimePowerPHZFiniteUpTo_eq_canonical]
  exact pascalPrimePowerPHZCanonicalUpTo_eq_vonMangoldt_sum X s

/-- The von Mangoldt coefficient has the zero convention required by `LSeries`. -/
@[simp] theorem vonMangoldtComplexCoeff_zero :
    (ArithmeticFunction.vonMangoldt 0 : ℂ) = 0 := by
  norm_cast

/-- A von Mangoldt L-series term is its usual Dirichlet monomial. -/
theorem vonMangoldt_LSeries_term_eq (s : ℂ) (n : ℕ) :
    LSeries.term (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) s n =
      (ArithmeticFunction.vonMangoldt n : ℂ) * ((n : ℂ) ^ (-s)) := by
  exact LSeries.term_def₀ vonMangoldtComplexCoeff_zero s n

/-- The canonical finite PHZ is a finite partial sum of the von Mangoldt L-series. -/
theorem pascalPrimePowerPHZCanonicalUpTo_eq_LSeries_partialSum
    (X : ℕ) (s : ℂ) :
    pascalPrimePowerPHZCanonicalUpTo X s =
      ∑ n ∈ Finset.range (X + 1),
        LSeries.term (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) s n := by
  rw [pascalPrimePowerPHZCanonicalUpTo_eq_vonMangoldt_sum]
  apply Finset.sum_congr rfl
  intro n hn
  symm
  exact vonMangoldt_LSeries_term_eq s n

/-- The pair-indexed finite PHZ is the corresponding L-series partial sum. -/
theorem pascalPrimePowerPHZFiniteUpTo_eq_LSeries_partialSum
    (X : ℕ) (s : ℂ) :
    pascalPrimePowerPHZFiniteUpTo X s =
      ∑ n ∈ Finset.range (X + 1),
        LSeries.term (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) s n := by
  rw [pascalPrimePowerPHZFiniteUpTo_eq_vonMangoldt_sum]
  apply Finset.sum_congr rfl
  intro n hn
  symm
  exact vonMangoldt_LSeries_term_eq s n

/-- In `s.re > 1`, canonical finite PHZ cutoffs converge to the von Mangoldt L-series. -/
theorem tendsto_pascalPrimePowerPHZCanonicalUpTo_LSeries
    {s : ℂ} (hs : 1 < s.re) :
    Tendsto (fun X => pascalPrimePowerPHZCanonicalUpTo X s) atTop
      (nhds (LSeries (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) s)) := by
  have hsum := (ArithmeticFunction.LSeriesSummable_vonMangoldt hs).LSeriesHasSum
  rw [LSeriesHasSum] at hsum
  simpa only [pascalPrimePowerPHZCanonicalUpTo_eq_LSeries_partialSum] using
    (tendsto_add_atTop_iff_nat 1).mpr hsum.tendsto_sum_nat

/-- In `s.re > 1`, pair-indexed finite PHZ cutoffs converge to the von Mangoldt L-series. -/
theorem tendsto_pascalPrimePowerPHZFiniteUpTo_LSeries
    {s : ℂ} (hs : 1 < s.re) :
    Tendsto (fun X => pascalPrimePowerPHZFiniteUpTo X s) atTop
      (nhds (LSeries (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) s)) := by
  simpa only [pascalPrimePowerPHZFiniteUpTo_eq_canonical] using
    tendsto_pascalPrimePowerPHZCanonicalUpTo_LSeries hs

/-- In the safe half-plane, finite PPW cutoffs converge to `-ζ'(s) / ζ(s)`. -/
theorem tendsto_pascalPrimePowerPHZFiniteUpTo_neg_deriv_riemannZeta_div
    {s : ℂ} (hs : 1 < s.re) :
    Tendsto (fun X => pascalPrimePowerPHZFiniteUpTo X s) atTop
      (nhds (- deriv riemannZeta s / riemannZeta s)) := by
  rw [← ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs]
  exact tendsto_pascalPrimePowerPHZFiniteUpTo_LSeries hs

end DkMath.RH.CFBRCProjection
