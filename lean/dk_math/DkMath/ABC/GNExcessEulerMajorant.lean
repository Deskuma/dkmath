/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.ABC.GNExcessActiveProfiles
import Mathlib.Analysis.PSeries

#print "file: DkMath.ABC.GNExcessEulerMajorant"

set_option linter.style.longLine false
set_option linter.style.emptyLine false

/-!
# Summable envelopes for the finite GN excess Euler product

This module isolates the analytic obligation left by the finite active-profile
factorization.  A nonnegative summable local envelope, uniform in the finite
excess cap, yields an Euler-density constant independent of the finite prime
set and of the interval endpoint.

The concrete `t = 1 / 2` local estimate is deliberately not assumed as a
theorem here: it remains the next arithmetic-analytic obligation.
-/

namespace DkMath.ABC

/-- The positive-excess part of one capped local Euler factor. -/
noncomputable def GNExcessLocalDensityTail
    (p q K : ℕ) (t : ℝ) : ℝ :=
  ∑ j ∈ (Finset.range K).erase 0,
    GNExcessLocalDensityWeight p q j t

/-- A summable local envelope gives a constant independent of the finite prime
family and of all finite valuation caps. -/
noncomputable def GNExcessEulerEnvelope
    (g : ℕ → ℝ) : ℝ :=
  Real.exp (∑' q, g q)

/-- The canonical `q^(-3/2)` envelope proposed for the fixed Chernoff
parameter `t = 1 / 2`.  The coefficient `4 * (p - 1)` leaves room for the
local geometric tail. -/
noncomputable def GNExcessHalfPowerEnvelope
    (p q : ℕ) : ℝ :=
  4 * ((p - 1 : ℕ) : ℝ) /
    (q : ℝ) ^ ((3 : ℝ) / 2)

/-- The resulting candidate uniform constant for the finite small-profile
Euler density. -/
noncomputable def GNExcessHalfEulerConstant
    (p : ℕ) : ℝ :=
  GNExcessEulerEnvelope
    (GNExcessHalfPowerEnvelope p)

/-- Every local density weight is nonnegative. -/
theorem GNExcessLocalDensityWeight_nonneg
    {p q j : ℕ} {t : ℝ} :
    0 ≤ GNExcessLocalDensityWeight p q j t := by
  unfold GNExcessLocalDensityWeight
  split_ifs
  · norm_num
  · positivity

/-- Every capped local Euler factor is nonnegative. -/
theorem GNExcessLocalDensityFactor_nonneg
    {p q K : ℕ} {t : ℝ} :
    0 ≤ GNExcessLocalDensityFactor p q K t := by
  unfold GNExcessLocalDensityFactor
  exact Finset.sum_nonneg fun _ _ =>
    GNExcessLocalDensityWeight_nonneg

/-- The canonical half-power envelope is pointwise nonnegative. -/
theorem GNExcessHalfPowerEnvelope_nonneg
    {p q : ℕ} :
    0 ≤ GNExcessHalfPowerEnvelope p q := by
  unfold GNExcessHalfPowerEnvelope
  positivity

/-- The canonical half-power envelope is summable over all natural numbers.
No prime-number theorem or prime-specific analytic input is used. -/
theorem summable_GNExcessHalfPowerEnvelope
    (p : ℕ) :
    Summable (GNExcessHalfPowerEnvelope p) := by
  have hbase :
      Summable
        (fun q : ℕ =>
          1 / (q : ℝ) ^ ((3 : ℝ) / 2)) :=
    Real.summable_one_div_nat_rpow.mpr (by norm_num)
  simpa [GNExcessHalfPowerEnvelope, div_eq_mul_inv,
    ← mul_assoc] using
      hbase.mul_left
        (4 * ((p - 1 : ℕ) : ℝ))

/-- For a nonempty cap, the local factor is one plus its positive-excess
tail. -/
theorem GNExcessLocalDensityFactor_eq_one_add_tail
    {p q K : ℕ} {t : ℝ}
    (hK : 0 < K) :
    GNExcessLocalDensityFactor p q K t =
      1 + GNExcessLocalDensityTail p q K t := by
  unfold GNExcessLocalDensityFactor
    GNExcessLocalDensityTail
  rw [← Finset.sum_erase_add _ _
    (Finset.mem_range.mpr hK)]
  simp [GNExcessLocalDensityWeight, add_comm]

/-- Bounding the positive local tail bounds the full local factor
exponentially. -/
theorem GNExcessLocalDensityFactor_le_exp_of_tail_le
    {p q K : ℕ} {t y : ℝ}
    (hK : 0 < K)
    (htail : GNExcessLocalDensityTail p q K t ≤ y) :
    GNExcessLocalDensityFactor p q K t ≤ Real.exp y := by
  rw [GNExcessLocalDensityFactor_eq_one_add_tail hK]
  simpa [add_comm] using
    ((Real.add_one_le_exp _).trans
      (Real.exp_le_exp.mpr htail))

/-- Abstract finite-to-infinite Euler majorant.

The hypothesis `hlocal` is the sole local analytic input: it must hold
uniformly in the finite cap `K`.  Summability of `g` then removes both the
prime family `Q` and the interval endpoint `X` from the bound. -/
theorem GNExcessFiniteEulerDensity_le_envelope
    {Q : Finset ℕ} {p b X : ℕ} {t : ℝ}
    {g : ℕ → ℝ}
    (hg0 : ∀ q, 0 ≤ g q)
    (hg : Summable g)
    (hlocal : ∀ q ∈ Q, ∀ K, 0 < K →
      GNExcessLocalDensityFactor p q K t ≤
        Real.exp (g q)) :
    GNExcessFiniteEulerDensity Q p b X t ≤
      GNExcessEulerEnvelope g := by
  rw [sum_GNExcessProfileDensityWeight_eq_prod]
  calc
    (∏ q ∈ Q,
        GNExcessLocalDensityFactor p q
          (Nat.log q (p * (X + b) ^ p) + 1) t) ≤
        ∏ q ∈ Q, Real.exp (g q) := by
      exact Finset.prod_le_prod
        (fun q _ =>
          GNExcessLocalDensityFactor_nonneg)
        (fun q hq =>
          hlocal q hq
            (Nat.log q (p * (X + b) ^ p) + 1)
            (Nat.succ_pos _))
    _ = Real.exp (∑ q ∈ Q, g q) := by
      rw [Real.exp_sum]
    _ ≤ Real.exp (∑' q, g q) := by
      apply Real.exp_le_exp.mpr
      exact hg.sum_le_tsum Q
        (fun q _ => hg0 q)
    _ = GNExcessEulerEnvelope g := rfl

/-- Tail-envelope form of the uniform Euler majorant.  This is the direct API
for a future `t = 1 / 2` local geometric estimate. -/
theorem GNExcessFiniteEulerDensity_le_envelope_of_tail
    {Q : Finset ℕ} {p b X : ℕ} {t : ℝ}
    {g : ℕ → ℝ}
    (hg0 : ∀ q, 0 ≤ g q)
    (hg : Summable g)
    (htail : ∀ q ∈ Q, ∀ K, 0 < K →
      GNExcessLocalDensityTail p q K t ≤ g q) :
    GNExcessFiniteEulerDensity Q p b X t ≤
      GNExcessEulerEnvelope g := by
  apply GNExcessFiniteEulerDensity_le_envelope
    hg0 hg
  intro q hq K hK
  exact GNExcessLocalDensityFactor_le_exp_of_tail_le
    hK (htail q hq K hK)

/-- Fixed-parameter `t = 1 / 2` endpoint.  The displayed `htail` hypothesis is
the smallest remaining local analytic lemma: once supplied, the finite Euler
density is bounded by a constant depending only on `p`. -/
theorem GNExcessFiniteEulerDensity_half_le
    {Q : Finset ℕ} {p b X : ℕ}
    (hQprime : ∀ q ∈ Q, Nat.Prime q)
    (htail : ∀ q K, Nat.Prime q → 0 < K →
      GNExcessLocalDensityTail p q K ((1 : ℝ) / 2) ≤
        GNExcessHalfPowerEnvelope p q) :
    GNExcessFiniteEulerDensity Q p b X ((1 : ℝ) / 2) ≤
      GNExcessHalfEulerConstant p := by
  exact GNExcessFiniteEulerDensity_le_envelope_of_tail
    (fun q => GNExcessHalfPowerEnvelope_nonneg)
    (summable_GNExcessHalfPowerEnvelope p)
    (fun q hq K hK => htail q K (hQprime q hq) hK)

/-- Small-profile moment bound after inserting the fixed half-power Euler
envelope.  The large-modulus boundary packet remains explicit. -/
theorem exp_GNExcessMassAt_sum_le_halfEuler_add_large
    {Q : Finset ℕ} {p b X : ℕ}
    (hp : Nat.Prime p)
    (hb : 0 < b)
    (hQprime : ∀ q ∈ Q, Nat.Prime q)
    (hQp : ∀ q ∈ Q, ¬ q ∣ p)
    (hQb : ∀ q ∈ Q, ¬ q ∣ b)
    (htail : ∀ q K, Nat.Prime q → 0 < K →
      GNExcessLocalDensityTail p q K ((1 : ℝ) / 2) ≤
        GNExcessHalfPowerEnvelope p q) :
    ∑ a ∈ Finset.Icc 0 X,
        Real.exp (((1 : ℝ) / 2) *
          GNExcessMassAt Q p b a) ≤
      2 * (X + 1 : ℝ) *
          GNExcessHalfEulerConstant p +
        GNExcessLargeBoundaryProfileSum
          Q p b X ((1 : ℝ) / 2) := by
  have hEuler :=
    GNExcessFiniteEulerDensity_half_le
      (Q := Q) (b := b) (X := X)
      hQprime htail
  have hcoef : 0 ≤ 2 * (X + 1 : ℝ) := by
    positivity
  exact (exp_GNExcessMassAt_sum_le_finiteEuler_add_large
    hp hb hQprime hQp hQb).trans
      (add_le_add
        (mul_le_mul_of_nonneg_left hEuler hcoef)
        (le_refl _))

end DkMath.ABC
