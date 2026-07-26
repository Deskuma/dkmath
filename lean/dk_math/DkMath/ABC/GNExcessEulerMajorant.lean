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

This module completes the analytic small-profile side left by the finite
active-profile factorization.  At `t = 1 / 2`, a direct geometric estimate
bounds every prime local tail by a summable `q^(-3/2)` envelope.  The resulting
Euler-density constant is independent of the finite prime set and of the
interval endpoint.
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

/-- The exponential half-power has square equal to its positive base. -/
private theorem exp_half_log_sq
    {q : ℕ}
    (hq : 0 < q) :
    Real.exp (((1 : ℝ) / 2) *
        Real.log (q : ℝ)) ^ 2 =
      (q : ℝ) := by
  rw [pow_two, ← Real.exp_add]
  rw [show
    (1 / 2 : ℝ) * Real.log (q : ℝ) +
        (1 / 2 : ℝ) * Real.log (q : ℝ) =
      Real.log (q : ℝ) by ring]
  exact Real.exp_log (by exact_mod_cast hq)

/-- At a prime base, the half-power ratio is at most `3 / 4`. -/
private theorem exp_half_log_div_le_three_quarters
    {q : ℕ}
    (hq : Nat.Prime q) :
    Real.exp (((1 : ℝ) / 2) *
          Real.log (q : ℝ)) /
        (q : ℝ) ≤
      (3 : ℝ) / 4 := by
  have hq0 : (0 : ℝ) < (q : ℝ) := by
    exact_mod_cast hq.pos
  have hq2 : (2 : ℝ) ≤ (q : ℝ) := by
    exact_mod_cast hq.two_le
  have hx0 :
      0 ≤ Real.exp (((1 : ℝ) / 2) *
        Real.log (q : ℝ)) :=
    (Real.exp_pos _).le
  have hx2 :=
    exp_half_log_sq hq.pos
  apply (div_le_iff₀ hq0).2
  nlinarith

/-- Successive positive-excess local weights decay by at least `3 / 4`. -/
private theorem GNExcessLocalDensityWeight_half_succ_le
    {p q j : ℕ}
    (hq : Nat.Prime q)
    (hj : 0 < j) :
    GNExcessLocalDensityWeight p q (j + 1)
        ((1 : ℝ) / 2) ≤
      ((3 : ℝ) / 4) *
        GNExcessLocalDensityWeight p q j
          ((1 : ℝ) / 2) := by
  have hq0 : (q : ℝ) ≠ 0 := by
    exact_mod_cast hq.ne_zero
  have hratio :
      GNExcessLocalDensityWeight p q (j + 1)
          ((1 : ℝ) / 2) =
        GNExcessLocalDensityWeight p q j
            ((1 : ℝ) / 2) *
          (Real.exp (((1 : ℝ) / 2) *
              Real.log (q : ℝ)) /
            (q : ℝ)) := by
    unfold GNExcessLocalDensityWeight
    rw [if_neg (Nat.succ_ne_zero j),
      if_neg (Nat.ne_of_gt hj)]
    rw [pow_succ]
    have hexp :
        Real.exp ((1 / 2 : ℝ) * (j + 1 : ℕ) *
            Real.log (q : ℝ)) =
          Real.exp ((1 / 2 : ℝ) * (j : ℝ) *
              Real.log (q : ℝ)) *
            Real.exp ((1 / 2 : ℝ) *
              Real.log (q : ℝ)) := by
      rw [← Real.exp_add]
      congr 1
      push_cast
      ring
    rw [hexp]
    field_simp
  rw [hratio]
  rw [mul_comm ((3 : ℝ) / 4)]
  exact mul_le_mul_of_nonneg_left
    (exp_half_log_div_le_three_quarters hq)
    GNExcessLocalDensityWeight_nonneg

/-- Positive local weights are dominated by the corresponding geometric
sequence with ratio `3 / 4`. -/
private theorem GNExcessLocalDensityWeight_half_succ_le_geometric
    {p q : ℕ}
    (hq : Nat.Prime q)
    (n : ℕ) :
    GNExcessLocalDensityWeight p q (n + 1)
        ((1 : ℝ) / 2) ≤
      GNExcessLocalDensityWeight p q 1
          ((1 : ℝ) / 2) *
        ((3 : ℝ) / 4) ^ n := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      calc
        GNExcessLocalDensityWeight p q (n + 1 + 1)
            ((1 : ℝ) / 2) ≤
            ((3 : ℝ) / 4) *
              GNExcessLocalDensityWeight p q (n + 1)
                ((1 : ℝ) / 2) :=
          GNExcessLocalDensityWeight_half_succ_le
            hq (Nat.succ_pos n)
        _ ≤ ((3 : ℝ) / 4) *
              (GNExcessLocalDensityWeight p q 1
                  ((1 : ℝ) / 2) *
                ((3 : ℝ) / 4) ^ n) :=
          mul_le_mul_of_nonneg_left ih (by norm_num)
        _ = GNExcessLocalDensityWeight p q 1
              ((1 : ℝ) / 2) *
            ((3 : ℝ) / 4) ^ (n + 1) := by
          rw [pow_succ]
          ring

/-- The fixed finite geometric sum is bounded by `4`. -/
private theorem sum_three_quarters_pow_le_four
    (n : ℕ) :
    ∑ i ∈ Finset.range n,
        ((3 : ℝ) / 4) ^ i ≤ 4 := by
  have hgeom :
      ∑ i ∈ Finset.range n,
          ((3 : ℝ) / 4) ^ i =
        4 * (1 - ((3 : ℝ) / 4) ^ n) := by
    induction n with
    | zero =>
        norm_num
    | succ n ih =>
        rw [Finset.sum_range_succ, ih, pow_succ]
        ring
  rw [hgeom]
  have hpownonneg :
      0 ≤ ((3 : ℝ) / 4) ^ n := by
    positivity
  nlinarith

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

/-- The finite positive-excess local tail at `t = 1 / 2` is bounded by the
canonical `q^(-3/2)` envelope. -/
theorem GNExcessLocalDensityTail_half_le
    {p q K : ℕ}
    (hq : Nat.Prime q)
    (hK : 0 < K) :
    GNExcessLocalDensityTail p q K
        ((1 : ℝ) / 2) ≤
      GNExcessHalfPowerEnvelope p q := by
  have hK1 : 1 ≤ K := hK
  have hKsub : K - 1 + 1 = K :=
    Nat.sub_add_cancel hK1
  have hset :
      (Finset.range K).erase 0 =
        Finset.Ico 1 K := by
    ext j
    simp [Nat.one_le_iff_ne_zero]
  have hreindex :
      (∑ j ∈ Finset.Ico 1 K,
          GNExcessLocalDensityWeight p q j
            ((1 : ℝ) / 2)) =
        ∑ i ∈ Finset.range (K - 1),
          GNExcessLocalDensityWeight p q (i + 1)
            ((1 : ℝ) / 2) := by
    simpa [hKsub] using
      (Finset.sum_Ico_add'
        (fun j =>
          GNExcessLocalDensityWeight p q j
            ((1 : ℝ) / 2))
        0 (K - 1) 1).symm
  have hfirst :
      4 *
          GNExcessLocalDensityWeight p q 1
            ((1 : ℝ) / 2) =
        GNExcessHalfPowerEnvelope p q := by
    have hq0 : (0 : ℝ) < (q : ℝ) := by
      exact_mod_cast hq.pos
    have hrpow :
        (q : ℝ) ^ ((3 : ℝ) / 2) =
          (q : ℝ) *
            Real.exp (((1 : ℝ) / 2) *
              Real.log (q : ℝ)) := by
      rw [Real.rpow_def_of_pos hq0]
      rw [show
        Real.log (q : ℝ) * ((3 : ℝ) / 2) =
          Real.log (q : ℝ) +
            ((1 : ℝ) / 2) *
              Real.log (q : ℝ) by ring]
      rw [Real.exp_add, Real.exp_log hq0]
    unfold GNExcessLocalDensityWeight
      GNExcessHalfPowerEnvelope
    simp only [if_false, Nat.one_ne_zero,
      Nat.cast_one]
    rw [hrpow]
    field_simp
    rw [show
      Real.log (q : ℝ) / 2 =
        ((1 : ℝ) / 2) *
          Real.log (q : ℝ) by ring]
    rw [exp_half_log_sq hq.pos]
    ring
  unfold GNExcessLocalDensityTail
  rw [hset, hreindex]
  calc
    (∑ i ∈ Finset.range (K - 1),
        GNExcessLocalDensityWeight p q (i + 1)
          ((1 : ℝ) / 2)) ≤
        ∑ i ∈ Finset.range (K - 1),
          (GNExcessLocalDensityWeight p q 1
              ((1 : ℝ) / 2) *
            ((3 : ℝ) / 4) ^ i) := by
      exact Finset.sum_le_sum fun i _ =>
        GNExcessLocalDensityWeight_half_succ_le_geometric
          hq i
    _ = GNExcessLocalDensityWeight p q 1
          ((1 : ℝ) / 2) *
        (∑ i ∈ Finset.range (K - 1),
          ((3 : ℝ) / 4) ^ i) := by
      rw [Finset.mul_sum]
    _ ≤ GNExcessLocalDensityWeight p q 1
          ((1 : ℝ) / 2) * 4 := by
      exact mul_le_mul_of_nonneg_left
        (sum_three_quarters_pow_le_four (K - 1))
        GNExcessLocalDensityWeight_nonneg
    _ = GNExcessHalfPowerEnvelope p q := by
      rw [mul_comm, hfirst]

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

/-- Unconditional fixed-parameter `t = 1 / 2` Euler-density endpoint for a
finite prime family.  The bound depends only on `p`, not on `Q`, `b`, or `X`. -/
theorem GNExcessFiniteEulerDensity_half_le
    {Q : Finset ℕ} {p b X : ℕ}
    (hQprime : ∀ q ∈ Q, Nat.Prime q) :
    GNExcessFiniteEulerDensity Q p b X ((1 : ℝ) / 2) ≤
      GNExcessHalfEulerConstant p := by
  exact GNExcessFiniteEulerDensity_le_envelope_of_tail
    (fun q => GNExcessHalfPowerEnvelope_nonneg)
    (summable_GNExcessHalfPowerEnvelope p)
    (fun q hq K hK =>
      GNExcessLocalDensityTail_half_le
        (hQprime q hq) hK)

/-- Small-profile moment bound after inserting the fixed half-power Euler
envelope.  The large-modulus boundary packet remains explicit. -/
theorem exp_GNExcessMassAt_sum_le_halfEuler_add_large
    {Q : Finset ℕ} {p b X : ℕ}
    (hp : Nat.Prime p)
    (hb : 0 < b)
    (hQprime : ∀ q ∈ Q, Nat.Prime q)
    (hQp : ∀ q ∈ Q, ¬ q ∣ p)
    (hQb : ∀ q ∈ Q, ¬ q ∣ b) :
    ∑ a ∈ Finset.Icc 0 X,
        Real.exp (((1 : ℝ) / 2) *
          GNExcessMassAt Q p b a) ≤
      2 * (X + 1 : ℝ) *
          GNExcessHalfEulerConstant p +
        GNExcessLargeBoundaryProfileSum
          Q p b X ((1 : ℝ) / 2) := by
  have hEuler :=
    GNExcessFiniteEulerDensity_half_le
      (Q := Q) (p := p) (b := b) (X := X)
      hQprime
  have hcoef : 0 ≤ 2 * (X + 1 : ℝ) := by
    positivity
  exact (exp_GNExcessMassAt_sum_le_finiteEuler_add_large
    hp hb hQprime hQp hQb).trans
      (add_le_add
        (mul_le_mul_of_nonneg_left hEuler hcoef)
        (le_refl _))

end DkMath.ABC
