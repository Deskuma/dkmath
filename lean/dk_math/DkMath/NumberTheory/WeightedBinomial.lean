/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.BinomialPrime
import DkMath.CosmicFormula.Mass.BodyGapSplit
import DkMath.Lib.Cosmic.GTail
import Mathlib.Algebra.BigOperators.Ring.Finset

#print "file: DkMath.NumberTheory.WeightedBinomial"

namespace DkMath
namespace NumberTheory

open DkMath.CosmicFormula
open DkMath.CosmicFormula.Mass

/-!
## Weighted binomial terms

This layer separates three sources of divisibility in a binomial term:

* the coefficient `Nat.choose d k`;
* the `x`-power `x^k`;
* the `u`-power `u^(d-k)`.

It deliberately avoids expanding into a full binomial theorem bridge. That
bridge belongs to the later CFBRC/GN checkpoint.
-/

/-- The `k`-th weighted term in row `d`: `C(d,k) * x^k * u^(d-k)`. -/
def weightedBinomialTerm (d k x u : ℕ) : ℕ :=
  Nat.choose d k * x ^ k * u ^ (d - k)

/-- The full weighted row sum, indexed over `0 ≤ k ≤ d`. -/
def weightedBinomialRowSum (d x u : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (d + 1), weightedBinomialTerm d k x u

/--
The positive weighted tail, indexed by `k+1`.

This removes the `k = 0` boundary vertex `u^d` and keeps all terms with an
`x`-factor.
-/
def weightedBinomialPositiveTailSum (d x u : ℕ) : ℕ :=
  ∑ k ∈ Finset.range d, weightedBinomialTerm d (k + 1) x u

/-- All inner weighted terms in row `d` are divisible by `m`. -/
def AllInnerWeightedTermDivisible (d m x u : ℕ) : Prop :=
  ∀ k, 0 < k → k < d → m ∣ weightedBinomialTerm d k x u

/-- All weighted terms in row `d`, including both boundary vertices, are divisible by `m`. -/
def AllWeightedTermDivisible (d m x u : ℕ) : Prop :=
  ∀ k, k ≤ d → m ∣ weightedBinomialTerm d k x u

/-- Divisibility coming from the binomial coefficient. -/
theorem dvd_weightedBinomialTerm_of_dvd_choose
    {q d k x u : ℕ}
    (h : q ∣ Nat.choose d k) :
    q ∣ weightedBinomialTerm d k x u := by
  unfold weightedBinomialTerm
  exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left h (x ^ k)) (u ^ (d - k))

/-- Divisibility coming from the `x`-power. -/
theorem dvd_weightedBinomialTerm_of_dvd_x
    {q d k x u : ℕ}
    (h : q ∣ x) (hk : 0 < k) :
    q ∣ weightedBinomialTerm d k x u := by
  have hxpow : q ∣ x ^ k := h.pow hk.ne'
  unfold weightedBinomialTerm
  simpa [mul_assoc] using
    dvd_mul_of_dvd_right
      (dvd_mul_of_dvd_left hxpow (u ^ (d - k)))
      (Nat.choose d k)

/-- Divisibility coming from the `u`-power. -/
theorem dvd_weightedBinomialTerm_of_dvd_u
    {q d k x u : ℕ}
    (h : q ∣ u) (hk : k < d) :
    q ∣ weightedBinomialTerm d k x u := by
  have hpow : q ∣ u ^ (d - k) := h.pow (Nat.sub_ne_zero_of_lt hk)
  unfold weightedBinomialTerm
  exact dvd_mul_of_dvd_right hpow (Nat.choose d k * x ^ k)

/--
Lift a row-level inner coefficient divisibility statement to the corresponding
weighted inner term.
-/
theorem allInnerChooseDivisible_dvd_inner_weightedBinomialTerm
    {m d k x u : ℕ}
    (h : AllInnerChooseDivisible d m) (hk0 : 0 < k) (hkd : k < d) :
    m ∣ weightedBinomialTerm d k x u :=
  dvd_weightedBinomialTerm_of_dvd_choose
    (allInnerChooseDivisible_dvd_choose h hk0 hkd)

/--
Coefficient-level inner divisibility lifts to the whole weighted inner row.
-/
theorem allInnerChooseDivisible_allInnerWeightedTermDivisible
    {m d x u : ℕ}
    (h : AllInnerChooseDivisible d m) :
    AllInnerWeightedTermDivisible d m x u := by
  intro k hk0 hkd
  exact allInnerChooseDivisible_dvd_inner_weightedBinomialTerm h hk0 hkd

/--
Unpack `AllInnerWeightedTermDivisible` at a concrete inner index.
-/
theorem allInnerWeightedTermDivisible_dvd_term
    {d m k x u : ℕ}
    (h : AllInnerWeightedTermDivisible d m x u) (hk0 : 0 < k) (hkd : k < d) :
    m ∣ weightedBinomialTerm d k x u :=
  h k hk0 hkd

/--
Unpack `AllWeightedTermDivisible` at a concrete index in the row.
-/
theorem allWeightedTermDivisible_dvd_term
    {d m k x u : ℕ}
    (h : AllWeightedTermDivisible d m x u) (hkd : k ≤ d) :
    m ∣ weightedBinomialTerm d k x u :=
  h k hkd

/-- In a prime row, every inner weighted term is divisible by that prime. -/
theorem prime_dvd_inner_weightedBinomialTerm
    {p k x u : ℕ}
    (hp : p.Prime) (hk0 : 0 < k) (hkp : k < p) :
    p ∣ weightedBinomialTerm p k x u :=
  dvd_weightedBinomialTerm_of_dvd_choose
    (prime_dvd_inner_choose hp hk0 hkp)

/-- Prime rows make all inner weighted terms divisible by the row prime. -/
theorem prime_allInnerWeightedTermDivisible
    {p x u : ℕ} (hp : p.Prime) :
    AllInnerWeightedTermDivisible p p x u :=
  allInnerChooseDivisible_allInnerWeightedTermDivisible
    (prime_allInnerChooseDivisible_self hp)

/-- Inner weighted terms inherit divisibility from `x`. -/
theorem dvd_inner_weightedBinomialTerm_of_dvd_x
    {q d k x u : ℕ}
    (h : q ∣ x) (hk0 : 0 < k) (_hkd : k < d) :
    q ∣ weightedBinomialTerm d k x u :=
  dvd_weightedBinomialTerm_of_dvd_x h hk0

/-- Inner weighted terms inherit divisibility from `u`. -/
theorem dvd_inner_weightedBinomialTerm_of_dvd_u
    {q d k x u : ℕ}
    (h : q ∣ u) (_hk0 : 0 < k) (hkd : k < d) :
    q ∣ weightedBinomialTerm d k x u :=
  dvd_weightedBinomialTerm_of_dvd_u h hkd

/-- The left boundary term is `u^d`. -/
theorem weightedBinomialTerm_left
    (d x u : ℕ) :
    weightedBinomialTerm d 0 x u = u ^ d := by
  simp [weightedBinomialTerm]

/-- The right boundary term is `x^d`. -/
theorem weightedBinomialTerm_right
    (d x u : ℕ) :
    weightedBinomialTerm d d x u = x ^ d := by
  simp [weightedBinomialTerm]

/-- Divisibility at the `u^d` boundary vertex. -/
theorem dvd_weightedBinomialTerm_left_of_dvd_u
    {q d x u : ℕ}
    (h : q ∣ u) (hd : 0 < d) :
    q ∣ weightedBinomialTerm d 0 x u := by
  simpa [weightedBinomialTerm_left] using h.pow hd.ne'

/-- Divisibility at the `x^d` boundary vertex. -/
theorem dvd_weightedBinomialTerm_right_of_dvd_x
    {q d x u : ℕ}
    (h : q ∣ x) (hd : 0 < d) :
    q ∣ weightedBinomialTerm d d x u := by
  simpa [weightedBinomialTerm_right] using h.pow hd.ne'

/--
If both boundary units carry `q`, then every term in a positive weighted row
carries `q`.
-/
theorem allWeightedTermDivisible_of_dvd_x_dvd_u
    {q d x u : ℕ}
    (hd : 0 < d) (hx : q ∣ x) (hu : q ∣ u) :
    AllWeightedTermDivisible d q x u := by
  intro k hkd
  by_cases hk0 : k = 0
  · subst hk0
    exact dvd_weightedBinomialTerm_left_of_dvd_u hu hd
  · by_cases hkd_eq : k = d
    · subst hkd_eq
      exact dvd_weightedBinomialTerm_right_of_dvd_x hx hd
    · have hk_pos : 0 < k := Nat.pos_of_ne_zero hk0
      have hk_lt : k < d := by omega
      exact dvd_inner_weightedBinomialTerm_of_dvd_x hx hk_pos hk_lt

/--
The full-row statement restricts to the inner-row statement.
-/
theorem allWeightedTermDivisible_allInnerWeightedTermDivisible
    {d m x u : ℕ}
    (h : AllWeightedTermDivisible d m x u) :
    AllInnerWeightedTermDivisible d m x u := by
  intro k hk0 hkd
  exact h k hkd.le

/--
If every weighted term in the row is divisible by `m`, then the row sum is
divisible by `m`.
-/
theorem dvd_weightedBinomialRowSum_of_allWeightedTermDivisible
    {d m x u : ℕ}
    (h : AllWeightedTermDivisible d m x u) :
    m ∣ weightedBinomialRowSum d x u := by
  unfold weightedBinomialRowSum
  refine Finset.dvd_sum ?_
  intro k hk
  exact h k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))

/--
If both boundary units carry `q`, then the whole positive weighted row sum
carries `q`.
-/
theorem dvd_weightedBinomialRowSum_of_dvd_x_dvd_u
    {q d x u : ℕ}
    (hd : 0 < d) (hx : q ∣ x) (hu : q ∣ u) :
    q ∣ weightedBinomialRowSum d x u :=
  dvd_weightedBinomialRowSum_of_allWeightedTermDivisible
    (allWeightedTermDivisible_of_dvd_x_dvd_u hd hx hu)

/--
The weighted row sum is the `r = 0` cosmic tail.
-/
theorem weightedBinomialRowSum_eq_GTail_zero
    (d x u : ℕ) :
    weightedBinomialRowSum d x u = GTail d 0 x u := by
  unfold weightedBinomialRowSum weightedBinomialTerm GTail
  apply Finset.sum_congr rfl
  intro k hk
  simp [mul_assoc]

/--
The weighted row sum is the ordinary binomial expansion `(x + u)^d`.

This is routed through the library kernel `GTail_zero_eq_add_pow`.
-/
theorem weightedBinomialRowSum_eq_add_pow
    (d x u : ℕ) :
    weightedBinomialRowSum d x u = (x + u) ^ d := by
  rw [weightedBinomialRowSum_eq_GTail_zero]
  exact GTail_zero_eq_add_pow d x u

/--
The full weighted row splits into the left boundary vertex `u^d` and the
positive weighted tail.
-/
theorem weightedBinomialRowSum_eq_left_add_positiveTail
    (d x u : ℕ) :
    weightedBinomialRowSum d x u =
      u ^ d + weightedBinomialPositiveTailSum d x u := by
  unfold weightedBinomialRowSum weightedBinomialPositiveTailSum
  rw [Finset.sum_range_succ']
  simp [weightedBinomialTerm_left, add_comm]

/--
The positive weighted tail is `x * GTail d 1 x u`.

This is the `r = 1` bridge from the weighted Pascal row to the cosmic tail
kernel.
-/
theorem weightedBinomialPositiveTailSum_eq_x_mul_GTail_one
    (d x u : ℕ) :
    weightedBinomialPositiveTailSum d x u = x * GTail d 1 x u := by
  unfold weightedBinomialPositiveTailSum weightedBinomialTerm GTail
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hidx : k + 1 = 1 + k := by omega
  rw [← hidx, pow_succ']
  simp [mul_assoc, mul_left_comm, mul_comm]

/--
The positive weighted tail is divisible by `x`.
-/
theorem x_dvd_weightedBinomialPositiveTailSum
    (d x u : ℕ) :
    x ∣ weightedBinomialPositiveTailSum d x u := by
  rw [weightedBinomialPositiveTailSum_eq_x_mul_GTail_one]
  exact dvd_mul_right x (GTail d 1 x u)

/--
The binomial body splits into the left boundary vertex and the positive tail.
-/
theorem add_pow_eq_left_add_positiveTail
    (d x u : ℕ) :
    (x + u) ^ d =
      u ^ d + weightedBinomialPositiveTailSum d x u := by
  rw [← weightedBinomialRowSum_eq_add_pow]
  exact weightedBinomialRowSum_eq_left_add_positiveTail d x u

/--
The binomial body splits into the left boundary vertex and the normalized
`r = 1` cosmic tail.
-/
theorem add_pow_eq_left_add_x_mul_GTail_one
    (d x u : ℕ) :
    (x + u) ^ d = u ^ d + x * GTail d 1 x u := by
  rw [add_pow_eq_left_add_positiveTail,
    weightedBinomialPositiveTailSum_eq_x_mul_GTail_one]

/--
Subtracting the left boundary vertex leaves exactly the positive weighted
tail.
-/
theorem add_pow_sub_left_eq_positiveTail
    (d x u : ℕ) :
    (x + u) ^ d - u ^ d =
      weightedBinomialPositiveTailSum d x u :=
  Nat.sub_eq_of_eq_add
    (by simpa [add_comm] using add_pow_eq_left_add_positiveTail d x u)

/--
Subtracting the left boundary vertex leaves `x * GTail d 1 x u`.
-/
theorem add_pow_sub_left_eq_x_mul_GTail_one
    (d x u : ℕ) :
    (x + u) ^ d - u ^ d = x * GTail d 1 x u := by
  rw [add_pow_sub_left_eq_positiveTail,
    weightedBinomialPositiveTailSum_eq_x_mul_GTail_one]

/--
The left-boundary difference is divisible by the gap `x`.
-/
theorem x_dvd_add_pow_sub_left
    (d x u : ℕ) :
    x ∣ (x + u) ^ d - u ^ d := by
  rw [add_pow_sub_left_eq_x_mul_GTail_one]
  exact dvd_mul_right x (GTail d 1 x u)

/--
The weighted binomial row as a `BodyGapKernelSplit`.

This packages `(x + u)^d = u^d + x * GTail d 1 x u` as the common
`Big = Boundary + GapAxis * Kernel` interface.
-/
def weightedBodyGapKernelSplit
    (d x u : ℕ) : BodyGapKernelSplit ℕ where
  big := (x + u) ^ d
  boundary := u ^ d
  gapAxis := x
  kernel := GTail d 1 x u
  split := add_pow_eq_left_add_x_mul_GTail_one d x u

/-- The weighted split tail is the left-boundary difference. -/
theorem weightedBodyGapKernelSplit_tail_eq_sub
    (d x u : ℕ) :
    (weightedBodyGapKernelSplit d x u).tail =
      (x + u) ^ d - u ^ d := by
  symm
  exact BodyGapKernelSplit.big_sub_boundary_eq_tail_nat
    (weightedBodyGapKernelSplit d x u)

/-- The weighted split tail is divisible by the gap axis `x`. -/
theorem weightedBodyGapKernelSplit_gapAxis_dvd_tail
    (d x u : ℕ) :
    (weightedBodyGapKernelSplit d x u).gapAxis ∣
      (weightedBodyGapKernelSplit d x u).tail :=
  BodyGapKernelSplit.gapAxis_dvd_tail_nat
    (weightedBodyGapKernelSplit d x u)

/--
The weighted split recovers the existing divisibility statement
`x ∣ (x + u)^d - u^d`.
-/
theorem weightedBodyGapKernelSplit_gapAxis_dvd_sub
    (d x u : ℕ) :
    (weightedBodyGapKernelSplit d x u).gapAxis ∣
      (x + u) ^ d - u ^ d := by
  rw [← weightedBodyGapKernelSplit_tail_eq_sub]
  exact weightedBodyGapKernelSplit_gapAxis_dvd_tail d x u

end NumberTheory
end DkMath
