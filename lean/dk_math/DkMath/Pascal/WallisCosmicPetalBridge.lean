/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import DkMath.Petal.Factorial

#print "file: DkMath.Pascal.WallisCosmicPetalBridge"

/-!
# Finite Wallis-Cosmic Petal bridge

This module packages the first finite, algebraic layer of the
Wallis-Cosmic Petal bridge over `ℚ`.  It deliberately avoids limits,
`π`, asymptotics, and Stirling estimates.
-/

namespace DkMath.Pascal.WallisCosmicPetalBridge

open Finset
open DkMath.Petal

/-- Left odd factor `2*k + 1`, viewed in `ℚ`. -/
def oddLeftQ (k : ℕ) : ℚ :=
  (2 * k + 1 : ℚ)

/-- Central even factor `2*k + 2`, viewed in `ℚ`. -/
def evenCenterQ (k : ℕ) : ℚ :=
  (2 * k + 2 : ℚ)

/-- Right odd factor `2*k + 3`, viewed in `ℚ`. -/
def oddRightQ (k : ℕ) : ℚ :=
  (2 * k + 3 : ℚ)

/-- The finite cosmic body `N_k = (2*k + 1) * (2*k + 3)`. -/
def cosmicBodyQ (k : ℕ) : ℚ :=
  oddLeftQ k * oddRightQ k

/-- The `k`th Wallis factor. -/
def wallisFactorQ (k : ℕ) : ℚ :=
  evenCenterQ k ^ 2 / (oddLeftQ k * oddRightQ k)

/-- The `k`th cosmic gap factor `(N_k + 1) / N_k`. -/
def cosmicFactorQ (k : ℕ) : ℚ :=
  (cosmicBodyQ k + 1) / cosmicBodyQ k

/-- The left odd factor is positive. -/
theorem oddLeftQ_pos (k : ℕ) : 0 < oddLeftQ k := by
  unfold oddLeftQ
  positivity

/-- The central even factor is positive. -/
theorem evenCenterQ_pos (k : ℕ) : 0 < evenCenterQ k := by
  unfold evenCenterQ
  positivity

/-- The right odd factor is positive. -/
theorem oddRightQ_pos (k : ℕ) : 0 < oddRightQ k := by
  unfold oddRightQ
  positivity

/-- The cosmic body is positive. -/
theorem cosmicBodyQ_pos (k : ℕ) : 0 < cosmicBodyQ k := by
  unfold cosmicBodyQ
  exact mul_pos (oddLeftQ_pos k) (oddRightQ_pos k)

/-- The left odd factor is nonzero. -/
theorem oddLeftQ_ne_zero (k : ℕ) : oddLeftQ k ≠ 0 :=
  (oddLeftQ_pos k).ne'

/-- The central even factor is nonzero. -/
theorem evenCenterQ_ne_zero (k : ℕ) : evenCenterQ k ≠ 0 :=
  (evenCenterQ_pos k).ne'

/-- The right odd factor is nonzero. -/
theorem oddRightQ_ne_zero (k : ℕ) : oddRightQ k ≠ 0 :=
  (oddRightQ_pos k).ne'

/-- The cosmic body is nonzero. -/
theorem cosmicBodyQ_ne_zero (k : ℕ) : cosmicBodyQ k ≠ 0 :=
  (cosmicBodyQ_pos k).ne'

/-- Local odd-square bridge: `(2*k + 2)^2 = (2*k + 1)*(2*k + 3) + 1`. -/
theorem cosmic_square_odd_bridge_Q (k : ℕ) :
    evenCenterQ k ^ 2 = oddLeftQ k * oddRightQ k + 1 := by
  unfold evenCenterQ oddLeftQ oddRightQ
  ring_nf

/-- Each Wallis factor is the corresponding cosmic gap factor. -/
theorem wallisFactorQ_eq_cosmicFactorQ (k : ℕ) :
    wallisFactorQ k = cosmicFactorQ k := by
  unfold wallisFactorQ cosmicFactorQ cosmicBodyQ
  rw [cosmic_square_odd_bridge_Q]

/-- The cosmic factor is the gap ratio `1 + 1/N_k`. -/
theorem cosmicFactorQ_eq_one_add_inv_body (k : ℕ) :
    cosmicFactorQ k = 1 + 1 / cosmicBodyQ k := by
  unfold cosmicFactorQ
  field_simp [cosmicBodyQ_ne_zero k]

/-- The Wallis factor is the cosmic gap ratio `1 + 1/N_k`. -/
theorem wallisFactorQ_eq_one_add_inv_body (k : ℕ) :
    wallisFactorQ k = 1 + 1 / cosmicBodyQ k := by
  rw [wallisFactorQ_eq_cosmicFactorQ, cosmicFactorQ_eq_one_add_inv_body]

/-- The Wallis factor is positive. -/
theorem wallisFactorQ_pos (k : ℕ) : 0 < wallisFactorQ k := by
  rw [wallisFactorQ_eq_one_add_inv_body]
  exact add_pos zero_lt_one (one_div_pos.mpr (cosmicBodyQ_pos k))

/-- The cosmic factor is positive. -/
theorem cosmicFactorQ_pos (k : ℕ) : 0 < cosmicFactorQ k := by
  rw [cosmicFactorQ_eq_one_add_inv_body]
  exact add_pos zero_lt_one (one_div_pos.mpr (cosmicBodyQ_pos k))

/-- Each Wallis factor is strictly larger than `1`. -/
theorem one_lt_wallisFactorQ (k : ℕ) :
    1 < wallisFactorQ k := by
  rw [wallisFactorQ_eq_one_add_inv_body]
  have hgap : 0 < 1 / cosmicBodyQ k := by
    exact one_div_pos.mpr (cosmicBodyQ_pos k)
  linarith

/-- Each cosmic factor is strictly larger than `1`. -/
theorem one_lt_cosmicFactorQ (k : ℕ) :
    1 < cosmicFactorQ k := by
  rw [cosmicFactorQ_eq_one_add_inv_body]
  have hgap : 0 < 1 / cosmicBodyQ k := by
    exact one_div_pos.mpr (cosmicBodyQ_pos k)
  linarith

/-- The finite Wallis partial product. -/
def wallisPartialQ (m : ℕ) : ℚ :=
  ∏ k ∈ Finset.range m, wallisFactorQ k

/-- The finite cosmic gap partial product. -/
def cosmicPartialQ (m : ℕ) : ℚ :=
  ∏ k ∈ Finset.range m, cosmicFactorQ k

/-- The finite Wallis partial product equals the finite cosmic gap product. -/
theorem wallisPartialQ_eq_cosmicPartialQ (m : ℕ) :
    wallisPartialQ m = cosmicPartialQ m := by
  unfold wallisPartialQ cosmicPartialQ
  exact Finset.prod_congr rfl fun k _ => wallisFactorQ_eq_cosmicFactorQ k

/-- The finite Wallis partial product is positive. -/
theorem wallisPartialQ_pos (m : ℕ) :
    0 < wallisPartialQ m := by
  unfold wallisPartialQ
  exact Finset.prod_pos fun k _ => wallisFactorQ_pos k

/-- The finite cosmic partial product is positive. -/
theorem cosmicPartialQ_pos (m : ℕ) :
    0 < cosmicPartialQ m := by
  unfold cosmicPartialQ
  exact Finset.prod_pos fun k _ => cosmicFactorQ_pos k

/-- The finite Wallis partial product is at least `1`. -/
theorem one_le_wallisPartialQ (m : ℕ) :
    1 ≤ wallisPartialQ m := by
  induction m with
  | zero =>
      simp [wallisPartialQ]
  | succ m ih =>
      rw [wallisPartialQ, Finset.prod_range_succ]
      rw [← wallisPartialQ]
      simpa using mul_le_mul ih (le_of_lt (one_lt_wallisFactorQ m))
        zero_le_one (le_of_lt (wallisPartialQ_pos m))

/-- The finite cosmic partial product is at least `1`. -/
theorem one_le_cosmicPartialQ (m : ℕ) :
    1 ≤ cosmicPartialQ m := by
  induction m with
  | zero =>
      simp [cosmicPartialQ]
  | succ m ih =>
      rw [cosmicPartialQ, Finset.prod_range_succ]
      rw [← cosmicPartialQ]
      simpa using mul_le_mul ih (le_of_lt (one_lt_cosmicFactorQ m))
        zero_le_one (le_of_lt (cosmicPartialQ_pos m))

/-- The finite Wallis partial products are monotone in the truncation length. -/
theorem wallisPartialQ_mono : Monotone wallisPartialQ := by
  refine monotone_nat_of_le_succ fun m => ?_
  unfold wallisPartialQ
  rw [Finset.prod_range_succ]
  calc
    (∏ k ∈ Finset.range m, wallisFactorQ k) =
        (∏ k ∈ Finset.range m, wallisFactorQ k) * 1 := by ring
    _ ≤ (∏ k ∈ Finset.range m, wallisFactorQ k) * wallisFactorQ m :=
      mul_le_mul_of_nonneg_left (le_of_lt (one_lt_wallisFactorQ m))
        (le_of_lt (wallisPartialQ_pos m))

/-- The finite cosmic partial products are monotone in the truncation length. -/
theorem cosmicPartialQ_mono : Monotone cosmicPartialQ := by
  refine monotone_nat_of_le_succ fun m => ?_
  unfold cosmicPartialQ
  rw [Finset.prod_range_succ]
  calc
    (∏ k ∈ Finset.range m, cosmicFactorQ k) =
        (∏ k ∈ Finset.range m, cosmicFactorQ k) * 1 := by ring
    _ ≤ (∏ k ∈ Finset.range m, cosmicFactorQ k) * cosmicFactorQ m :=
      mul_le_mul_of_nonneg_left (le_of_lt (one_lt_cosmicFactorQ m))
        (le_of_lt (cosmicPartialQ_pos m))

/-- The central odd half-product. -/
def centralOddRatioPartialQ (m : ℕ) : ℚ :=
  ∏ k ∈ Finset.range m, evenCenterQ k / oddLeftQ k

/-- The mirror odd half-product. -/
def mirrorOddRatioPartialQ (m : ℕ) : ℚ :=
  ∏ k ∈ Finset.range m, evenCenterQ k / oddRightQ k

/-- The legacy choose-based central ratio, retained as a compatibility entry. -/
def centralRatioQ (m : ℕ) : ℚ :=
  (2 ^ (2 * m) : ℚ) / (Nat.choose (2 * m) m : ℚ)

/-- The central ratio built from the canonical Petal factorial. -/
def petalCentralRatioQ (m : ℕ) : ℚ :=
  ((2 : ℚ) ^ (2 * m) * (factorialPetal m : ℚ) ^ 2) /
    (factorialPetal (2 * m) : ℚ)

/-- The central odd half-product is positive. -/
theorem centralOddRatioPartialQ_pos (m : ℕ) :
    0 < centralOddRatioPartialQ m := by
  unfold centralOddRatioPartialQ
  exact Finset.prod_pos fun k _ => div_pos (evenCenterQ_pos k) (oddLeftQ_pos k)

/-- The mirror odd half-product is positive. -/
theorem mirrorOddRatioPartialQ_pos (m : ℕ) :
    0 < mirrorOddRatioPartialQ m := by
  unfold mirrorOddRatioPartialQ
  exact Finset.prod_pos fun k _ => div_pos (evenCenterQ_pos k) (oddRightQ_pos k)

theorem centralRatioQ_eq_petalCentralRatioQ (m : ℕ) :
    centralRatioQ m = petalCentralRatioQ m := by
  unfold centralRatioQ petalCentralRatioQ
  have hm : m ≤ 2 * m := by omega
  have hchoose : (Nat.choose (2 * m) m : ℚ) =
      (Nat.factorial (2 * m) : ℚ) /
        ((Nat.factorial m : ℚ) * (Nat.factorial m : ℚ)) := by
    rw [Nat.choose_eq_factorial_div_factorial hm]
    rw [Nat.cast_div_charZero]
    · have hsub : 2 * m - m = m := by omega
      rw [hsub]
      simp
    · simpa using Nat.factorial_mul_factorial_dvd_factorial hm
  rw [hchoose]
  rw [← factorialPetal_eq_factorial m, ← factorialPetal_eq_factorial (2 * m)]
  field_simp

/-- The legacy central ratio is positive via the Petal central ratio. -/
theorem centralRatioQ_pos (m : ℕ) :
    0 < centralRatioQ m := by
  rw [centralRatioQ_eq_petalCentralRatioQ]
  unfold petalCentralRatioQ
  have hm_pos : (0 : ℚ) < factorialPetal m := by
    exact_mod_cast factorialPetal_pos m
  have h2m_pos : (0 : ℚ) < factorialPetal (2 * m) := by
    exact_mod_cast factorialPetal_pos (2 * m)
  exact div_pos
    (mul_pos (pow_pos (by norm_num : (0 : ℚ) < 2) _) (sq_pos_of_pos hm_pos))
    h2m_pos

/-- The Petal factorial central ratio equals the central odd half-product.

The induction stays on the Petal successor API throughout. -/
theorem petalCentralRatioQ_eq_centralOddRatioPartialQ (m : ℕ) :
    petalCentralRatioQ m = centralOddRatioPartialQ m := by
  induction m with
  | zero =>
      simp [petalCentralRatioQ, centralOddRatioPartialQ]
  | succ m ih =>
      rw [centralOddRatioPartialQ, Finset.prod_range_succ]
      rw [← centralOddRatioPartialQ, ← ih]
      unfold petalCentralRatioQ evenCenterQ oddLeftQ
      rw [factorialPetal_succ m]
      rw [show 2 * (m + 1) = (2 * m + 1) + 1 by omega]
      rw [factorialPetal_succ (2 * m + 1)]
      rw [factorialPetal_succ (2 * m)]
      have hm_ne : (factorialPetal m : ℚ) ≠ 0 := by
        exact_mod_cast (factorialPetal_pos m).ne'
      have h2m_ne : (factorialPetal (2 * m) : ℚ) ≠ 0 := by
        exact_mod_cast (factorialPetal_pos (2 * m)).ne'
      field_simp [hm_ne, h2m_ne]
      norm_num
      ring_nf

/-- The central binomial ratio equals the central odd half-product. -/
theorem centralRatioQ_eq_centralOddRatioPartialQ (m : ℕ) :
    centralRatioQ m = centralOddRatioPartialQ m := by
  rw [centralRatioQ_eq_petalCentralRatioQ,
    petalCentralRatioQ_eq_centralOddRatioPartialQ]

private theorem halfFactor_mul_eq_wallisFactorQ (k : ℕ) :
    evenCenterQ k / oddLeftQ k * (evenCenterQ k / oddRightQ k) =
      wallisFactorQ k := by
  unfold wallisFactorQ evenCenterQ oddLeftQ oddRightQ
  field_simp

/-- The two half-products multiply to the finite Wallis partial product. -/
theorem centralOdd_mul_mirror_eq_wallisPartialQ (m : ℕ) :
    centralOddRatioPartialQ m * mirrorOddRatioPartialQ m = wallisPartialQ m := by
  unfold centralOddRatioPartialQ mirrorOddRatioPartialQ wallisPartialQ
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun k _ => halfFactor_mul_eq_wallisFactorQ k

/-- The Petal factorial central ratio times the mirror product equals Wallis. -/
theorem petalCentralRatioQ_mul_mirror_eq_wallisPartialQ (m : ℕ) :
    petalCentralRatioQ m * mirrorOddRatioPartialQ m = wallisPartialQ m := by
  rw [petalCentralRatioQ_eq_centralOddRatioPartialQ,
    centralOdd_mul_mirror_eq_wallisPartialQ]

/-- The central binomial ratio times the mirror product equals the finite Wallis product. -/
theorem centralRatioQ_mul_mirror_eq_wallisPartialQ (m : ℕ) :
    centralRatioQ m * mirrorOddRatioPartialQ m = wallisPartialQ m := by
  rw [centralRatioQ_eq_petalCentralRatioQ,
    petalCentralRatioQ_mul_mirror_eq_wallisPartialQ]

/--
The proof-note central-ratio expression is the ordered finite product of the
Wallis factors.

This is intentionally a finite theorem: `centralRatioQ m * mirrorOddRatioPartialQ m`
is a partial-product expression, not a per-factor sequence.
-/
theorem centralRatioQ_mul_mirror_eq_prod_wallisFactorQ (m : ℕ) :
    centralRatioQ m * mirrorOddRatioPartialQ m =
      ∏ k ∈ Finset.range m, wallisFactorQ k := by
  rw [centralRatioQ_mul_mirror_eq_wallisPartialQ]
  rfl

/--
The finite Wallis-Cosmic Petal bridge:
the central odd half-product times its mirror equals the cosmic gap product.
-/
theorem centralOdd_mul_mirror_eq_cosmicPartialQ (m : ℕ) :
    centralOddRatioPartialQ m * mirrorOddRatioPartialQ m = cosmicPartialQ m := by
  rw [centralOdd_mul_mirror_eq_wallisPartialQ, wallisPartialQ_eq_cosmicPartialQ]

/-- The Petal factorial central ratio times the mirror product equals Cosmic. -/
theorem petalCentralRatioQ_mul_mirror_eq_cosmicPartialQ (m : ℕ) :
    petalCentralRatioQ m * mirrorOddRatioPartialQ m = cosmicPartialQ m := by
  rw [petalCentralRatioQ_mul_mirror_eq_wallisPartialQ,
    wallisPartialQ_eq_cosmicPartialQ]

/--
The proof-note form of the finite Wallis-Cosmic Petal bridge:
the central binomial ratio times the mirror product equals the cosmic gap product.
-/
theorem centralRatioQ_mul_mirror_eq_cosmicPartialQ (m : ℕ) :
    centralRatioQ m * mirrorOddRatioPartialQ m = cosmicPartialQ m := by
  rw [centralRatioQ_eq_petalCentralRatioQ,
    petalCentralRatioQ_mul_mirror_eq_cosmicPartialQ]

/--
The proof-note central-ratio expression is the ordered finite product of the
cosmic gap factors.

As with `centralRatioQ_mul_mirror_eq_prod_wallisFactorQ`, this stays in the
finite algebraic module because it does not assert an infinite product.
-/
theorem centralRatioQ_mul_mirror_eq_prod_cosmicFactorQ (m : ℕ) :
    centralRatioQ m * mirrorOddRatioPartialQ m =
      ∏ k ∈ Finset.range m, cosmicFactorQ k := by
  rw [centralRatioQ_mul_mirror_eq_cosmicPartialQ]
  rfl

end DkMath.Pascal.WallisCosmicPetalBridge
