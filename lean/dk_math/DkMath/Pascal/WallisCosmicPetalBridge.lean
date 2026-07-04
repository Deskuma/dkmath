/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib

#print "file: DkMath.Pascal.WallisCosmicPetalBridge"

/-!
# Finite Wallis-Cosmic Petal bridge

This module packages the first finite, algebraic layer of the
Wallis-Cosmic Petal bridge over `ℚ`.  It deliberately avoids limits,
`π`, asymptotics, and Stirling estimates.
-/

namespace DkMath.Pascal.WallisCosmicPetalBridge

open Finset

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

/-- The central odd half-product. -/
def centralOddRatioPartialQ (m : ℕ) : ℚ :=
  ∏ k ∈ Finset.range m, evenCenterQ k / oddLeftQ k

/-- The mirror odd half-product. -/
def mirrorOddRatioPartialQ (m : ℕ) : ℚ :=
  ∏ k ∈ Finset.range m, evenCenterQ k / oddRightQ k

/-- The central binomial ratio `2^(2*m) / Nat.choose (2*m) m`, viewed in `ℚ`. -/
def centralRatioQ (m : ℕ) : ℚ :=
  (2 ^ (2 * m) : ℚ) / (Nat.choose (2 * m) m : ℚ)

private def centralRatioFactorialQ (m : ℕ) : ℚ :=
  ((2 : ℚ) ^ (2 * m) * (Nat.factorial m : ℚ) ^ 2) /
    (Nat.factorial (2 * m) : ℚ)

private theorem centralRatioQ_eq_factorialQ (m : ℕ) :
    centralRatioQ m = centralRatioFactorialQ m := by
  unfold centralRatioQ centralRatioFactorialQ
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
  field_simp

private theorem factorial_two_mul_succ_cast_Q (m : ℕ) :
    ((Nat.factorial (2 * (m + 1)) : ℕ) : ℚ) =
      (2 * m + 2 : ℚ) * ((2 * m + 1 : ℚ) *
        (Nat.factorial (2 * m) : ℚ)) := by
  rw [show 2 * (m + 1) = (2 * m + 1) + 1 by omega]
  rw [Nat.factorial_succ]
  rw [show 2 * m + 1 = (2 * m) + 1 by omega]
  rw [Nat.factorial_succ]
  norm_num
  left
  ring

private theorem centralRatioFactorialQ_eq_centralOddRatioPartialQ (m : ℕ) :
    centralRatioFactorialQ m = centralOddRatioPartialQ m := by
  induction m with
  | zero =>
      simp [centralRatioFactorialQ, centralOddRatioPartialQ]
  | succ m ih =>
      rw [centralOddRatioPartialQ, Finset.prod_range_succ]
      rw [← centralOddRatioPartialQ, ← ih]
      unfold centralRatioFactorialQ evenCenterQ oddLeftQ
      have hm_factorial : ((Nat.factorial (m + 1) : ℕ) : ℚ) =
          (m + 1 : ℚ) * (Nat.factorial m : ℚ) := by
        rw [Nat.factorial_succ]
        norm_num
      rw [hm_factorial, factorial_two_mul_succ_cast_Q]
      field_simp
      ring_nf

/-- The central binomial ratio equals the central odd half-product. -/
theorem centralRatioQ_eq_centralOddRatioPartialQ (m : ℕ) :
    centralRatioQ m = centralOddRatioPartialQ m := by
  rw [centralRatioQ_eq_factorialQ, centralRatioFactorialQ_eq_centralOddRatioPartialQ]

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

/--
The finite Wallis-Cosmic Petal bridge:
the central odd half-product times its mirror equals the cosmic gap product.
-/
theorem centralOdd_mul_mirror_eq_cosmicPartialQ (m : ℕ) :
    centralOddRatioPartialQ m * mirrorOddRatioPartialQ m = cosmicPartialQ m := by
  rw [centralOdd_mul_mirror_eq_wallisPartialQ, wallisPartialQ_eq_cosmicPartialQ]

/--
The proof-note form of the finite Wallis-Cosmic Petal bridge:
the central binomial ratio times the mirror product equals the cosmic gap product.
-/
theorem centralRatioQ_mul_mirror_eq_cosmicPartialQ (m : ℕ) :
    centralRatioQ m * mirrorOddRatioPartialQ m = cosmicPartialQ m := by
  rw [centralRatioQ_eq_centralOddRatioPartialQ,
    centralOdd_mul_mirror_eq_cosmicPartialQ]

end DkMath.Pascal.WallisCosmicPetalBridge
