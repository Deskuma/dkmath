/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib
import DkMath.CosmicFormula.CosmicFormulaBinom

#print "file: DkMath.CosmicFormula.CoreBeamGap"

set_option linter.style.longLine false

/-! ## Core・Beam・Gap 構造の明示化

本ファイルでは、二項定理 `(x+u)^d = x^d + ⋮ + u^d` を
三層構造として分解する表現を提供します：

$$
\text{Big} \, d \, x \, u = \text{Core} \, d \, x + \text{Beam} \, d \, x \, u + \text{Gap} \, d \, u
$$

ここで：
- `Core d x := x^d` は左端の純冪
- `Gap d u := u^d` は右端の純冪
- `Beam d x u` は両端純冪を除いた中間項の総和

既存の `BigN`, `BodyN`, `GapN`, `GN` とは橋渡し補題で関係を明示します。

-/

namespace DkMath.CosmicFormula.CoreBeamGap

open scoped BigOperators
open DkMath.CosmicFormulaBinom

variable {R : Type*} [CommSemiring R]

-- ============================================================================
-- Definition: Core, Beam, Gap
-- ============================================================================

/-- Left endpoint power: Core -/
def Core (d : ℕ) (x : R) : R := x ^ d

/-- Right endpoint power: Gap -/
def Gap (d : ℕ) (u : R) : R := u ^ d

/-- Middle interaction term: Beam, the sum of all non-endpoint binomial terms. -/
def Beam (d : ℕ) (x u : R) : R :=
  match d with
  | 0 => 0
  | n + 1 =>
      ∑ k ∈ Finset.range n, (Nat.choose (n + 1) (k + 1) : R) * x ^ (k + 1) * u ^ (n - k)

/-- Full structure: Big (identical to BigN) -/
def Big (d : ℕ) (x u : R) : R := BigN d x u

-- ============================================================================
-- Correspondence with existing definitions
-- ============================================================================

/-- Big equals BigN by definition -/
@[simp]
lemma big_eq_BigN (d : ℕ) (x u : R) :
    Big d x u = BigN d x u := rfl

/-- Gap equals GapN by definition -/
@[simp]
lemma gap_eq_GapN (d : ℕ) (u : R) :
    Gap d u = GapN d u := rfl

/-- For positive degree, `BodyN` splits as the left endpoint power plus the middle Beam. -/
theorem body_eq_core_add_beam {d : ℕ} (hd : 0 < d) (x u : R) :
    BodyN d x u = Core d x + Beam d x u := by
  cases d with
  | zero =>
      cases Nat.lt_asymm hd hd
  | succ n =>
      unfold BodyN Core Beam
      rw [GN_eq_sum]
      simp only
      rw [Finset.mul_sum, Finset.sum_range_succ]
      have hsum :
          ∑ k ∈ Finset.range n, x * ((Nat.choose (n + 1) (k + 1) : R) * x ^ k * u ^ (n + 1 - 1 - k)) =
            ∑ k ∈ Finset.range n, (Nat.choose (n + 1) (k + 1) : R) * x ^ (k + 1) * u ^ (n - k) := by
        apply Finset.sum_congr rfl
        intro k hk
        have hk' : k < n := Finset.mem_range.mp hk
        have hsub : n + 1 - 1 - k = n - k := by
          omega
        rw [hsub]
        ring
      rw [hsum]
      simp [pow_succ', add_comm]

-- ============================================================================
-- Main decomposition theorems
-- ============================================================================

/-- Central theorem: Big = Core + Beam + Gap
This is the fundamental decomposition of the binomial expansion
into three layers: left endpoint, middle interaction, and right endpoint. -/
theorem big_eq_body_add_gap (d : ℕ) (x u : R) :
    Big d x u = BodyN d x u + Gap d u := by
  simp only [Big, BigN, Gap]
  exact cosmic_id_csr d x u

/-- Central theorem for positive degree: Big = Core + Beam + Gap
This is the fundamental decomposition of the binomial expansion
into three layers: left endpoint, middle interaction, and right endpoint. -/
theorem big_eq_core_beam_gap {d : ℕ} (hd : 0 < d) (x u : R) :
    Big d x u = Core d x + Beam d x u + Gap d u := by
  rw [big_eq_body_add_gap, body_eq_core_add_beam hd]

-- ============================================================================
-- Inequality lemmas (Natural numbers)
-- ============================================================================

/-- On Nat: if d ≥ 2 and x, u > 0, then Body > Core -/
theorem body_gt_core_nat (d x u : ℕ)
    (hd : 2 ≤ d) (hx : 0 < x) (hu : 0 < u) :
    Core d x < BodyN d x u := by
  simp only [Core, BodyN]
  exact xpow_lt_bodyN_nat_of_two_le hd hx hu

end DkMath.CosmicFormula.CoreBeamGap
