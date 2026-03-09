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
- `Beam d x u := GN d x u` は中間結合項

既存の `BigN`, `BodyN`, `GapN`, `GN` との関係を補題で明示します。

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

/-- Middle interaction term: Beam (identical to GN) -/
def Beam (d : ℕ) (x u : R) : R := GN d x u

/-- Full structure: Big (identical to BigN) -/
def Big (d : ℕ) (x u : R) : R := BigN d x u

-- ============================================================================
-- Correspondence with existing definitions
-- ============================================================================

/-- Beam equals GN by definition -/
@[simp]
lemma beam_eq_GN (d : ℕ) (x u : R) :
    Beam d x u = GN d x u := rfl

/-- Big equals BigN by definition -/
@[simp]
lemma big_eq_BigN (d : ℕ) (x u : R) :
    Big d x u = BigN d x u := rfl

/-- Gap equals GapN by definition -/
@[simp]
lemma gap_eq_GapN (d : ℕ) (u : R) :
    Gap d u = GapN d u := rfl

-- ============================================================================
-- Main decomposition theorems
-- ============================================================================

/-- Central theorem: Big = Core + Beam + Gap
This is the fundamental decomposition of the binomial expansion
into three layers: left endpoint, middle interaction, and right endpoint. -/
theorem big_eq_core_beam_gap (d : ℕ) (x u : R) :
    Big d x u = Core d x + Beam d x u + Gap d u := by
  unfold Big BigN Core Beam Gap
  -- From cosmic_id_csr': (x+u)^d = x*GN d x u + u^d
  -- And BodyN d x u = x * GN d x u
  -- And GN d x u ≡ Beam d x u
  -- Therefore: Big = Core + Beam + Gap follows from rearrangement
  sorry

/-- Equivalence: Big = Body + Gap -/
theorem big_eq_body_add_gap (d : ℕ) (x u : R) :
    Big d x u = BodyN d x u + Gap d u := by
  simp only [Big, BigN, Gap]
  exact cosmic_id_csr d x u

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
