/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.Cosmic.GTailSevenArithmetic
import DkMath.Lib.NumberTheory.PadicValNat

#print "file: DkMath.Lib.Cosmic.GTailSevenValuation"

/-!
# Neutral exact seven-adic layer

An endpoint unit suffices; no Fermat equation or full coordinate coprimality
is assumed. The excluded second layer also excludes a zero residual.
-/

namespace DkMath.CosmicFormula

/-- The endpoint-unit residual has valuation one, even when the gap is zero. -/
theorem padicValNat_gtail_seven_eq_one {g c : ℕ}
    (hgap : 7 ∣ g) (hend : ¬ 7 ∣ c) :
    padicValNat 7 (GTail 7 1 g c) = 1 := by
  have hp : Nat.Prime 7 := by decide
  have hlayer := gtail_seven_exact_seven_layer hgap hend
  have htail : GTail 7 1 g c ≠ 0 := by
    intro hzero
    exact hlayer.2 (hzero ▸ dvd_zero _)
  have hge := (DkMath.Lib.NumberTheory.Vp_ge_one_iff hp htail).mpr hlayer.1
  have hlt : ¬ 2 ≤ padicValNat 7 (GTail 7 1 g c) := by
    intro htwo
    exact hlayer.2
      ((DkMath.Lib.NumberTheory.padicValNat_le_iff_dvd hp htail 2).mp htwo)
  omega

/-- A nonzero gap contributes its valuation plus the single residual layer. -/
theorem padicValNat_gap_mul_gtail_seven {g c : ℕ}
    (hg : g ≠ 0) (hgap : 7 ∣ g) (hend : ¬ 7 ∣ c) :
    padicValNat 7 (g * GTail 7 1 g c) = padicValNat 7 g + 1 := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  have htail : GTail 7 1 g c ≠ 0 := by
    intro hzero
    exact (gtail_seven_exact_seven_layer hgap hend).2 (hzero ▸ dvd_zero _)
  rw [padicValNat.mul hg htail, padicValNat_gtail_seven_eq_one hgap hend]

end DkMath.CosmicFormula
