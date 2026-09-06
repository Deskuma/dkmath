/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.ABC.GNWieferichAccumulation
import DkMath.NumberTheory.GNThreeOrientation

#print "file: DkMath.ABC.GNCubicOrientation"

/-!
# Cubic repeated-support separation

Transport of elementary orientation arithmetic to the actual Wieferich sets
and repeated moduli. No counting or ABC contract is assumed.
-/

namespace DkMath.ABC

open DkMath.CosmicFormulaBinom
open DkMath.NumberTheory

/-- The actual non-exceptional Wieferich sets are disjoint; positivity is unnecessary. -/
theorem GNNonExceptionalWieferichPrimeSet_three_disjoint_swap {a b : ℕ} (hc : Nat.Coprime a b) :
    Disjoint (GNNonExceptionalWieferichPrimeSet 3 a b)
      (GNNonExceptionalWieferichPrimeSet 3 b a) := by
  classical
  apply Finset.disjoint_left.mpr
  intro q hf hg
  have hF := (Finset.mem_filter.mp hf).2
  have hG := (Finset.mem_filter.mp hg).2
  exact not_prime_sq_dvd_both_GN_three hc hF.1 ⟨hF.2.2.2,hG.2.2.2⟩

/-- For positive coprime coordinates, the two actual repeated moduli are coprime. -/
theorem GNNonExceptionalRepeatedPart_three_coprime_swap {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hc : Nat.Coprime a b) :
    Nat.Coprime (GNNonExceptionalRepeatedPart 3 a b)
      (GNNonExceptionalRepeatedPart 3 b a) := by
  apply Nat.coprime_of_dvd'
  intro q hq hf hg
  have hF := prime_sq_dvd_repeatedPrimePowerPart hq hf
  have hG := prime_sq_dvd_repeatedPrimePowerPart hq hg
  have hFn := GN_ne_zero_nat_of_two_le (by norm_num : 2 ≤ 3) ha hb
  have hGn := GN_ne_zero_nat_of_two_le (by norm_num : 2 ≤ 3) hb ha
  exact False.elim (not_prime_sq_dvd_both_GN_three hc hq
    ⟨hF.trans (GNNonExceptionalRepeatedPart_dvd_GN hFn),
     hG.trans (GNNonExceptionalRepeatedPart_dvd_GN hGn)⟩)

end DkMath.ABC
