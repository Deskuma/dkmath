/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.ABC.GNCubicOrientation
import DkMath.NumberTheory.GNThreePairedDepth

#print "file: DkMath.ABC.GNCubicPairedDepth"

/-!
# Simultaneously unbounded actual cubic repeated parts

Independent exact depths at 7 and 13 transfer to the actual non-exceptional
repeated parts. Both parts can exceed every fixed bound while their supports
remain disjoint. This is an absolute unboundedness statement, not a statement
about their size relative to height or the original ABC radical.
-/

namespace DkMath.ABC

open DkMath.CosmicFormulaBinom DkMath.NumberTheory

/-- A non-exceptional GN prime power of depth at least two belongs to the actual repeated part. -/
theorem prime_pow_dvd_GNNonExceptionalRepeatedPart {p a b q k : ℕ}
    (hq : Nat.Prime q) (hqp : ¬ q ∣ p) (hGN : GN p a b ≠ 0)
    (hk : 2 ≤ k) (hd : q ^ k ∣ GN p a b) :
    q ^ k ∣ GNNonExceptionalRepeatedPart p a b := by
  have hqGN : q ∣ GN p a b := (dvd_pow_self q (by omega : k ≠ 0)).trans hd
  have hqS : q ∈ GNNonExceptionalSupport p a b :=
    Finset.mem_filter.mpr ⟨mem_support_factorization_iff.mpr ⟨hGN,hq,hqGN⟩,hqp⟩
  have hv := (hq.pow_dvd_iff_le_factorization hGN).mp hd
  have hqN : q ∈ (GNNonExceptionalPart p a b).factorization.support := by
    rw [GNNonExceptionalPart_factorization_support]
    exact hqS
  have hvN : k ≤ (GNNonExceptionalPart p a b).factorization q := by
    rw [GNNonExceptionalPart_factorization, if_pos hqS]
    exact hv
  apply (hq.pow_dvd_iff_le_factorization (Nat.ne_of_gt (repeatedPrimePowerPart_pos _))).mpr
  rw [repeatedPrimePowerPart_factorization,
    if_pos ⟨hqN, hk.trans hvN⟩]
  exact hvN

/-- Both actual repeated parts can exceed every fixed bound while remaining coprime. -/
theorem exists_arbitrarily_large_coprime_cubic_repeated_parts (B : ℕ) :
    ∃ a : ℕ, 0 < a ∧
      B < GNNonExceptionalRepeatedPart 3 a 1 ∧
      B < GNNonExceptionalRepeatedPart 3 1 a ∧
      Nat.Coprime (GNNonExceptionalRepeatedPart 3 a 1)
        (GNNonExceptionalRepeatedPart 3 1 a) := by
  obtain ⟨a,ha,_,h7,_,h13,_⟩ := exists_large_GN_three_seven_thirteen_exact_depth
    (k := B+2) (l := B+2) (by omega) (by omega) 0
  have hF : GN 3 a 1 ≠ 0 := by rw [GN_three_dual_explicit]; positivity
  have hG : GN 3 1 a ≠ 0 := by rw [GN_three_dual_explicit]; positivity
  have h7rep := prime_pow_dvd_GNNonExceptionalRepeatedPart (by norm_num : Nat.Prime 7)
    (by norm_num : ¬7 ∣ 3) hF (by omega : 2 ≤ B+2) h7
  have h13rep := prime_pow_dvd_GNNonExceptionalRepeatedPart (by norm_num : Nat.Prime 13)
    (by norm_num : ¬13 ∣ 3) hG (by omega : 2 ≤ B+2) h13
  have h7B : B < (7:ℕ)^(B+2) := by
    have h := Nat.lt_pow_self (n := B+2) (by norm_num : 1 < 7)
    omega
  have h13B : B < (13:ℕ)^(B+2) := by
    have h := Nat.lt_pow_self (n := B+2) (by norm_num : 1 < 13)
    omega
  exact ⟨a,ha,h7B.trans_le (Nat.le_of_dvd (repeatedPrimePowerPart_pos _) h7rep),
    h13B.trans_le (Nat.le_of_dvd (repeatedPrimePowerPart_pos _) h13rep),
    GNNonExceptionalRepeatedPart_three_coprime_swap ha (by norm_num) (by simp)⟩

end DkMath.ABC
