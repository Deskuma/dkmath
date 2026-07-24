/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.ABC.GNValuationExcess

#print "file: DkMath.ABC.GNHighLift"

set_option linter.style.longLine false
set_option linter.style.emptyLine false

/-!
# High-lift primes on GN

This module isolates primes whose square divides a GN kernel.  It separates
exponent-exceptional high lifts (`q ∣ n`) from non-exceptional high lifts
(`q ∤ n`) and provides the local no-lift valuation obstruction.

It does not assert that non-exceptional high lifts are globally rare.
-/

namespace DkMath.ABC

open DkMath.CosmicFormulaBinom

/-- A prime whose square divides the selected GN kernel. -/
def GNHighLiftPrime (q n a b : ℕ) : Prop :=
  Nat.Prime q ∧ q ^ 2 ∣ GN n a b

/-- A GN high lift carried by a prime divisor of the exponent. -/
def GNExceptionalHighLiftPrime (q n a b : ℕ) : Prop :=
  GNHighLiftPrime q n a b ∧ q ∣ n

/-- A GN high lift carried by a prime not dividing the exponent. -/
def GNNonExceptionalHighLiftPrime (q n a b : ℕ) : Prop :=
  GNHighLiftPrime q n a b ∧ ¬ q ∣ n

/-- Every GN high lift lies in exactly one of the two exponent layers. -/
theorem GNHighLiftPrime.exceptional_or_nonExceptional
    {q n a b : ℕ} (h : GNHighLiftPrime q n a b) :
    GNExceptionalHighLiftPrime q n a b ∨
      GNNonExceptionalHighLiftPrime q n a b := by
  by_cases hqn : q ∣ n
  · exact Or.inl ⟨h, hqn⟩
  · exact Or.inr ⟨h, hqn⟩

/-- The exceptional and non-exceptional high-lift layers are disjoint. -/
theorem not_exceptional_and_nonExceptional_highLift
    (q n a b : ℕ) :
    ¬ (GNExceptionalHighLiftPrime q n a b ∧
      GNNonExceptionalHighLiftPrime q n a b) := by
  rintro ⟨⟨_, hqn⟩, ⟨_, hqn'⟩⟩
  exact hqn' hqn

/-- A non-exceptional GN high-lift prime cannot divide the ABC boundary. -/
theorem Triple.nonExceptionalHighLift_not_dvd_boundary
    (T : Triple) {n q : ℕ}
    (hn : 1 ≤ n) (ha : 0 < T.a)
    (h : GNNonExceptionalHighLiftPrime q n T.a T.b) :
    ¬ q ∣ T.a := by
  exact T.not_dvd_boundary_of_not_dvd_exp_of_dvd_GN
    hn ha h.2 (dvd_trans (dvd_pow_self q (by decide : (2 : ℕ) ≠ 0)) h.1.2)

/-- A GN high lift has valuation at least two. -/
theorem two_le_padicValNat_GN_of_highLift
    {q n a b : ℕ} (hGN : GN n a b ≠ 0)
    (h : GNHighLiftPrime q n a b) :
    2 ≤ padicValNat q (GN n a b) := by
  exact (DkMath.ABC.padicValNat_le_iff_dvd h.1 hGN 2).2 h.2

/-- Absence of a square lift bounds the GN valuation by one. -/
theorem padicValNat_GN_le_one_of_noHighLift
    {q n a b : ℕ} (hq : Nat.Prime q) (hGN : GN n a b ≠ 0)
    (hNoLift : ¬ q ^ 2 ∣ GN n a b) :
    padicValNat q (GN n a b) ≤ 1 := by
  by_contra hle
  have htwo : 2 ≤ padicValNat q (GN n a b) := by omega
  exact hNoLift ((DkMath.ABC.padicValNat_le_iff_dvd hq hGN 2).1 htwo)

/--
On a non-exceptional GN channel with no square lift, the full power-difference
valuation is at most one.
-/
theorem Triple.padic_powerDiff_le_one_of_nonExceptional_noHighLift
    (T : Triple) {n q : ℕ}
    (hn : 2 ≤ n) (ha : 0 < T.a) (hb : 0 < T.b)
    (hq : Nat.Prime q) (hq_exp : ¬ q ∣ n)
    (hq_GN : q ∣ GN n T.a T.b)
    (hNoLift : ¬ q ^ 2 ∣ GN n T.a T.b) :
    padicValNat q (T.c ^ n - T.b ^ n) ≤ 1 := by
  rw [T.padic_powerDiff_eq_GN_of_not_dvd_exp_of_dvd_GN
    hn ha hb hq hq_exp hq_GN]
  exact padicValNat_GN_le_one_of_noHighLift hq
    (GN_ne_zero_nat_of_two_le hn ha hb) hNoLift

end DkMath.ABC
