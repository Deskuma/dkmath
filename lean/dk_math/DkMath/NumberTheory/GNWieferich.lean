/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Gcd.GN

#print "file: DkMath.NumberTheory.GNWieferich"

set_option linter.style.longLine false
set_option linter.style.emptyLine false

/-!
# Clean Wieferich lifts for the GN kernel

This module records the generic arithmetic meaning of a two-step prime lift
inside `GN`.  It deliberately lives below the FLT and ABC packages.
-/

namespace DkMath.NumberTheory

open DkMath.CosmicFormulaBinom
open DkMath.NumberTheory.Gcd

/--
A prime is a GN-Wieferich lift when it avoids the boundary gap and occurs to
depth at least two in the GN kernel.
-/
def GNWieferichLift (p a b q : ℕ) : Prop :=
  Nat.Prime q ∧
    q ∣ GN p a b ∧
      ¬ q ∣ a ∧
        q ^ 2 ∣ GN p a b

/--
Avoiding the boundary gap transports arbitrary prime-power divisibility
between the GN kernel and its difference-of-powers body.
-/
theorem primePow_dvd_GN_iff_primePow_dvd_diff
    {p a b q k : ℕ}
    (hp2 : 2 ≤ p)
    (ha : 0 < a)
    (hb : 0 < b)
    (hq : Nat.Prime q)
    (hqa : ¬ q ∣ a) :
    q ^ k ∣ GN p a b ↔
      q ^ k ∣ (a + b) ^ p - b ^ p := by
  have hdiff :
      padicValNat q ((a + b) ^ p - b ^ p) =
        padicValNat q (GN p a b) := by
    simpa using
      padicValNat_sub_pow_eq_padicValNat_GN_of_not_dvd_gap
        hp2 (by omega : b < a + b) hb hq (by simpa using hqa)
  have hGN0 : GN p a b ≠ 0 :=
    GN_ne_zero_nat_of_two_le hp2 ha hb
  have hdiff0 : (a + b) ^ p - b ^ p ≠ 0 := by
    have hp0 : p ≠ 0 := by omega
    exact Nat.sub_ne_zero_of_lt
      (Nat.pow_lt_pow_left (by omega : b < a + b) hp0)
  constructor
  · intro h
    apply
      (@padicValNat_dvd_iff_le q (Fact.mk hq)
        ((a + b) ^ p - b ^ p) k hdiff0).2
    rw [hdiff]
    exact
      (@padicValNat_dvd_iff_le q (Fact.mk hq)
        (GN p a b) k hGN0).1 h
  · intro h
    apply
      (@padicValNat_dvd_iff_le q (Fact.mk hq)
        (GN p a b) k hGN0).2
    rw [← hdiff]
    exact
      (@padicValNat_dvd_iff_le q (Fact.mk hq)
        ((a + b) ^ p - b ^ p) k hdiff0).1 h

/--
The GN predicate is exactly the difference-power Wieferich predicate at
`z = a + b`, `y = b`.
-/
theorem GNWieferichLift_iff_diffLift
    {p a b q : ℕ}
    (hp2 : 2 ≤ p)
    (ha : 0 < a)
    (hb : 0 < b) :
    GNWieferichLift p a b q ↔
      Nat.Prime q ∧
        q ∣ ((a + b) ^ p - b ^ p) ∧
          ¬ q ∣ a ∧
            q ^ 2 ∣ ((a + b) ^ p - b ^ p) := by
  constructor
  · rintro ⟨hq, hqGN, hqa, hq2GN⟩
    exact
      ⟨hq,
        by
          simpa using
            (primePow_dvd_GN_iff_primePow_dvd_diff
              (k := 1) hp2 ha hb hq hqa).mp (by simpa using hqGN),
        hqa,
        (primePow_dvd_GN_iff_primePow_dvd_diff
          (k := 2) hp2 ha hb hq hqa).mp hq2GN⟩
  · rintro ⟨hq, hqdiff, hqa, hq2diff⟩
    exact
      ⟨hq, by
          simpa using
            (primePow_dvd_GN_iff_primePow_dvd_diff
              (k := 1) hp2 ha hb hq hqa).mpr (by simpa using hqdiff),
        hqa,
        (primePow_dvd_GN_iff_primePow_dvd_diff
          (k := 2) hp2 ha hb hq hqa).mpr hq2diff⟩

end DkMath.NumberTheory
