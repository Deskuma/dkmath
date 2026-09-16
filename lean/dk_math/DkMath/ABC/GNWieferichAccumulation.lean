/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.ABC.GNExcessLargeBoundaryPacket
import DkMath.NumberTheory.GNWieferich

#print "file: DkMath.ABC.GNWieferichAccumulation"

set_option linter.style.longLine false
set_option linter.style.emptyLine false

/-!
# Exact GN-Wieferich interpretation of the large boundary

The excess-active primes of the canonical interval profile are exactly the
non-exceptional GN-Wieferich lifts.  Consequently the large-boundary modulus
is the complete product of their full GN prime-power depths.
-/

namespace DkMath.ABC

open DkMath.CosmicFormulaBinom
open DkMath.NumberTheory

/--
At a positive coprime target point, active excess support is exactly
non-exceptional GN-Wieferich support.
-/
theorem mem_GNExcessActivePrimeSet_target_iff_GNWieferichLift
    {p b a X q : ℕ}
    (hp : Nat.Prime p)
    (ha : 0 < a)
    (hb : 0 < b)
    (haX : a ∈ Finset.Icc 0 X)
    (hcop : Nat.Coprime a b) :
    q ∈
        GNExcessActivePrimeSet
          (GNNonExceptionalIntervalPrimeFamily p b X)
          (GNExcessDepthProfileAt
            (GNNonExceptionalIntervalPrimeFamily p b X) p b a) ↔
      ¬ q ∣ p ∧ GNWieferichLift p a b q := by
  let Q := GNNonExceptionalIntervalPrimeFamily p b X
  let T : Triple := Triple.mk a b (a + b) rfl hcop
  have hactive :=
    GNExcessActivePrimeSet_target_eq_repeatedSupport
      hp haX hcop
  have hGN0 : GN p a b ≠ 0 :=
    GN_ne_zero_nat_of_two_le hp.two_le ha hb
  constructor
  · intro hqactive
    have hqrepeated :
        q ∈ (GNNonExceptionalPart p a b).factorization.support.filter
          (fun r =>
            2 ≤ (GNNonExceptionalPart p a b).factorization r) := by
      rw [← hactive]
      exact hqactive
    have hqpart := (Finset.mem_filter.mp hqrepeated).1
    have hvpart := (Finset.mem_filter.mp hqrepeated).2
    have hqS : q ∈ GNNonExceptionalSupport p a b := by
      rw [← GNNonExceptionalPart_factorization_support]
      exact hqpart
    have hfresh :=
      T.nonExceptionalSupport_fresh hp.one_le ha hqS
    have hv :
        2 ≤ (GN p a b).factorization q := by
      rw [GNNonExceptionalPart_factorization, ite_eq_left hqS] at hvpart
      exact hvpart
    have hq2 : q ^ 2 ∣ GN p a b :=
      (hfresh.1.pow_dvd_iff_le_factorization hGN0).2 hv
    exact
      ⟨(Finset.mem_filter.mp hqS).2,
        hfresh.1, hfresh.2.1, hfresh.2.2.1, hq2⟩
  · rintro ⟨hqp, hqprime, hqGN, hqa, hq2⟩
    have hqGNsupport :
        q ∈ (GN p a b).factorization.support :=
      mem_support_factorization_iff.mpr
        ⟨hGN0, hqprime, hqGN⟩
    have hqS : q ∈ GNNonExceptionalSupport p a b :=
      Finset.mem_filter.mpr ⟨hqGNsupport, hqp⟩
    have hqb : ¬ q ∣ b := by
      intro hqbd
      exact
        (DkMath.NumberTheory.prime_dvd_right_not_dvd_GN_of_coprime
          hp.one_le hcop hqprime hqbd) hqGN
    have hqQ : q ∈ Q := by
      exact mem_GNNonExceptionalIntervalPrimeFamily_iff.mpr
        ⟨a, haX, hqS, hqb⟩
    apply Finset.mem_filter.mpr
    refine ⟨hqQ, ?_⟩
    have hv :
        2 ≤ padicValNat q (GN p a b) :=
      (@padicValNat_dvd_iff_le q (Fact.mk hqprime)
        (GN p a b) 2 hGN0).1 hq2
    have hvalue :
        GNExcessProfileValue Q
            (GNExcessDepthProfileAt Q p b a) q =
          padicValNat q (GN p a b) - 1 := by
      simp [GNExcessProfileValue, GNExcessDepthProfileAt, hqQ]
    rw [hvalue]
    omega

/-- The finite set of non-exceptional GN-Wieferich primes at one point. -/
noncomputable def GNNonExceptionalWieferichPrimeSet
    (p a b : ℕ) : Finset ℕ :=
  by
    classical
    exact
      (GNNonExceptionalSupport p a b).filter
        (fun q => GNWieferichLift p a b q)

/--
The GN-Wieferich prime set is exactly the repeated support of the
non-exceptional GN factor.
-/
theorem GNNonExceptionalWieferichPrimeSet_eq_repeatedSupport
    {p a b : ℕ}
    (hp : Nat.Prime p)
    (ha : 0 < a)
    (hb : 0 < b)
    (hcop : Nat.Coprime a b) :
    GNNonExceptionalWieferichPrimeSet p a b =
      (GNNonExceptionalPart p a b).factorization.support.filter
        (fun q =>
          2 ≤ (GNNonExceptionalPart p a b).factorization q) := by
  classical
  let Q := GNNonExceptionalIntervalPrimeFamily p b a
  let A :=
    GNExcessActivePrimeSet Q
      (GNExcessDepthProfileAt Q p b a)
  have haIcc : a ∈ Finset.Icc 0 a := by simp
  have hArepeated :
      A =
        (GNNonExceptionalPart p a b).factorization.support.filter
          (fun q =>
            2 ≤ (GNNonExceptionalPart p a b).factorization q) := by
    exact
      GNExcessActivePrimeSet_target_eq_repeatedSupport
        hp haIcc hcop
  have hGN0 : GN p a b ≠ 0 :=
    GN_ne_zero_nat_of_two_le hp.two_le ha hb
  calc
    GNNonExceptionalWieferichPrimeSet p a b = A := by
      ext q
      simp only [GNNonExceptionalWieferichPrimeSet,
        Finset.mem_filter]
      constructor
      · rintro ⟨hqS, hqW⟩
        apply
          (mem_GNExcessActivePrimeSet_target_iff_GNWieferichLift
            hp ha hb haIcc hcop).mpr
        exact
          ⟨(Finset.mem_filter.mp hqS).2, hqW⟩
      · intro hq
        have hqdata :=
          (mem_GNExcessActivePrimeSet_target_iff_GNWieferichLift
            hp ha hb haIcc hcop).mp hq
        rcases hqdata.2 with ⟨hqprime, hqGN, hqa, hq2⟩
        have hqGNsupport :
            q ∈ (GN p a b).factorization.support :=
          mem_support_factorization_iff.mpr
            ⟨hGN0, hqprime, hqGN⟩
        exact
          ⟨Finset.mem_filter.mpr ⟨hqGNsupport, hqdata.1⟩,
            ⟨hqprime, hqGN, hqa, hq2⟩⟩
    _ = _ := hArepeated

/--
The exact repeated part is the product of the complete GN prime powers over
all non-exceptional GN-Wieferich primes.
-/
theorem GNNonExceptionalRepeatedPart_eq_wieferichPrimePowerProduct
    {p a b : ℕ}
    (hp : Nat.Prime p)
    (ha : 0 < a)
    (hb : 0 < b)
    (hcop : Nat.Coprime a b) :
    GNNonExceptionalRepeatedPart p a b =
      ∏ q ∈ GNNonExceptionalWieferichPrimeSet p a b,
        q ^ padicValNat q (GN p a b) := by
  classical
  unfold GNNonExceptionalRepeatedPart repeatedPrimePowerPart
  rw [← GNNonExceptionalWieferichPrimeSet_eq_repeatedSupport
    hp ha hb hcop]
  apply Finset.prod_congr rfl
  intro q hq
  rw [GNNonExceptionalWieferichPrimeSet] at hq
  have hqS :
      q ∈ GNNonExceptionalSupport p a b :=
    (Finset.mem_filter.mp hq).1
  have hqprime :
      Nat.Prime q :=
    (mem_support_factorization_iff.mp
      (Finset.mem_filter.mp hqS).1).2.1
  rw [GNNonExceptionalPart_factorization, ite_eq_left hqS,
    Nat.factorization_def (GN p a b) hqprime]

/--
Large-boundary data enriched with its exact simultaneous GN-Wieferich
interpretation.
-/
structure GNWieferichAccumulationPacket
    (p a b X : ℕ) where
  largeBoundary : GNExcessLargeBoundaryPacket p a b X
  active_iff :
    ∀ q : ℕ,
      q ∈
          GNExcessActivePrimeSet
            (GNNonExceptionalIntervalPrimeFamily p b X)
            (GNExcessDepthProfileAt
              (GNNonExceptionalIntervalPrimeFamily p b X) p b a) ↔
        ¬ q ∣ p ∧ GNWieferichLift p a b q
  modulus_eq_wieferichPrimePowerProduct :
    largeBoundary.modulus =
      ∏ q ∈ GNNonExceptionalWieferichPrimeSet p a b,
        q ^ padicValNat q (GN p a b)

/-- A large canonical target profile yields simultaneous GN-Wieferich
accumulation data. -/
noncomputable def GNWieferichAccumulationPacket.of_target
    {p a b X : ℕ}
    (hp : Nat.Prime p)
    (hb : 0 < b)
    (ha : 0 < a)
    (haX : a ∈ Finset.Icc 0 X)
    (hcop : Nat.Coprime a b)
    (hlarge :
      X + 1 <
        GNExcessJointDepthModulus
          (GNNonExceptionalIntervalPrimeFamily p b X)
          (GNExcessDepthProfileAt
            (GNNonExceptionalIntervalPrimeFamily p b X) p b a)) :
    GNWieferichAccumulationPacket p a b X := by
  let P :=
    GNExcessLargeBoundaryPacket.of_target
      hp hb ha haX hcop hlarge
  refine
    { largeBoundary := P
      active_iff := ?_
      modulus_eq_wieferichPrimePowerProduct := ?_ }
  · intro q
    exact
      mem_GNExcessActivePrimeSet_target_iff_GNWieferichLift
        hp ha hb haX hcop
  · rw [P.modulus_eq_repeated]
    exact
      GNNonExceptionalRepeatedPart_eq_wieferichPrimePowerProduct
        hp ha hb hcop

end DkMath.ABC
