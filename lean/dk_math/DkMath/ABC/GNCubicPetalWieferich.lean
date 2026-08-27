/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.ABC.GNWieferichAccumulation
import DkMath.Petal.PrimitiveD3ValuationBridge

#print "file: DkMath.ABC.GNCubicPetalWieferich"

set_option linter.style.longLine false
set_option linter.style.emptyLine false

/-!
# Cubic Petal-Wieferich orientation

Every positive coprime ABC triple admits a cubic Petal orientation.  The
primitive prime supplied in that orientation either has valuation at most one
or is a GN-Wieferich lift lying in the exact repeated support.

No NoWieferich research/default module is imported or used.
-/

namespace DkMath.ABC

open DkMath.CosmicFormulaBinom
open DkMath.NumberTheory
open DkMath.Petal

namespace Triple

/-- Exchange the two left coordinates of an ABC triple. -/
def swap (T : Triple) : Triple where
  a := T.b
  b := T.a
  c := T.c
  hsum := by simpa [Nat.add_comm] using T.hsum
  hcop := T.hcop.symm

@[simp] theorem swap_a (T : Triple) : T.swap.a = T.b := rfl
@[simp] theorem swap_b (T : Triple) : T.swap.b = T.a := rfl
@[simp] theorem swap_c (T : Triple) : T.swap.c = T.c := rfl
@[simp] theorem swap_hcop (T : Triple) : Nat.Coprime T.swap.a T.swap.b :=
  T.hcop.symm

@[simp] theorem swap_swap (T : Triple) : T.swap.swap = T := by
  cases T
  rfl

/-- Swapping the left coordinates preserves the ABC radical input. -/
theorem rad_mul_swap (T : Triple) :
    rad (T.swap.a * T.swap.b * T.swap.c) =
      rad (T.a * T.b * T.c) := by
  congr 1
  simp only [swap_a, swap_b, swap_c]
  ac_rfl

/-- The pointwise raw ABC conclusion is invariant under left-coordinate
orientation. -/
theorem abcBound_swap_iff
    (T : Triple) (K ε : ℝ) :
    (T.swap.c : ℝ) ≤
        K * (rad (T.swap.a * T.swap.b * T.swap.c) : ℝ) ^ (1 + ε) ↔
      (T.c : ℝ) ≤
        K * (rad (T.a * T.b * T.c) : ℝ) ^ (1 + ε) := by
  have hrad := T.rad_mul_swap
  simp only [swap_a, swap_b, swap_c] at hrad ⊢
  rw [hrad]

end Triple

/--
At least one orientation of a coprime ABC triple lies in the reduced cubic
Petal branch.
-/
theorem Triple.cubicReduced_or_swapReduced
    (T : Triple) :
    BoundaryD3Reduced T.c T.b ∨
      BoundaryD3Reduced T.c T.a := by
  rw [← T.hsum]
  simp only [BoundaryD3Reduced, Nat.add_sub_cancel_left,
    Nat.add_sub_cancel_right]
  by_cases h3a : 3 ∣ T.a
  · right
    intro h3b
    have h3gcd : 3 ∣ Nat.gcd T.a T.b :=
      Nat.dvd_gcd h3a h3b
    rw [T.hcop] at h3gcd
    exact Nat.prime_three.not_dvd_one h3gcd
  · exact Or.inl h3a

/--
A cubic Petal witness, together with its exact NoLift/Wieferich
multiplicity branch.
-/
structure GNCubicPetalWieferichPacket
    (a b q : ℕ) where
  prime : Nat.Prime q
  primitive :
    DkMath.Zsigmondy.PrimitivePrimeDivisor (a + b) b 3 q
  anchored : AnchoredS0Carrier q (a + b) b q
  notDvdGap : ¬ q ∣ a
  dividesGN : q ∣ GN 3 a b
  branch :
    padicValNat q (GN 3 a b) ≤ 1 ∨
      (GNWieferichLift 3 a b q ∧
        q ∈
          (GNNonExceptionalPart 3 a b).factorization.support.filter
            (fun r =>
              2 ≤ (GNNonExceptionalPart 3 a b).factorization r))

/--
One reduced positive cubic orientation supplies a Petal witness split into a
NoLift valuation-one channel or an exact repeated-support Wieferich channel.
-/
theorem exists_cubicPetalWieferichPacket_of_reduced
    {a b : ℕ}
    (ha : 0 < a)
    (hb : 0 < b)
    (hcop : Nat.Coprime a b)
    (hred : BoundaryD3Reduced (a + b) b) :
    ∃ q : ℕ, GNCubicPetalWieferichPacket a b q := by
  have hbc : b < a + b := by omega
  have hcCop : Nat.Coprime (a + b) b :=
    (Nat.coprime_add_self_left).2 hcop
  rcases
      exists_anchoredS0Carrier_and_primitivePrimeDivisor_d3
        hbc hb hcCop hred with
    ⟨q, hprim, hanchored, hqgap⟩
  have hqprime : Nat.Prime q :=
    DkMath.Zsigmondy.PrimitivePrimeDivisor.prime hprim
  have hqGN : q ∣ GN 3 a b := by
    have hqS0 :=
      primitivePrimeDivisor_d3_dvd_S0_nat hbc hprim
    rw [S0_nat_eq_GN_three_sub hbc] at hqS0
    simpa using hqS0
  have hqgap' : ¬ q ∣ a := by
    simpa using hqgap
  refine ⟨q, hqprime, hprim, hanchored, hqgap', hqGN, ?_⟩
  by_cases hq2 : q ^ 2 ∣ GN 3 a b
  · right
    have hW : GNWieferichLift 3 a b q :=
      ⟨hqprime, hqGN, hqgap', hq2⟩
    refine ⟨hW, ?_⟩
    have hGN0 : GN 3 a b ≠ 0 :=
      GN_ne_zero_nat_of_two_le (by norm_num) ha hb
    have hqnot3 : ¬ q ∣ 3 := by
      intro hq3
      have hqeq :
          q = 3 :=
        (Nat.prime_dvd_prime_iff_eq hqprime Nat.prime_three).1 hq3
      subst q
      exact hqgap'
        (prime_dvd_boundary_of_dvd_GN_prime
          Nat.prime_three hqGN)
    have hqGNsupport :
        q ∈ (GN 3 a b).factorization.support :=
      mem_support_factorization_iff.mpr
        ⟨hGN0, hqprime, hqGN⟩
    have hqS : q ∈ GNNonExceptionalSupport 3 a b :=
      Finset.mem_filter.mpr ⟨hqGNsupport, hqnot3⟩
    apply Finset.mem_filter.mpr
    refine ⟨?_, ?_⟩
    · rw [GNNonExceptionalPart_factorization_support]
      exact hqS
    · rw [GNNonExceptionalPart_factorization, if_pos hqS]
      exact
        (hqprime.pow_dvd_iff_le_factorization hGN0).1 hq2
  · left
    have hdiff :=
      primitiveD3_padicValNat_le_one_of_noLift_GN
        hbc hprim (by simpa using hq2)
    have hval :
        padicValNat q ((a + b) ^ 3 - b ^ 3) =
          padicValNat q (GN 3 a b) := by
      simpa using
        DkMath.NumberTheory.Gcd.padicValNat_sub_pow_eq_padicValNat_GN_of_not_dvd_gap
          (by norm_num : 2 ≤ 3) hbc hb hqprime (by simpa using hqgap')
    rw [hval] at hdiff
    exact hdiff

/--
Every positive coprime ABC triple supplies a cubic Petal-Wieferich packet in
one of its two left-coordinate orientations.
-/
theorem exists_oriented_cubicPetalWieferichPacket
    (T : Triple)
    (ha : 0 < T.a)
    (hb : 0 < T.b) :
    (∃ q : ℕ, GNCubicPetalWieferichPacket T.a T.b q) ∨
      (∃ q : ℕ, GNCubicPetalWieferichPacket T.b T.a q) := by
  rcases T.cubicReduced_or_swapReduced with hred | hred
  · left
    have hred' : BoundaryD3Reduced (T.a + T.b) T.b := by
      simpa [T.hsum] using hred
    exact
      exists_cubicPetalWieferichPacket_of_reduced
        ha hb T.hcop hred'
  · right
    have hred' : BoundaryD3Reduced (T.b + T.a) T.a := by
      simpa [T.hsum, Nat.add_comm] using hred
    exact
      exists_cubicPetalWieferichPacket_of_reduced
        hb ha T.hcop.symm hred'

end DkMath.ABC
