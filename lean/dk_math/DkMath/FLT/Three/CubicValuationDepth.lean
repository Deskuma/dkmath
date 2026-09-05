/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Three.PrimitiveCubicLiftPacket

#print "file: DkMath.FLT.Three.CubicValuationDepth"

namespace DkMath.FLT.Three

open DkMath.CosmicFormulaBinom
open DkMath.FLT
open DkMath.FLT.PetalDetect
open DkMath.NumberTheory
open DkMath.NumberTheory.GcdNext

/-!
## Exact cubic valuation depth

This module turns the packet lower bound into the exact cubic valuation
forced by `a ^ 3 + b ^ 3 = c ^ 3`.  The result is finite arithmetic data for
the GN shell; it does not construct a NoLift/Lift splitter or a descent.
-/

private lemma cubic_counterexample_gap_lt
    {a b c : ℕ} (ha : 0 < a)
    (hEq : a ^ 3 + b ^ 3 = c ^ 3) : b < c := by
  by_contra hbc_not
  have hcb : c ≤ b := Nat.not_lt.mp hbc_not
  have hc3_le : c ^ 3 ≤ b ^ 3 := Nat.pow_le_pow_left hcb 3
  have hsum_le : a ^ 3 + b ^ 3 ≤ b ^ 3 := by
    simpa [hEq] using hc3_le
  have ha3_pos : 0 < a ^ 3 := by positivity
  omega

private lemma padicValNat_cubic_diff_eq_GN_of_packet
    {a b c q : ℕ} (h : PrimitiveCubicLiftPacket a b c q)
    (ha : 0 < a) (hEq : a ^ 3 + b ^ 3 = c ^ 3) :
    padicValNat q (c ^ 3 - b ^ 3) =
      padicValNat q (DkMath.CosmicFormulaBinom.GN 3 (c - b) b) := by
  have hbc : b < c := cubic_counterexample_gap_lt ha hEq
  have hfactor :
      c ^ 3 - b ^ 3 =
        (c - b) * DkMath.CosmicFormulaBinom.GN 3 (c - b) b := by
    exact pow_sub_pow_factor_cosmic_N (a := c) (b := b) (d := 3)
      (by norm_num) hbc
  have hdiff_ne : c ^ 3 - b ^ 3 ≠ 0 := by
    exact Nat.sub_ne_zero_of_lt
      (Nat.pow_lt_pow_left hbc (by decide : 3 ≠ 0))
  have hGN_ne : DkMath.CosmicFormulaBinom.GN 3 (c - b) b ≠ 0 := by
    intro hGN0
    have hrewrite := hfactor
    rw [hGN0, mul_zero] at hrewrite
    exact hdiff_ne hrewrite
  have hpadic :
      padicValNat q (c ^ 3 - b ^ 3) =
        padicValNat q (c - b) +
          padicValNat q (DkMath.CosmicFormulaBinom.GN 3 (c - b) b) := by
    exact padicValNat_factorization
      (a := c) (b := b) (d := 3) (q := q)
      (N := DkMath.CosmicFormulaBinom.GN 3 (c - b) b)
      (by norm_num) hbc h.hq hfactor hGN_ne
  have hzero : padicValNat q (c - b) = 0 :=
    padicValNat.eq_zero_of_not_dvd h.hqBoundary
  simpa [hzero] using hpadic

/--
Exact valuation transport for a primitive cubic packet.

For a packet built from `a ^ 3 + b ^ 3 = c ^ 3`, the GN valuation is exactly
the valuation of the cube `a ^ 3`, hence three times the valuation of `a`.
-/
theorem padicValNat_GN_three_eq_three_mul_padicValNat_of_packet
    {a b c q : ℕ}
    (h : PrimitiveCubicLiftPacket a b c q)
    (ha : 0 < a)
    (hEq : a ^ 3 + b ^ 3 = c ^ 3) :
    padicValNat q (DkMath.CosmicFormulaBinom.GN 3 (c - b) b) =
      3 * padicValNat q a := by
  letI : Fact (Nat.Prime q) := ⟨h.hq⟩
  have htransport := padicValNat_cubic_diff_eq_GN_of_packet h ha hEq
  have hsub : c ^ 3 - b ^ 3 = a ^ 3 := cube_sub_eq_of_add_eq hEq
  calc
    padicValNat q (DkMath.CosmicFormulaBinom.GN 3 (c - b) b) =
        padicValNat q (c ^ 3 - b ^ 3) := htransport.symm
    _ = padicValNat q (a ^ 3) := by rw [hsub]
    _ = 3 * padicValNat q a := by
      exact padicValNat.pow a 3

/--
The multiplier in the exact cubic depth is positive, with the packet lower
bound supplying the positivity.
-/
theorem exists_pos_cubic_depth_multiplier_of_packet
    {a b c q : ℕ}
    (h : PrimitiveCubicLiftPacket a b c q)
    (ha : 0 < a)
    (hEq : a ^ 3 + b ^ 3 = c ^ 3) :
    ∃ k : ℕ, 0 < k ∧
      padicValNat q (DkMath.CosmicFormulaBinom.GN 3 (c - b) b) = 3 * k := by
  have hexact := padicValNat_GN_three_eq_three_mul_padicValNat_of_packet h ha hEq
  have hdepthA : 3 ≤ 3 * padicValNat q a := by
    rw [← hexact]
    exact h.hdepth
  have hpositiveA : 0 < padicValNat q a := by omega
  exact ⟨padicValNat q a, hpositiveA, hexact⟩

private lemma GN_three_ne_zero_of_packet
    {a b c q : ℕ} (h : PrimitiveCubicLiftPacket a b c q) :
    DkMath.CosmicFormulaBinom.GN 3 (c - b) b ≠ 0 := by
  intro hGN0
  have hcontra := h.hdepth
  rw [hGN0] at hcontra
  rw [padicValNat_zero_right] at hcontra
  omega

/--
The packet's depth lower bound forces a cubic prime-power divisor on the GN
side.  This theorem uses only packet data and does not assume an exact
equation or a NoLift hypothesis.
-/
theorem cube_dvd_GN_of_primitiveCubicLiftPacket
    {a b c q : ℕ}
    (h : PrimitiveCubicLiftPacket a b c q) :
    q ^ 3 ∣ DkMath.CosmicFormulaBinom.GN 3 (c - b) b := by
  letI : Fact (Nat.Prime q) := ⟨h.hq⟩
  exact
    (@padicValNat_dvd_iff_le q (Fact.mk h.hq)
      (DkMath.CosmicFormulaBinom.GN 3 (c - b) b) 3
      (GN_three_ne_zero_of_packet h)).2 h.hdepth

/-- The forced cubic divisor also yields the square divisor used by later branches. -/
theorem square_dvd_GN_of_primitiveCubicLiftPacket
    {a b c q : ℕ}
    (h : PrimitiveCubicLiftPacket a b c q) :
    q ^ 2 ∣ DkMath.CosmicFormulaBinom.GN 3 (c - b) b := by
  apply dvd_trans (show q ^ 2 ∣ q ^ 3 by
    refine ⟨q, ?_⟩
    ring)
  exact cube_dvd_GN_of_primitiveCubicLiftPacket h

end DkMath.FLT.Three
