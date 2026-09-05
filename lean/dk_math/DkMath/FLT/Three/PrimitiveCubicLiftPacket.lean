/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.PhaseLift
import DkMath.NumberTheory.GNThreeHenselDepth

#print "file: DkMath.FLT.Three.PrimitiveCubicLiftPacket"

namespace DkMath.FLT.Three

open DkMath.CosmicFormulaBinom
open DkMath.FLT
open DkMath.FLT.PetalDetect
open DkMath.NumberTheory
open DkMath.NumberTheory.GcdNext

/-!
## Primitive cubic lift packet

This module packages the finite, non-ramified prime data needed by the
degree-three GN lifting API.  It is a bridge from a primitive cubic
counterexample shape to one `q`-adic GN packet; it does not perform a strict
descent or claim an infinite lift.
-/

/--
The finite prime packet attached to cubic coordinates `a`, `b`, `c` and a
primitive prime `q` of the cubic difference.

The coordinates exposed to the GN API are `u = c - b` and `x = b`.  The
valuation lower bound is deliberately a packet field, while its constructor
below derives it from the cubic equation and the primitive valuation
transport.
-/
structure PrimitiveCubicLiftPacket (a b c q : ℕ) : Prop where
  hq : Nat.Prime q
  hqDiff : q ∣ c ^ 3 - b ^ 3
  hqBoundary : ¬ q ∣ c - b
  hcopCoordinates : Nat.Coprime (c - b) b
  hqGN : q ∣ DkMath.CosmicFormulaBinom.GN 3 (c - b) b
  hqThree : q ≠ 3
  hresidue : 3 ∣ q - 1
  hderivative : ¬ q ∣ 2 * (c - b) + 3 * b
  hdepth :
    3 ≤ padicValNat q (DkMath.CosmicFormulaBinom.GN 3 (c - b) b)

private lemma padicValNat_cubic_diff_eq_GN
    {c b q : ℕ} (hbc : b < c) (hq : Nat.Prime q)
    (hqBoundary : ¬ q ∣ c - b) :
    padicValNat q (c ^ 3 - b ^ 3) =
      padicValNat q (DkMath.CosmicFormulaBinom.GN 3 (c - b) b) := by
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
      (by norm_num) hbc hq hfactor hGN_ne
  have hzero : padicValNat q (c - b) = 0 :=
    padicValNat.eq_zero_of_not_dvd hqBoundary
  simpa [hzero] using hpadic

/--
Construct the packet from a positive primitive cubic equation and a supplied
primitive prime divisor of `c^3 - b^3`.

The lower bound is transported from `a^3` through
`c^3 - b^3 = a^3` and the factorization of the cubic difference.  No
`NoLift` hypothesis or completed FLT theorem is used.
-/
theorem primitiveCubicLiftPacket_of_counterexample_prime
    {a b c q : ℕ}
    (ha : 0 < a) (_hb : 0 < b) (_hc : 0 < c)
    (hab : Nat.Coprime a b)
    (hEq : a ^ 3 + b ^ 3 = c ^ 3)
    (hq : Nat.Prime q)
    (hqDiff : q ∣ c ^ 3 - b ^ 3)
    (hqBoundary : ¬ q ∣ c - b) :
    PrimitiveCubicLiftPacket a b c q := by
  have hcopCB : Nat.Coprime c b := coprime_cb_of_eq hab hEq
  have hbc : b < c := by
    by_contra hbc_not
    have hcb : c ≤ b := Nat.not_lt.mp hbc_not
    have hc3_le : c ^ 3 ≤ b ^ 3 := Nat.pow_le_pow_left hcb 3
    have hsum_le : a ^ 3 + b ^ 3 ≤ b ^ 3 := by
      simpa [hEq] using hc3_le
    have ha3_pos : 0 < a ^ 3 := by positivity
    omega
  have hcopCoordinates : Nat.Coprime (c - b) b :=
    (Nat.coprime_sub_self_left hbc.le).2 hcopCB
  have hqGN : q ∣ DkMath.CosmicFormulaBinom.GN 3 (c - b) b := by
    have hqS0 : q ∣ S0_nat c b :=
      prime_dvd_S0_via_cosmic_bridge hbc hq hqDiff hqBoundary
    rw [GN_three_sub_eq_S0_nat hbc]
    exact hqS0
  have hqThree : q ≠ 3 := by
    intro hqeq
    have h3GN : 3 ∣ DkMath.CosmicFormulaBinom.GN 3 (c - b) b := by
      simpa [hqeq] using hqGN
    have h3Boundary : 3 ∣ c - b :=
      (three_dvd_GN_three_iff_dvd_boundary (u := c - b) (x := b)).mp h3GN
    exact hqBoundary (by simpa [hqeq] using h3Boundary)
  have hresidue : 3 ∣ q - 1 :=
    three_dvd_prime_sub_one_of_prime_dvd_GN_three_of_coprime_of_ne_three
      hq hcopCoordinates hqGN hqThree
  have hderivative : ¬ q ∣ 2 * (c - b) + 3 * b :=
    prime_not_dvd_cubic_boundary_derivative
      hq hcopCoordinates hqGN hqThree
  have hsub : c ^ 3 - b ^ 3 = a ^ 3 := cube_sub_eq_of_add_eq hEq
  have hqDvdA3 : q ∣ a ^ 3 := by
    simpa [hsub] using hqDiff
  have hqDvdA : q ∣ a := hq.dvd_of_dvd_pow hqDvdA3
  have hdepthA : 3 ≤ padicValNat q (a ^ 3) :=
    padicValNat_lower_bound_of_dvd_d3 ha hq hqDvdA
  have hdepth :
      3 ≤ padicValNat q (DkMath.CosmicFormulaBinom.GN 3 (c - b) b) := by
    have htransport :
        padicValNat q (c ^ 3 - b ^ 3) =
          padicValNat q (DkMath.CosmicFormulaBinom.GN 3 (c - b) b) :=
      padicValNat_cubic_diff_eq_GN hbc hq hqBoundary
    rw [← htransport]
    simpa [hsub] using hdepthA
  exact
    { hq := hq
      hqDiff := hqDiff
      hqBoundary := hqBoundary
      hcopCoordinates := hcopCoordinates
      hqGN := hqGN
      hqThree := hqThree
      hresidue := hresidue
      hderivative := hderivative
      hdepth := hdepth }

end DkMath.FLT.Three
