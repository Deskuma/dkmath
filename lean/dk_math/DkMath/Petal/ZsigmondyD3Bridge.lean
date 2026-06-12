/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Petal.BoundaryD3
import DkMath.Zsigmondy

#print "file: DkMath.Petal.ZsigmondyD3Bridge"

/-!
# Petal Zsigmondy D3 Bridge

This file is the first Petal-facing handshake with the existing Zsigmondy
primitive-divisor API.

It intentionally proves only existence and location statements for the
degree-three reduced branch.  It does not prove any `padicValNat <= 1` bound:
that belongs to the squarefree/no-lift multiplicity layer.
-/

namespace DkMath
namespace Petal

open DkMath.CosmicFormulaBinom
open DkMath.FLT.PetalDetect

/--
Reduced cubic Petal coordinates satisfy the existing Zsigmondy `d = 3`
primitive-divisor existence theorem.
-/
theorem exists_primitivePrimeDivisor_d3_of_boundaryD3Reduced
    {c b : ℕ} (hbc : b < c) (hb : 0 < b)
    (hcop : Nat.Coprime c b) (hred : BoundaryD3Reduced c b) :
    ∃ q : ℕ, DkMath.Zsigmondy.PrimitivePrimeDivisor c b 3 q := by
  exact
    DkMath.Zsigmondy.exists_primitivePrimeDivisor_prime_exp
      (a := c) (b := b) (d := 3)
      Nat.prime_three (by norm_num) hbc hb hcop hred

/--
A `d = 3` primitive divisor obtained from Zsigmondy does not divide the
boundary gap.
-/
theorem primitivePrimeDivisor_d3_not_dvd_sub
    {c b q : ℕ} (hprim : DkMath.Zsigmondy.PrimitivePrimeDivisor c b 3 q) :
    ¬ q ∣ c - b := by
  have hnot : ¬ q ∣ c ^ 1 - b ^ 1 :=
    DkMath.Zsigmondy.PrimitivePrimeDivisor.not_dvd_lower
      hprim (by norm_num) (by norm_num)
  simpa using hnot

/--
A `d = 3` primitive divisor obtained from Zsigmondy lies on the cubic Petal
`S0_nat` face.
-/
theorem primitivePrimeDivisor_d3_dvd_S0_nat
    {c b q : ℕ} (hbc : b < c)
    (hprim : DkMath.Zsigmondy.PrimitivePrimeDivisor c b 3 q) :
    q ∣ S0_nat c b := by
  have hx : 0 < c - b := Nat.sub_pos_of_lt hbc
  have hprim_body :
      DkMath.Zsigmondy.PrimitivePrimeDivisor (c - b + b) b 3 q := by
    simpa [Nat.sub_add_cancel hbc.le] using hprim
  have hq_dvd_GN :
      q ∣ GN 3 (c - b) b := by
    exact
      (DkMath.Zsigmondy.primitivePrimeDivisor_body_three_imp_dvd_GN
        (x := c - b) (u := b) hx hprim_body)
  rw [S0_nat_eq_GN_three_sub hbc]
  exact hq_dvd_GN

/--
The same `d = 3` Zsigmondy primitive divisor can be read as an anchored
`S0_nat` carrier.
-/
theorem anchoredS0Carrier_of_primitivePrimeDivisor_d3
    {c b q : ℕ} (hbc : b < c)
    (hprim : DkMath.Zsigmondy.PrimitivePrimeDivisor c b 3 q) :
    AnchoredS0Carrier q c b q := by
  refine ⟨?_, ?_⟩
  · exact hasPositiveAnchorPrime_self_of_prime
      (DkMath.Zsigmondy.PrimitivePrimeDivisor.prime hprim)
  · exact primitivePrimeDivisor_d3_dvd_S0_nat hbc hprim

/--
The reduced cubic branch yields a single witness that is simultaneously a
Zsigmondy primitive divisor and a Petal anchored `S0_nat` carrier.
-/
theorem exists_anchoredS0Carrier_and_primitivePrimeDivisor_d3
    {c b : ℕ} (hbc : b < c) (hb : 0 < b)
    (hcop : Nat.Coprime c b) (hred : BoundaryD3Reduced c b) :
    ∃ q : ℕ,
      DkMath.Zsigmondy.PrimitivePrimeDivisor c b 3 q ∧
        AnchoredS0Carrier q c b q ∧
          ¬ q ∣ c - b := by
  rcases exists_primitivePrimeDivisor_d3_of_boundaryD3Reduced hbc hb hcop hred with
    ⟨q, hprim⟩
  exact
    ⟨q, hprim, anchoredS0Carrier_of_primitivePrimeDivisor_d3 hbc hprim,
      primitivePrimeDivisor_d3_not_dvd_sub hprim⟩

/--
Projection form: the reduced cubic branch has a boundary-free prime divisor on
`S0_nat`.
-/
theorem exists_prime_dvd_S0_nat_of_boundaryD3Reduced_via_zsigmondy
    {c b : ℕ} (hbc : b < c) (hb : 0 < b)
    (hcop : Nat.Coprime c b) (hred : BoundaryD3Reduced c b) :
    ∃ q : ℕ, Nat.Prime q ∧ q ∣ S0_nat c b ∧ ¬ q ∣ c - b := by
  rcases exists_anchoredS0Carrier_and_primitivePrimeDivisor_d3 hbc hb hcop hred with
    ⟨q, hprim, hcarrier, hq_not_dvd_sub⟩
  exact
    ⟨q, DkMath.Zsigmondy.PrimitivePrimeDivisor.prime hprim,
      anchoredS0Carrier_dvd_S0 hcarrier, hq_not_dvd_sub⟩

end Petal
end DkMath
