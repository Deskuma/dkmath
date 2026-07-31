/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.CoordinateNormalForm

#print "file: DkMath.FLT.Seven.ModSevenSectors"

namespace DkMath.FLT.Seven

abbrev ModSeven := ZMod 7

local instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

theorem seven_dvd_endpoint_product_of_away {x y z : ℕ}
    (p : AwayCoordinateNormalForm x y z) : 7 ∣ y * z * (y + z) := by
  apply (ZMod.natCast_eq_zero_iff _ _).1
  have hsnd : (cyclotomicSevenSnd (z : ℤ) (y : ℤ) : ModSeven) = 0 := by
    rw [p.snd_eq, seventhPowerSnd_mod_seven]
  push_cast at hsnd ⊢
  simp [cyclotomicSevenSnd] at hsnd
  linear_combination -hsnd

theorem not_both_seven_dvd_y_z {x y z : ℕ}
    (p : AwayCoordinateNormalForm x y z) : ¬ (7 ∣ y ∧ 7 ∣ z) := by
  rintro ⟨hy, hz⟩
  exact (Nat.not_coprime_of_dvd_of_dvd (by norm_num) hy hz)
    (coprime_y_z_of_counterexamplePack p.counterexample)

theorem not_both_seven_dvd_y_sum {x y z : ℕ}
    (p : AwayCoordinateNormalForm x y z) : ¬ (7 ∣ y ∧ 7 ∣ y + z) := by
  rintro ⟨hy, hsum⟩
  have hz : 7 ∣ z :=
    (Nat.dvd_add_iff_right (k := 7) (m := y) (n := z) hy).mpr hsum
  exact not_both_seven_dvd_y_z p ⟨hy, hz⟩

theorem not_both_seven_dvd_z_sum {x y z : ℕ}
    (p : AwayCoordinateNormalForm x y z) : ¬ (7 ∣ z ∧ 7 ∣ y + z) := by
  rintro ⟨hz, hsum⟩
  have hy : 7 ∣ y :=
    (Nat.dvd_add_iff_left (k := 7) (m := y) (n := z) hz).mpr hsum
  exact not_both_seven_dvd_y_z p ⟨hy, hz⟩

inductive AwayExceptionalFactor (y z : ℕ) : Prop
  | right (hy : 7 ∣ y) (hz : ¬ 7 ∣ z) (hsum : ¬ 7 ∣ y + z)
  | left (hz : 7 ∣ z) (hy : ¬ 7 ∣ y) (hsum : ¬ 7 ∣ y + z)
  | sum (hsum : 7 ∣ y + z) (hy : ¬ 7 ∣ y) (hz : ¬ 7 ∣ z)

theorem awayExceptionalFactor_of_packet {x y z : ℕ}
    (p : AwayCoordinateNormalForm x y z) : AwayExceptionalFactor y z := by
  have hprod := seven_dvd_endpoint_product_of_away p
  rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 7)).mp hprod with hyz | hsum
  · rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 7)).mp hyz with hy | hz
    · exact .right hy (fun hz => not_both_seven_dvd_y_z p ⟨hy, hz⟩)
        (fun hs => not_both_seven_dvd_y_sum p ⟨hy, hs⟩)
    · exact .left hz (fun hy => not_both_seven_dvd_y_z p ⟨hy, hz⟩)
        (fun hs => not_both_seven_dvd_z_sum p ⟨hz, hs⟩)
  · exact .sum hsum (fun hy => not_both_seven_dvd_y_sum p ⟨hy, hsum⟩)
      (fun hz => not_both_seven_dvd_z_sum p ⟨hz, hsum⟩)

theorem fermat7Equation_modSeven_linear {x y z : ℕ}
    (hEq : Fermat7Equation x y z) :
    (x : ModSeven) + (y : ModSeven) = (z : ModSeven) := by
  have h := congrArg (fun n : ℕ => (n : ModSeven)) hEq
  push_cast at h
  simpa only [ZMod.pow_card] using h

inductive SevenEndpointResidueSector (x y z : ℕ) : Prop
  | ramified (t : ModSeven) (ht : t ≠ 0)
      (hx : (x : ModSeven) = 0) (hy : (y : ModSeven) = t)
      (hz : (z : ModSeven) = t)
  | awayRight (t : ModSeven) (ht : t ≠ 0)
      (hx : (x : ModSeven) = t) (hy : (y : ModSeven) = 0)
      (hz : (z : ModSeven) = t)
  | awayLeft (t : ModSeven) (ht : t ≠ 0)
      (hx : (x : ModSeven) = -t) (hy : (y : ModSeven) = t)
      (hz : (z : ModSeven) = 0)
  | awaySum (t : ModSeven) (ht : t ≠ 0)
      (hx : (x : ModSeven) = -2 * t) (hy : (y : ModSeven) = t)
      (hz : (z : ModSeven) = -t)

theorem sevenEndpointResidueSector_of_counterexample {x y z : ℕ}
    (hPack : CounterexamplePack x y z) : SevenEndpointResidueSector x y z := by
  have hlin := fermat7Equation_modSeven_linear hPack.hEq
  rcases coordinateCounterexampleRoute_of_pack hPack with ⟨route⟩
  cases route with
  | ramified p =>
      let t : ModSeven := (y : ModSeven)
      have hgap := p.seventhPower.residual.powerSplit.sevenAdic.seven_dvd_gap
      have hy7 := p.seventhPower.residual.powerSplit.sevenAdic.seven_not_dvd_y
      have hzyeq : (z : ModSeven) = (y : ModSeven) := by
        have hyz := (right_lt_of_fermat7Equation hPack.hx hPack.hEq).le
        exact (ZMod.natCast_eq_natCast_iff _ _ _).2
          ((Nat.modEq_iff_dvd' hyz).2 hgap).symm
      have ht : t ≠ 0 := by
        simpa [t, ZMod.natCast_eq_zero_iff] using hy7
      refine .ramified t ht ?_ rfl hzyeq
      rw [← hzyeq] at hlin
      linear_combination hlin
  | away p =>
      cases awayExceptionalFactor_of_packet p with
      | right hy hz hsum =>
          let t : ModSeven := (z : ModSeven)
          have hy0 : (y : ModSeven) = 0 :=
            (ZMod.natCast_eq_zero_iff _ _).2 hy
          have ht : t ≠ 0 := by
            simpa [t, ZMod.natCast_eq_zero_iff] using hz
          refine .awayRight t ht ?_ hy0 rfl
          simpa [t, hy0] using hlin
      | left hz hy hsum =>
          let t : ModSeven := (y : ModSeven)
          have hz0 : (z : ModSeven) = 0 :=
            (ZMod.natCast_eq_zero_iff _ _).2 hz
          have ht : t ≠ 0 := by
            simpa [t, ZMod.natCast_eq_zero_iff] using hy
          refine .awayLeft t ht ?_ rfl hz0
          rw [hz0] at hlin
          linear_combination hlin
      | sum hsum hy hz =>
          let t : ModSeven := (y : ModSeven)
          have hsum0 : (y : ModSeven) + (z : ModSeven) = 0 := by
            rw [← Nat.cast_add]
            exact (ZMod.natCast_eq_zero_iff _ _).2 hsum
          have ht : t ≠ 0 := by
            simpa [t, ZMod.natCast_eq_zero_iff] using hy
          have hzneg : (z : ModSeven) = -t := by
            dsimp [t]
            linear_combination hsum0
          refine .awaySum t ht ?_ rfl hzneg
          rw [hzneg] at hlin
          dsimp [t] at hlin ⊢
          linear_combination hlin

end DkMath.FLT.Seven
