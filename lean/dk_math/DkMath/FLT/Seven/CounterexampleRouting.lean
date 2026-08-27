/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.PrimitiveCyclotomicDepth
import DkMath.FLT.Seven.Basic

#print "file: DkMath.FLT.Seven.CounterexampleRouting"

namespace DkMath.FLT.Seven

open DkMath.CosmicFormulaBinom

theorem coprime_y_z_of_counterexamplePack
    {x y z : ℕ} (hPack : CounterexamplePack x y z) : Nat.Coprime y z := by
  refine (Nat.coprime_iff_gcd_eq_one).2 ?_
  by_contra hg
  rcases Nat.exists_prime_and_dvd (n := Nat.gcd y z) hg with ⟨q, hq, hqgcd⟩
  have hqy : q ∣ y := hqgcd.trans (Nat.gcd_dvd_left y z)
  have hqz : q ∣ z := hqgcd.trans (Nat.gcd_dvd_right y z)
  have hqyp : q ∣ y ^ 7 := hqy.trans (dvd_pow_self y (by decide))
  have hqzp : q ∣ z ^ 7 := hqz.trans (dvd_pow_self z (by decide))
  have hqxp : q ∣ x ^ 7 := by
    have hqsum : q ∣ x ^ 7 + y ^ 7 := by rw [hPack.hEq]; exact hqzp
    exact (Nat.dvd_add_left hqyp).mp hqsum
  have hqx : q ∣ x := hq.dvd_of_dvd_pow hqxp
  exact (Nat.not_coprime_of_dvd_of_dvd hq.one_lt hqx hqy) hPack.hxy

theorem coprime_gap_y_of_counterexamplePack
    {x y z : ℕ} (hPack : CounterexamplePack x y z) :
    Nat.Coprime (z - y) y := by
  have hyz := (right_lt_of_fermat7Equation hPack.hx hPack.hEq).le
  have h := (Nat.coprime_sub_self_right hyz).2
    (coprime_y_z_of_counterexamplePack hPack)
  simpa [Nat.coprime_comm] using h

/-- The natural gap-times-GN body at exponent seven. -/
def Body7 (g y : ℕ) : ℕ := g * GN 7 g y

theorem body7_eq_seventh_power_of_counterexample
    {x y z : ℕ} (hPack : CounterexamplePack x y z) :
    Body7 (z - y) y = x ^ 7 := by
  have hyz := (right_lt_of_fermat7Equation hPack.hx hPack.hEq).le
  unfold Body7
  have hfactor : z ^ 7 = (z - y) * GN 7 (z - y) y + y ^ 7 := by
    simpa [Nat.sub_add_cancel hyz] using
      (cosmic_id_csr' (R := ℕ) 7 (z - y) y)
  have heq := hPack.hEq
  unfold Fermat7Equation at heq
  omega

theorem GN_seven_pos_of_counterexample
    {x y z : ℕ} (hPack : CounterexamplePack x y z) :
    0 < GN 7 (z - y) y := by
  have hg := gap_pos_of_fermat7Equation hPack.hx hPack.hEq
  have hbody := body7_eq_seventh_power_of_counterexample hPack
  unfold Body7 at hbody
  have hxpow : 0 < x ^ 7 := pow_pos hPack.hx 7
  nlinarith

theorem body7_ne_zero_of_counterexample
    {x y z : ℕ} (hPack : CounterexamplePack x y z) :
    Body7 (z - y) y ≠ 0 := by
  rw [body7_eq_seventh_power_of_counterexample hPack]
  exact pow_ne_zero 7 (Nat.ne_of_gt hPack.hx)

theorem GN_seven_eq_gap_mul_add_seven_mul_y_pow_six (g y : ℕ) :
    GN 7 g y =
      g * (g ^ 5 + 7 * g ^ 4 * y + 21 * g ^ 3 * y ^ 2
        + 35 * g ^ 2 * y ^ 3 + 35 * g * y ^ 4 + 21 * y ^ 5)
        + 7 * y ^ 6 := by
  rw [GN_eq_sum]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

theorem gcd_gap_GN_seven_dvd_seven {g y : ℕ} (hcop : Nat.Coprime g y) :
    Nat.gcd g (GN 7 g y) ∣ 7 := by
  let d := Nat.gcd g (GN 7 g y)
  have hdg : d ∣ g := Nat.gcd_dvd_left _ _
  have hdGN : d ∣ GN 7 g y := Nat.gcd_dvd_right _ _
  have hprefix : d ∣ g * (g ^ 5 + 7 * g ^ 4 * y + 21 * g ^ 3 * y ^ 2
      + 35 * g ^ 2 * y ^ 3 + 35 * g * y ^ 4 + 21 * y ^ 5) :=
    dvd_mul_of_dvd_left hdg _
  have hdy6 : d ∣ 7 * y ^ 6 := by
    rw [GN_seven_eq_gap_mul_add_seven_mul_y_pow_six] at hdGN
    exact (Nat.dvd_add_right hprefix).mp hdGN
  have hdy : Nat.Coprime d y := hcop.of_dvd_left hdg
  exact (hdy.pow_right 6).dvd_of_dvd_mul_right hdy6

theorem gcd_gap_GN_seven_eq_one_of_not_seven_dvd
    {g y : ℕ} (hcop : Nat.Coprime g y) (h7g : ¬ 7 ∣ g) :
    Nat.gcd g (GN 7 g y) = 1 := by
  have hd := gcd_gap_GN_seven_dvd_seven hcop
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 7)).mp hd with h | h
  · exact h
  · exfalso
    apply h7g
    rw [← h]
    exact Nat.gcd_dvd_left _ _

theorem gcd_gap_GN_seven_eq_seven_of_seven_dvd
    {g y : ℕ} (hcop : Nat.Coprime g y) (h7g : 7 ∣ g) :
    Nat.gcd g (GN 7 g y) = 7 := by
  apply Nat.dvd_antisymm (gcd_gap_GN_seven_dvd_seven hcop)
  apply Nat.dvd_gcd h7g
  have hGN : 7 ∣ GN 7 ((g + y) - y) y :=
    (seven_dvd_GN_seven_sub_iff (g + y) y (by omega)).2 (by simpa using h7g)
  simpa using hGN

theorem branchAway_coprime_gap_GN_seven
    {x y z : ℕ} (hPack : CounterexamplePack x y z)
    (hBranch : ¬ 7 ∣ z - y) :
    Nat.Coprime (z - y) (GN 7 (z - y) y) := by
  rw [Nat.coprime_iff_gcd_eq_one]
  exact gcd_gap_GN_seven_eq_one_of_not_seven_dvd
    (coprime_gap_y_of_counterexamplePack hPack) hBranch

theorem branchRamified_gcd_gap_GN_seven
    {x y z : ℕ} (hPack : CounterexamplePack x y z)
    (hBranch : 7 ∣ z - y) :
    Nat.gcd (z - y) (GN 7 (z - y) y) = 7 :=
  gcd_gap_GN_seven_eq_seven_of_seven_dvd
    (coprime_gap_y_of_counterexamplePack hPack) hBranch

theorem seventh_power_factor_split {a b x : ℕ}
    (hcop : Nat.Coprime a b) (hbody : a * b = x ^ 7) :
    (∃ u : ℕ, a = u ^ 7) ∧ (∃ v : ℕ, b = v ^ 7) := by
  have hunit : IsUnit (GCDMonoid.gcd a b) := by
    simpa [gcd_eq_nat_gcd, Nat.Coprime, Nat.isUnit_iff] using hcop
  constructor
  · exact exists_eq_pow_of_mul_eq_pow hunit hbody
  · have hunit' : IsUnit (GCDMonoid.gcd b a) := by simpa [gcd_comm] using hunit
    exact exists_eq_pow_of_mul_eq_pow hunit' (by simpa [mul_comm] using hbody)

theorem branchAway_seventh_power_factor_split
    {x y z : ℕ} (hPack : CounterexamplePack x y z)
    (hBranch : ¬ 7 ∣ z - y) :
    (∃ u : ℕ, z - y = u ^ 7) ∧
      (∃ v : ℕ, GN 7 (z - y) y = v ^ 7) :=
  seventh_power_factor_split (branchAway_coprime_gap_GN_seven hPack hBranch)
    (body7_eq_seventh_power_of_counterexample hPack)

theorem not_seven_dvd_y_of_counterexample_of_seven_dvd_gap
    {x y z : ℕ} (hPack : CounterexamplePack x y z)
    (hBranch : 7 ∣ z - y) : ¬ 7 ∣ y := by
  intro hy
  exact (Nat.not_coprime_of_dvd_of_dvd (by norm_num : 1 < 7) hBranch hy)
    (coprime_gap_y_of_counterexamplePack hPack)

theorem seven_dvd_x_of_counterexample_of_seven_dvd_gap
    {x y z : ℕ} (hPack : CounterexamplePack x y z)
    (hBranch : 7 ∣ z - y) : 7 ∣ x := by
  apply (by norm_num : Nat.Prime 7).dvd_of_dvd_pow
  rw [← body7_eq_seventh_power_of_counterexample hPack]
  exact dvd_mul_of_dvd_left hBranch _

theorem padicValNat_GN_seven_eq_one_of_counterexample
    {x y z : ℕ} (hPack : CounterexamplePack x y z)
    (hBranch : 7 ∣ z - y) :
    padicValNat 7 (GN 7 (z - y) y) = 1 := by
  exact (padicValNat_GN_seven_sub_eq_one_iff
    (right_lt_of_fermat7Equation hPack.hx hPack.hEq).le
    (coprime_y_z_of_counterexamplePack hPack).symm).2 hBranch

theorem padicValNat_carrier_shape_of_mul_eq_seventh
    {carrier residual distinguished : ℕ}
    (hc0 : carrier ≠ 0) (hr0 : residual ≠ 0) (_hd0 : distinguished ≠ 0)
    (hEq : carrier * residual = distinguished ^ 7)
    (hrVal : padicValNat 7 residual = 1) :
    ∃ m : ℕ, padicValNat 7 carrier = 6 + 7 * m := by
  letI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hpow : padicValNat 7 (distinguished ^ 7) =
      7 * padicValNat 7 distinguished := by
    exact padicValNat.pow (p := 7) (a := distinguished) 7
  have hmul : padicValNat 7 (carrier * residual) =
      padicValNat 7 carrier + padicValNat 7 residual := by
    simpa using (padicValNat.mul (p := 7) hc0 hr0)
  have hvalEq : 7 * padicValNat 7 distinguished =
      padicValNat 7 carrier + 1 := by
    calc
      _ = padicValNat 7 (distinguished ^ 7) := hpow.symm
      _ = padicValNat 7 (carrier * residual) := by rw [hEq]
      _ = _ := hmul
      _ = _ := by rw [hrVal]
  have hdPos : 0 < padicValNat 7 distinguished := by
    have : 0 < 7 * padicValNat 7 distinguished := by rw [hvalEq]; omega
    exact Nat.pos_of_mul_pos_left this
  have hcVal : padicValNat 7 carrier =
      7 * padicValNat 7 distinguished - 1 := Nat.eq_sub_of_add_eq hvalEq.symm
  refine ⟨padicValNat 7 distinguished - 1, ?_⟩
  have hs := Nat.sub_add_cancel (Nat.succ_le_of_lt hdPos)
  rw [hcVal, ← hs]
  omega

theorem padicValNat_gap_shape_of_counterexample
    {x y z : ℕ} (hPack : CounterexamplePack x y z)
    (hBranch : 7 ∣ z - y) :
    ∃ m : ℕ, padicValNat 7 (z - y) = 6 + 7 * m := by
  apply padicValNat_carrier_shape_of_mul_eq_seventh
  · exact (gap_pos_of_fermat7Equation hPack.hx hPack.hEq).ne'
  · exact (GN_seven_pos_of_counterexample hPack).ne'
  · exact hPack.hx.ne'
  · exact body7_eq_seventh_power_of_counterexample hPack
  · exact padicValNat_GN_seven_eq_one_of_counterexample hPack hBranch

theorem seven_pow_six_dvd_gap_of_counterexample
    {x y z : ℕ} (hPack : CounterexamplePack x y z)
    (hBranch : 7 ∣ z - y) : 7 ^ 6 ∣ z - y := by
  have hshape := padicValNat_gap_shape_of_counterexample hPack hBranch
  apply (@padicValNat_dvd_iff_le 7 (Fact.mk (by norm_num)) (z - y) 6
    (gap_pos_of_fermat7Equation hPack.hx hPack.hEq).ne').2
  rcases hshape with ⟨m, hm⟩
  rw [hm]
  omega

structure SevenAdicCounterexamplePacket (x y z : ℕ) : Prop where
  counterexample : CounterexamplePack x y z
  seven_dvd_gap : 7 ∣ z - y
  factor_eq : (z - y) * GN 7 (z - y) y = x ^ 7
  gcd_eq_seven : Nat.gcd (z - y) (GN 7 (z - y) y) = 7
  seven_not_dvd_y : ¬ 7 ∣ y
  seven_dvd_x : 7 ∣ x
  residual_padicValNat : padicValNat 7 (GN 7 (z - y) y) = 1
  gap_padicValNat_shape : ∃ m : ℕ, padicValNat 7 (z - y) = 6 + 7 * m
  seven_pow_six_dvd_gap : 7 ^ 6 ∣ z - y

theorem sevenAdicCounterexamplePacket_of_branch
    {x y z : ℕ} (hPack : CounterexamplePack x y z)
    (hBranch : 7 ∣ z - y) : SevenAdicCounterexamplePacket x y z where
  counterexample := hPack
  seven_dvd_gap := hBranch
  factor_eq := body7_eq_seventh_power_of_counterexample hPack
  gcd_eq_seven := branchRamified_gcd_gap_GN_seven hPack hBranch
  seven_not_dvd_y := not_seven_dvd_y_of_counterexample_of_seven_dvd_gap hPack hBranch
  seven_dvd_x := seven_dvd_x_of_counterexample_of_seven_dvd_gap hPack hBranch
  residual_padicValNat := padicValNat_GN_seven_eq_one_of_counterexample hPack hBranch
  gap_padicValNat_shape := padicValNat_gap_shape_of_counterexample hPack hBranch
  seven_pow_six_dvd_gap := seven_pow_six_dvd_gap_of_counterexample hPack hBranch

inductive CounterexampleRoute (x y z : ℕ) : Prop
  | away (hnot : ¬ 7 ∣ z - y)
      (gapPow : ∃ u : ℕ, z - y = u ^ 7)
      (gnPow : ∃ v : ℕ, GN 7 (z - y) y = v ^ 7)
  | ramified (packet : SevenAdicCounterexamplePacket x y z)

theorem counterexampleRoute_of_pack
    {x y z : ℕ} (hPack : CounterexamplePack x y z) :
    CounterexampleRoute x y z := by
  by_cases hBranch : 7 ∣ z - y
  · exact .ramified (sevenAdicCounterexamplePacket_of_branch hPack hBranch)
  · rcases branchAway_seventh_power_factor_split hPack hBranch with ⟨hg, hGN⟩
    exact .away hBranch hg hGN

end DkMath.FLT.Seven
