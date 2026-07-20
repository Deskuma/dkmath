/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Five.Reduction

#print "file: DkMath.FLT.Five.NormalForm"

namespace DkMath.FLT.Five

/-- Coprimality passes from the gap to the GN5 residual modulo `y`. -/
theorem coprime_GN5_y_of_coprime
    {g y : ℕ} (hgy : Nat.Coprime g y) :
    Nat.Coprime (GN5 g y) y := by
  refine (Nat.coprime_iff_gcd_eq_one).2 ?_
  by_contra hgcd
  rcases Nat.exists_prime_and_dvd (n := Nat.gcd (GN5 g y) y) hgcd with
    ⟨q, hq, hqgcd⟩
  have hqGN : q ∣ GN5 g y :=
    hqgcd.trans (Nat.gcd_dvd_left (GN5 g y) y)
  have hqy : q ∣ y := hqgcd.trans (Nat.gcd_dvd_right (GN5 g y) y)
  have hdecomp :
      GN5 g y =
        g ^ 4 +
          y * (5 * g ^ 3 + 10 * g ^ 2 * y + 10 * g * y ^ 2 + 5 * y ^ 3) := by
    unfold GN5
    ring
  have hqTail :
      q ∣ y * (5 * g ^ 3 + 10 * g ^ 2 * y + 10 * g * y ^ 2 + 5 * y ^ 3) :=
    dvd_mul_of_dvd_left hqy _
  rw [hdecomp] at hqGN
  have hqg4 : q ∣ g ^ 4 := (Nat.dvd_add_left hqTail).mp hqGN
  have hqg : q ∣ g := hq.dvd_of_dvd_pow hqg4
  exact (Nat.not_coprime_of_dvd_of_dvd hq.one_lt hqg hqy) hgy

/-- Complete elementary normal form of a Branch-B exponent-five candidate. -/
structure BranchBFifthPowerNormalForm
    (x y z a b : ℕ) : Prop where
  pack : CounterexamplePack x y z
  branchB : ¬ 5 ∣ z - y
  gap_eq : z - y = a ^ 5
  GN_eq : GN5 (a ^ 5) y = b ^ 5
  x_eq : x = a * b
  z_eq : z = y + a ^ 5
  a_pos : 0 < a
  b_pos : 0 < b
  coprime_a_y : Nat.Coprime a y
  coprime_a_b : Nat.Coprime a b
  coprime_b_y : Nat.Coprime b y
  five_not_dvd_a : ¬ 5 ∣ a

/-- Every Branch-B counterexample pack supplies the complete fifth-power packet. -/
theorem exists_branchB_fifthPowerNormalForm
    {x y z : ℕ} (hPack : CounterexamplePack x y z)
    (hBranch : ¬ 5 ∣ z - y) :
    ∃ a b : ℕ, BranchBFifthPowerNormalForm x y z a b := by
  rcases branchB_fifth_power_factor_split hPack hBranch with
    ⟨⟨a, hgap⟩, ⟨b, hGN0⟩⟩
  have hGN : GN5 (a ^ 5) y = b ^ 5 := by
    simpa [hgap] using hGN0
  have hyz : y ≤ z := (right_lt_of_fermat5Equation hPack.hx hPack.hEq).le
  have hbody : (z - y) * GN5 (z - y) y = x ^ 5 := by
    rw [← pow_five_sub_pow_five_eq_gap_mul_GN5 hyz]
    exact fifth_sub_eq_of_add_eq hPack.hEq
  have hxpow : (a * b) ^ 5 = x ^ 5 := by
    rw [mul_pow, ← hgap, ← hGN0]
    exact hbody
  have hx : x = a * b :=
    (Nat.pow_left_injective (by decide : 5 ≠ 0) hxpow).symm
  have hz : z = y + a ^ 5 := by omega
  have ha : 0 < a := by
    have hgapPos := gap_pos_of_fermat5Equation hPack.hx hPack.hEq
    rw [hgap] at hgapPos
    by_contra ha0
    have : a = 0 := by omega
    simp [this] at hgapPos
  have hb : 0 < b := by
    by_contra hb0
    have : b = 0 := by omega
    have hxzero : x = 0 := by simpa [this] using hx
    exact (Nat.ne_of_gt hPack.hx) hxzero
  have hgapY := coprime_gap_y_of_counterexamplePack hPack
  rw [hgap] at hgapY
  have hay : Nat.Coprime a y :=
    (Nat.coprime_pow_left_iff (by decide : 0 < 5) a y).mp hgapY
  have hgapGN := branchB_coprime_gap_GN5 hPack hBranch
  rw [hgap, hGN] at hgapGN
  have hab5 : Nat.Coprime a (b ^ 5) :=
    (Nat.coprime_pow_left_iff (by decide : 0 < 5) a (b ^ 5)).mp hgapGN
  have hab : Nat.Coprime a b :=
    (Nat.coprime_pow_right_iff (by decide : 0 < 5) a b).mp hab5
  have hGNy : Nat.Coprime (GN5 (a ^ 5) y) y :=
    coprime_GN5_y_of_coprime (Nat.Coprime.pow_left 5 hay)
  rw [hGN] at hGNy
  have hby : Nat.Coprime b y :=
    (Nat.coprime_pow_left_iff (by decide : 0 < 5) b y).mp hGNy
  have h5a : ¬ 5 ∣ a := by
    intro h5
    apply hBranch
    rw [hgap]
    exact h5.trans (dvd_pow_self a (by decide))
  exact ⟨a, b, hPack, hBranch, hgap, hGN, hx, hz,
    ha, hb, hay, hab, hby, h5a⟩

/-- The narrowed unknown arithmetic kernel after the elementary reduction. -/
abbrev BranchBFifthPowerCore : Prop :=
  ∀ {a b y : ℕ},
    0 < a →
    0 < y →
    Nat.Coprime a y →
    ¬ 5 ∣ a →
    GN5 (a ^ 5) y = b ^ 5 →
    False

/-- A proof of the narrowed fifth-power core refutes every Branch-B pack. -/
theorem branchB_false_of_fifthPowerCore
    (hCore : BranchBFifthPowerCore)
    {x y z : ℕ} (hPack : CounterexamplePack x y z)
    (hBranch : ¬ 5 ∣ z - y) :
    False := by
  rcases exists_branchB_fifthPowerNormalForm hPack hBranch with ⟨a, b, hNF⟩
  exact hCore hNF.a_pos hNF.pack.hy hNF.coprime_a_y
    hNF.five_not_dvd_a hNF.GN_eq

end DkMath.FLT.Five
