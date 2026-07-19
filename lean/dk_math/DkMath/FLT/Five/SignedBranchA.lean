/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Five.BranchA
import DkMath.FLT.Five.BranchB

#print "file: DkMath.FLT.Five.SignedBranchA"

namespace DkMath.FLT.Five

/-- Swapping the two left coordinates preserves a counterexample pack. -/
theorem CounterexamplePack.swap
    {x y z : ℕ} (hPack : CounterexamplePack x y z) :
    CounterexamplePack y x z where
  hx := hPack.hy
  hy := hPack.hx
  hz := hPack.hz
  hxy := hPack.hxy.symm
  hEq := by
    simpa [Fermat5Equation, Nat.add_comm] using hPack.hEq

/-- Away from a five-divisible gap, the GN5 residual is also prime to five. -/
theorem five_not_dvd_GN5_of_five_not_dvd_gap
    {g y : ℕ} (h5g : ¬ 5 ∣ g) :
    ¬ 5 ∣ GN5 g y := by
  intro h5GN
  have hdecomp :
      GN5 g y =
        g ^ 4 +
          5 * (g ^ 3 * y + 2 * g ^ 2 * y ^ 2 + 2 * g * y ^ 3 + y ^ 4) := by
    unfold GN5
    ring
  have h5tail :
      5 ∣ 5 * (g ^ 3 * y + 2 * g ^ 2 * y ^ 2 + 2 * g * y ^ 3 + y ^ 4) :=
    dvd_mul_of_dvd_left (dvd_refl 5) _
  rw [hdecomp] at h5GN
  have h5g4 : 5 ∣ g ^ 4 := (Nat.dvd_add_left h5tail).mp h5GN
  exact h5g ((by decide : Nat.Prime 5).dvd_of_dvd_pow h5g4)

/-- A Branch-B candidate cannot have its first coordinate divisible by five. -/
theorem five_not_dvd_x_of_branchB
    {x y z : ℕ} (hPack : CounterexamplePack x y z)
    (hBranch : ¬ 5 ∣ z - y) :
    ¬ 5 ∣ x := by
  intro h5x
  have hyz : y ≤ z := (right_lt_of_fermat5Equation hPack.hx hPack.hEq).le
  have hbody : Body5 (z - y) y = x ^ 5 :=
    body5_eq_fifth_power_of_fermat hyz hPack.hEq
  have h5x5 : 5 ∣ x ^ 5 := h5x.trans (dvd_pow_self x (by decide))
  have h5body : 5 ∣ Body5 (z - y) y := by
    rw [hbody]
    exact h5x5
  unfold Body5 at h5body
  rcases (by decide : Nat.Prime 5).dvd_mul.mp h5body with h5gap | h5GN
  · exact hBranch h5gap
  · exact (five_not_dvd_GN5_of_five_not_dvd_gap hBranch) h5GN

/-- Fifth powers reduce to their bases modulo five. -/
theorem pow_five_mod_five (n : ℕ) :
    n ^ 5 % 5 = n % 5 := by
  rw [Nat.pow_mod]
  have hn : n % 5 < 5 := Nat.mod_lt _ (by decide)
  interval_cases h : n % 5 <;> norm_num [h]

/-- The finite mod-25 residue obstruction used by the signed routing theorem. -/
private theorem mod25_fifth_residue_classification :
    ∀ x y z : Fin 25,
      (x.1 ^ 5 + y.1 ^ 5) % 25 = z.1 ^ 5 % 25 →
      ¬ 5 ∣ x.1 →
      5 ∣ y.1 ∨ 5 ∣ z.1 := by
  native_decide

/-- A fifth-power equation with `5 ∤ x` forces five into `y` or `z`. -/
theorem five_dvd_y_or_z_of_fermat5_of_five_not_dvd_x
    {x y z : ℕ} (hEq : Fermat5Equation x y z)
    (h5x : ¬ 5 ∣ x) :
    5 ∣ y ∨ 5 ∣ z := by
  let xr : Fin 25 := ⟨x % 25, Nat.mod_lt _ (by decide)⟩
  let yr : Fin 25 := ⟨y % 25, Nat.mod_lt _ (by decide)⟩
  let zr : Fin 25 := ⟨z % 25, Nat.mod_lt _ (by decide)⟩
  have hEqNat : x ^ 5 + y ^ 5 = z ^ 5 := by
    simpa [Fermat5Equation] using hEq
  have hEqMod :
      ((x % 25) ^ 5 + (y % 25) ^ 5) % 25 = (z % 25) ^ 5 % 25 := by
    have h := congrArg (fun n : ℕ => n % 25) hEqNat
    simpa [Nat.add_mod, Nat.pow_mod] using h
  have h5xr : ¬ 5 ∣ x % 25 := by
    intro h
    exact h5x ((Nat.dvd_mod_iff (by norm_num : 5 ∣ 25)).mp h)
  have hres := mod25_fifth_residue_classification xr yr zr
  have hfinite : 5 ∣ y % 25 ∨ 5 ∣ z % 25 := by
    simpa [xr, yr, zr] using hres hEqMod h5xr
  rcases hfinite with h5yr | h5zr
  · exact Or.inl ((Nat.dvd_mod_iff (by norm_num : 5 ∣ 25)).mp h5yr)
  · exact Or.inr ((Nat.dvd_mod_iff (by norm_num : 5 ∣ 25)).mp h5zr)

/-- If five enters the second coordinate, swapping exposes a difference gap. -/
theorem five_dvd_z_sub_x_of_fermat5_of_five_dvd_y
    {x y z : ℕ} (hEq : Fermat5Equation x y z)
    (h5y : 5 ∣ y) :
    5 ∣ z - x := by
  have hEqNat : x ^ 5 + y ^ 5 = z ^ 5 := by
    simpa [Fermat5Equation] using hEq
  have hmod := congrArg (fun n : ℕ => n % 5) hEqNat
  have hy0 : y % 5 = 0 := Nat.mod_eq_zero_of_dvd h5y
  have hxz : x % 5 = z % 5 := by
    simpa [Nat.add_mod, pow_five_mod_five, hy0] using hmod
  exact Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq hxz.symm)

/-- If five enters the result coordinate, the left pair has a five-divisible sum. -/
theorem five_dvd_x_add_y_of_fermat5_of_five_dvd_z
    {x y z : ℕ} (hEq : Fermat5Equation x y z)
    (h5z : 5 ∣ z) :
    5 ∣ x + y := by
  have hEqNat : x ^ 5 + y ^ 5 = z ^ 5 := by
    simpa [Fermat5Equation] using hEq
  have hmod := congrArg (fun n : ℕ => n % 5) hEqNat
  have hz0 : z % 5 = 0 := Nat.mod_eq_zero_of_dvd h5z
  apply Nat.dvd_of_mod_eq_zero
  simpa [Nat.add_mod, pow_five_mod_five, hz0] using hmod

/-- The two exceptional five-adic orientations of an exponent-five equation. -/
inductive SignedBranchAOrientation (u v w : ℕ) : Prop
  | differenceGap
      (five_dvd_left : 5 ∣ u)
      (five_dvd_gap : 5 ∣ w - v) :
      SignedBranchAOrientation u v w
  | sumGap
      (five_dvd_result : 5 ∣ w)
      (five_dvd_sum : 5 ∣ u + v) :
      SignedBranchAOrientation u v w

/-- A primitive exponent-five candidate equipped with its signed five-adic orientation. -/
structure SignedBranchANormalForm (u v w : ℕ) : Prop where
  pack : CounterexamplePack u v w
  orientation : SignedBranchAOrientation u v w

/-- Every Branch-B pack is routed into one of the two signed Branch-A orientations. -/
theorem signedBranchA_normalForm_of_branchB
    {x y z : ℕ} (hPack : CounterexamplePack x y z)
    (hBranch : ¬ 5 ∣ z - y) :
    SignedBranchANormalForm y x z ∨ SignedBranchANormalForm x y z := by
  have h5x : ¬ 5 ∣ x := five_not_dvd_x_of_branchB hPack hBranch
  rcases five_dvd_y_or_z_of_fermat5_of_five_not_dvd_x hPack.hEq h5x with
    h5y | h5z
  · left
    refine ⟨hPack.swap, ?_⟩
    exact SignedBranchAOrientation.differenceGap h5y
      (five_dvd_z_sub_x_of_fermat5_of_five_dvd_y hPack.hEq h5y)
  · right
    refine ⟨hPack, ?_⟩
    exact SignedBranchAOrientation.sumGap h5z
      (five_dvd_x_add_y_of_fermat5_of_five_dvd_z hPack.hEq h5z)

/-- Contract for the common five-adic descent after signed routing. -/
abbrev SignedBranchARefuter : Prop :=
  ∀ {u v w : ℕ}, SignedBranchANormalForm u v w → False

/-- A refuter for both signed orientations closes every Branch-B candidate. -/
theorem branchB_false_of_signedBranchARefuter
    (hRefuter : SignedBranchARefuter)
    {x y z : ℕ} (hPack : CounterexamplePack x y z)
    (hBranch : ¬ 5 ∣ z - y) :
    False := by
  rcases signedBranchA_normalForm_of_branchB hPack hBranch with hDiff | hSum
  · exact hRefuter hDiff
  · exact hRefuter hSum

end DkMath.FLT.Five
