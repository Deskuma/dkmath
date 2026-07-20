/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Five.SquareGoldenBridge

#print "file: DkMath.FLT.Five.SquareGoldenNormalForm"

namespace DkMath.FLT.Five

/-- The endpoint-square mass coordinate. -/
def SquareGoldenM (z y : ℕ) : ℤ :=
  (z : ℤ) ^ 2 + (y : ℤ) ^ 2

/-- The endpoint cross-beam coordinate. -/
def SquareGoldenN (z y : ℕ) : ℤ :=
  (z : ℤ) * (y : ℤ)

/-- The square-world boundary retained by the golden coordinates. -/
theorem squareGolden_tenth_boundary_base (z y : ℕ) :
    SquareGoldenM z y - 2 * SquareGoldenN z y =
      ((z : ℤ) - (y : ℤ)) ^ 2 := by
  unfold SquareGoldenM SquareGoldenN
  ring

/-- The endpoint coordinates retain an independent square discriminant. -/
theorem squareGolden_square_discriminant (z y : ℕ) :
    (SquareGoldenM z y) ^ 2 - 4 * (SquareGoldenN z y) ^ 2 =
      ((z : ℤ) ^ 2 - (y : ℤ) ^ 2) ^ 2 := by
  unfold SquareGoldenM SquareGoldenN
  exact endpoint_square_discriminant (z : ℤ) (y : ℤ)

/--
The full Branch-B packet after projection through the square-world link into
integral golden-ratio coordinates.
-/
structure BranchBSquareGoldenNormalForm
    (x y z a b : ℕ) : Prop where
  normal : BranchBFifthPowerNormalForm x y z a b
  golden_eq :
    GoldenNorm (SquareGoldenM z y) (SquareGoldenN z y) = (b : ℤ) ^ 5
  tenth_boundary :
    SquareGoldenM z y - 2 * SquareGoldenN z y = (a : ℤ) ^ 10
  square_discriminant :
    (SquareGoldenM z y) ^ 2 - 4 * (SquareGoldenN z y) ^ 2 =
      ((z : ℤ) ^ 2 - (y : ℤ) ^ 2) ^ 2
  discriminant_five_eq :
    (2 * SquareGoldenM z y + SquareGoldenN z y) ^ 2 -
        5 * (SquareGoldenN z y) ^ 2 =
      4 * (b : ℤ) ^ 5

/-- Every Branch-B candidate supplies the simultaneous golden/square packet. -/
theorem exists_branchB_squareGoldenNormalForm
    {x y z : ℕ} (hPack : CounterexamplePack x y z)
    (hBranch : ¬ 5 ∣ z - y) :
    ∃ a b : ℕ, BranchBSquareGoldenNormalForm x y z a b := by
  rcases exists_branchB_fifthPowerNormalForm hPack hBranch with ⟨a, b, hNF⟩
  have hzy : a ^ 5 + y = z := by
    simpa [Nat.add_comm] using hNF.z_eq.symm
  have hGolden :
      GoldenNorm (SquareGoldenM z y) (SquareGoldenN z y) = (b : ℤ) ^ 5 := by
    have h := goldenNorm_eq_fifth_power_of_GN5 hNF.GN_eq
    simpa [SquareGoldenM, SquareGoldenN, hzy] using h
  have hzInt : (z : ℤ) = (y : ℤ) + (a : ℤ) ^ 5 := by
    exact_mod_cast hNF.z_eq
  have hTenth :
      SquareGoldenM z y - 2 * SquareGoldenN z y = (a : ℤ) ^ 10 := by
    calc
      SquareGoldenM z y - 2 * SquareGoldenN z y =
          ((z : ℤ) - (y : ℤ)) ^ 2 := squareGolden_tenth_boundary_base z y
      _ = (a : ℤ) ^ 10 := by
        rw [hzInt]
        ring
  have hSquare := squareGolden_square_discriminant z y
  have hDiscFive :
      (2 * SquareGoldenM z y + SquareGoldenN z y) ^ 2 -
          5 * (SquareGoldenN z y) ^ 2 =
        4 * (b : ℤ) ^ 5 := by
    calc
      (2 * SquareGoldenM z y + SquareGoldenN z y) ^ 2 -
            5 * (SquareGoldenN z y) ^ 2 =
          4 * GoldenNorm (SquareGoldenM z y) (SquareGoldenN z y) :=
        (four_mul_goldenNorm_eq_discriminant_five
          (SquareGoldenM z y) (SquareGoldenN z y)).symm
      _ = 4 * (b : ℤ) ^ 5 := by rw [hGolden]
  exact ⟨a, b, hNF, hGolden, hTenth, hSquare, hDiscFive⟩

/-- The narrowed receiver after both fifth-power and square-golden reduction. -/
abbrev BranchBSquareGoldenCore : Prop :=
  ∀ {x y z a b : ℕ}, BranchBSquareGoldenNormalForm x y z a b → False

/-- A contradiction for every square-golden packet closes Branch B. -/
theorem branchB_false_of_squareGoldenCore
    (hCore : BranchBSquareGoldenCore)
    {x y z : ℕ} (hPack : CounterexamplePack x y z)
    (hBranch : ¬ 5 ∣ z - y) :
    False := by
  rcases exists_branchB_squareGoldenNormalForm hPack hBranch with ⟨a, b, hNF⟩
  exact hCore hNF

end DkMath.FLT.Five
