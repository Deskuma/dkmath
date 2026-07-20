/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Five.NormalForm

#print "file: DkMath.FLT.Five.SquareGoldenBridge"

namespace DkMath.FLT.Five

/-- The golden-ratio norm form in the integral basis `1, φ`. -/
def GoldenNorm (m n : ℤ) : ℤ :=
  m ^ 2 + m * n - n ^ 2

/-- GN5 is a quadratic form in the square gap and the endpoint cross-beam. -/
theorem GN5_eq_square_cross_form (g y : ℕ) :
    GN5 g y =
      (g ^ 2) ^ 2 +
        5 * (g ^ 2) * (y * (g + y)) +
        5 * (y * (g + y)) ^ 2 := by
  unfold GN5
  ring

/-- The square-world coordinates are the endpoint square sum and product. -/
theorem square_cross_coordinate_change (g y : ℕ) :
    g ^ 2 + 2 * (y * (g + y)) = (g + y) ^ 2 + y ^ 2 := by
  ring

/-- The GN5 quadratic form is exactly the golden-ratio norm. -/
theorem GN5_eq_goldenNorm_squareLink (g y : ℕ) :
    (GN5 g y : ℤ) =
      GoldenNorm
        (↑((g + y) ^ 2 + y ^ 2) : ℤ)
        (↑((g + y) * y) : ℤ) := by
  unfold GN5 GoldenNorm
  push_cast
  ring

/-- Diagonalizing the golden coordinates gives the discriminant-five form. -/
theorem four_mul_goldenNorm_eq_discriminant_five (m n : ℤ) :
    4 * GoldenNorm m n = (2 * m + n) ^ 2 - 5 * n ^ 2 := by
  unfold GoldenNorm
  ring

/-- The two endpoint-square coordinates retain an independent square boundary. -/
theorem endpoint_square_discriminant (z y : ℤ) :
    (z ^ 2 + y ^ 2) ^ 2 - 4 * (z * y) ^ 2 =
      (z ^ 2 - y ^ 2) ^ 2 := by
  ring

/-- A fifth-power GN5 value becomes a fifth-power golden norm. -/
theorem goldenNorm_eq_fifth_power_of_GN5
    {g y b : ℕ} (hGN : GN5 g y = b ^ 5) :
    GoldenNorm
        (↑((g + y) ^ 2 + y ^ 2) : ℤ)
        (↑((g + y) * y) : ℤ) =
      (b : ℤ) ^ 5 := by
  calc
    GoldenNorm
        (↑((g + y) ^ 2 + y ^ 2) : ℤ)
        (↑((g + y) * y) : ℤ) =
        (GN5 g y : ℤ) := (GN5_eq_goldenNorm_squareLink g y).symm
    _ = ((b ^ 5 : ℕ) : ℤ) := congrArg (fun n : ℕ => (n : ℤ)) hGN
    _ = (b : ℤ) ^ 5 := by norm_num

end DkMath.FLT.Five
